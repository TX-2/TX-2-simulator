use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

use assembler::*;

fn get_test_input_file_name(relative_to_manifest: &str) -> PathBuf {
    let mut location = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    location.push(relative_to_manifest);
    if location.exists() {
        location
    } else {
        panic!(
            "Cannot find input {relative_to_manifest}: {} does not exist",
            location.display()
        );
    }
}

fn get_temp_file_name(prefix: &str, extension: &str) -> tempfile::TempPath {
    assert!(extension.starts_with("."));
    tempfile::Builder::new()
        .prefix(prefix)
        .suffix(extension)
        .tempfile()
        .expect("should be able to create a temporary file")
        .into_temp_path()
}

fn files_are_identical(expected: &OsStr, got: &OsStr) -> Result<(), String> {
    fn must_open(name: &OsStr) -> File {
        File::open(name).unwrap_or_else(|_| panic!("should be able to open test file {name:?}"))
    }

    let expected_file = must_open(expected);
    let got_file = must_open(got);
    const COMPLAIN: &str = "should be able to obtain file size";
    let expected_file_len = expected_file.metadata().expect(COMPLAIN).len();
    let got_file_len = got_file.metadata().expect(COMPLAIN).len();
    if expected_file_len != got_file_len {
        return Err(format!(
            "wrong file length: {expected:?} is {expected_file_len} bytes but {got:?} is {got_file_len} bytes",
        ));
    }

    const READ_ERR: &str = "unexpected read error";
    let expected_file_reader = BufReader::new(expected_file);
    let got_file_reader = BufReader::new(got_file);
    for (offset, (expected_byte, got_byte)) in expected_file_reader
        .bytes()
        .zip(got_file_reader.bytes())
        .map(|(exp, got)| (exp.expect(READ_ERR), got.expect(READ_ERR)))
        .enumerate()
    {
        if expected_byte != got_byte {
            return Err(format!(
                "difference at position {offset}: expected byte {expected_byte} but got {got_byte}"
            ));
        }
    }
    Ok(())
}

fn fill_output_file_with_garbage(name: &Path) {
    let f = match OpenOptions::new().write(true).open(name) {
        Ok(f) => f,
        Err(e) => {
            panic!(
                "should be able to open temporary file {} for writing: {e}",
                name.display()
            );
        }
    };
    let mut w = BufWriter::new(f);
    let data = [0u8; 1024];
    for _ in 0..1000 {
        if let Err(e) = w.write(&data) {
            panic!(
                "failed to write data to temporary file {}: {e}",
                name.display()
            );
        }
    }
    if let Err(e) = w.flush() {
        panic!(
            "failed to flush output data to temporary file {}: {e}",
            name.display()
        );
    }
}

fn check_golden_match(golden: &OsStr, actual_output: &OsStr) -> Result<(), String> {
    match files_are_identical(golden, actual_output) {
        Ok(()) => Ok(()),
        Err(e) => Err(format!(
            "{} and {} are not identical: {}",
            golden.display(),
            actual_output.display(),
            e
        )),
    }
}

fn disassemble_ensuring_no_diagnostics(tape_file: &OsStr) -> Result<String, String> {
    let mut output: Vec<u8> = Vec::new();
    let mut errors: Vec<u8> = Vec::new();
    match disassemble_file(tape_file, false, &mut output, &mut errors) {
        Err(e) => Err(format!("disassembly failed: {e}")),
        Ok(()) if errors.is_empty() => match str::from_utf8(&output) {
            Err(e) => Err(format!(
                "disassembler produced output which was not valid utf8: {e}"
            )),
            Ok(output_str) => Ok(output_str.to_string()),
        },
        Ok(()) => match str::from_utf8(&errors) {
            Ok(messages) => Err(format!(
                "disassembly produced error or warning messages: {messages}"
            )),
            Err(e) => {
                let n = errors.len();
                Err(format!(
                    "disassembly produced {n} bytes of error or warning messages, but they were not valid utf8 ({e})"
                ))
            }
        },
    }
}

fn verify_successful_disassembly(tape_file: &OsStr) -> Result<(), String> {
    disassemble_ensuring_no_diagnostics(tape_file).map(|_| ())
}

fn assembler_golden_output_test(
    input_relative_path: &str,
    golden_output_relative_path: &str,
) -> Result<(), String> {
    let input = get_test_input_file_name(input_relative_path);
    let golden = get_test_input_file_name(golden_output_relative_path);
    let actual_output = get_temp_file_name("golden", ".tape");
    fill_output_file_with_garbage(&actual_output);
    match assemble_file(input.as_os_str(), &actual_output, Default::default()) {
        Ok(()) => {
            check_golden_match(golden.as_os_str(), actual_output.as_os_str())?;
            verify_successful_disassembly(actual_output.as_os_str())
        }
        Err(e) => Err(format!("failed to assemble {input_relative_path}: {e}")),
    }
}

#[test]
fn golden_output_assembling_hello_program() {
    assembler_golden_output_test("examples/hello.tx2as", "../examples/hello.tape")
        .expect("actual and golden outputs should have been identical for 'hello'");
}

#[test]
fn golden_output_assembling_echo_program() {
    assembler_golden_output_test("examples/echo.tx2as", "../examples/echo.tape")
        .expect("actual and golden outputs should have been identical for 'echo'");
}

/// Verify that we can dissassemble a tape file, and then assemble the
/// disassembly to generate a second tape file which is identical to
/// the first tape file.
fn round_trip_tape_file_test(input_tape_relative_path: &str) -> Result<(), String> {
    let input_tape = get_test_input_file_name(input_tape_relative_path);

    let disassembly: String = disassemble_ensuring_no_diagnostics(input_tape.as_os_str())?;
    let temp_input_file_name = get_temp_file_name("disassembled", ".tx2as");
    let actual_output = get_temp_file_name("round_tripped", ".tape");

    if let Err(e) = std::fs::write(&temp_input_file_name, disassembly) {
        return Err(e.to_string());
    }

    let mut listing = String::new();
    let output_options = OutputOptions {
        list: ListingDestination::Capture(&mut listing),
    };
    let asm_result = assemble_file(
        temp_input_file_name.as_os_str(),
        &actual_output,
        output_options,
    );
    eprintln!("Assembly listing:\n{listing}");
    match asm_result {
        Ok(()) => {
            // The contents of `input_tape` and `actual_output` should be identical.
            files_are_identical(input_tape.as_os_str(), actual_output.as_os_str())
        }
        Err(e) => Err(format!(
            "failed to assemble {} (which is the output of the disassembler): {e}",
            temp_input_file_name.display()
        )),
    }
}

#[test]
fn round_trip_hello_tape() {
    round_trip_tape_file_test("../examples/hello.tape").expect(
        "should be able to assemble the disassembly of 'hello.tape' and get an identical tape file",
    );
}

#[test]
fn round_trip_echo_tape() {
    round_trip_tape_file_test("../examples/echo.tape").expect(
        "should be able to assemble the disassembly of 'echo.tape' and get an identical tape file",
    );
}

fn error_message<E: std::error::Error>(e: E) -> String {
    e.to_string()
}

/// Verify that we can take some source, write it to source file A1.tx2as,
/// assemble that to A1.tape, disassemble the tape to A2.tx2as, assemble to
/// create A2.tape, and then find that A1.tape and A2.tape are identical.
fn round_trip_source_test(basename: &str, input_body: &str) -> Result<(), String> {
    let a1_basename = format!("{basename}_1");
    let a1_source = get_temp_file_name(&a1_basename, ".tx2as");
    let a1_tape = get_temp_file_name(&a1_basename, ".tape");

    let a2_basename = format!("{basename}_2");
    let a2_source = get_temp_file_name(&a2_basename, ".tx2as");
    let a2_tape = get_temp_file_name(&a2_basename, ".tape");

    let mut listing1 = String::new();
    let output_options1 = OutputOptions {
        list: ListingDestination::Capture(&mut listing1),
    };

    // Assemble the initial source, generating a1_tape.
    eprintln!("first assembly body:\n{input_body}");
    fs::write(&a1_source, input_body).map_err(error_message)?;
    if let Err(e) = assemble_file(a1_source.as_os_str(), &a1_tape, output_options1) {
        return Err(format!(
            "failed to assemble {} (which contains the source for test {basename}: {e}",
            a1_source.display()
        ));
    }

    eprintln!(
        "Listing from assembly of {} (used to produce {}):\n{listing1}",
        a1_source.display(),
        a1_tape.display(),
    );

    // Disassemble a1_tape, generating a2_source.
    match disassemble_ensuring_no_diagnostics(a1_tape.as_os_str()) {
        Ok(a2_source_body) => {
            eprintln!(
                "Disassembly of {} (which we will store in {}):\n{}",
                a1_tape.display(),
                a2_source.display(),
                a2_source_body
            );
            fs::write(&a2_source, a2_source_body).map_err(error_message)?;
        }
        Err(e) => {
            return Err(format!(
                "failed to disassemble a1_tape file {}: {e}",
                a1_tape.display()
            ));
        }
    }

    let mut listing2 = String::new();
    let output_options2 = OutputOptions {
        list: ListingDestination::Capture(&mut listing2),
    };

    // Assemble a2_source, generating a2_tape.
    if let Err(e) = assemble_file(a2_source.as_os_str(), &a2_tape, output_options2) {
        return Err(format!(
            "failed to assemble {} (which contains the disassembly for test {basename}: {e}",
            a2_source.display()
        ));
    }

    eprintln!(
        "Listing from assembly of {} (used to produce {}):\n{listing2}",
        a2_source.display(),
        a2_tape.display(),
    );

    // a1_tape and a2_tape should be identical.
    if let Err(e) = files_are_identical(a1_tape.as_os_str(), a2_tape.as_os_str()) {
        return Err(format!(
            "first ({}) and second ({}) tape files are not identical: {e}",
            a1_tape.display(),
            a2_tape.display(),
        ));
    }
    Ok(())
}

#[test]
fn test_round_trip_seq() -> Result<(), String> {
    round_trip_source_test("one", concat!("100| 1\n", "☛☛PUNCH 100\n"))?;
    round_trip_source_test("two", concat!("100| 1\n2\n", "☛☛PUNCH 100\n"))?;
    Ok(())
}

#[test]
fn test_round_trip_origin() -> Result<(), String> {
    round_trip_source_test(
        "begin",
        concat!(
            "LWCONNECT   =  30000\n",
            "\n",
            "100|\n",
            "              REX₆₆ OUTPUT\n",
            "            ²¹IOS₆₆ LWCONNECT\n",
            "OUTPUT->      REX₁ 777760\n", // was 777760,
            "\n",
            "☛☛PUNCH 100\n"
        ),
    )?;
    Ok(())
}
