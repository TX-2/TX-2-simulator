use std::ffi::OsStr;
use std::fs::{File, OpenOptions};
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

fn get_temp_output_file_name() -> tempfile::TempPath {
    tempfile::Builder::new()
        .prefix("hello_golden_")
        .suffix(".tape")
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

fn verify_successful_disassembly(tape_file: &OsStr) -> Result<(), String> {
    let mut output: Vec<u8> = Vec::new();
    let mut errors: Vec<u8> = Vec::new();
    match disassemble_file(tape_file, &mut output, &mut errors) {
        Err(e) => Err(format!("disassembly failed: {e}")),
        Ok(()) if errors.is_empty() => Ok(()),
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

fn assembler_golden_output_test(
    input_relative_path: &str,
    golden_output_relative_path: &str,
) -> Result<(), String> {
    let input = get_test_input_file_name(input_relative_path);
    let golden = get_test_input_file_name(golden_output_relative_path);
    let actual_output = get_temp_output_file_name();
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
