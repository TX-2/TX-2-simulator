use std::ffi::OsStr;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use tempfile;

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
        .suffix(".tape")
        .tempfile()
        .expect("should be able to create a temporary file")
        .into_temp_path()
}

fn files_are_identical(expected: &OsStr, got: &OsStr) -> Result<(), String> {
    fn must_open(name: &OsStr) -> File {
        File::open(name).expect(&format!("should be able to open test file {name:?}"))
    }

    let expected_file = must_open(&expected);
    let got_file = must_open(&got);
    const COMPLAIN: &str = "should be able to obtain file size";
    let expected_file_len = expected_file.metadata().expect(COMPLAIN).len();
    let got_file_len = got_file.metadata().expect(COMPLAIN).len();
    if expected_file_len != got_file_len {
        return Err(format!(
            "wrong file length: {:?} is {} bytes but {:?} is {} bytes",
            expected, expected_file_len, got, got_file_len
        ));
    }

    const READ_ERR: &str = "unexpected read error";
    for (offset, (expected_byte, got_byte)) in expected_file
        .bytes()
        .zip(got_file.bytes())
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

fn assembler_golden_output_test(
    input_relative_path: &str,
    golden_output_relative_path: &str,
) -> Result<(), String> {
    let input = get_test_input_file_name(input_relative_path);
    let golden = get_test_input_file_name(golden_output_relative_path);
    let actual_output = get_temp_output_file_name();

    match assemble_file(input.as_os_str(), actual_output.as_os_str()) {
        Ok(()) => match files_are_identical(golden.as_os_str(), actual_output.as_os_str()) {
            Ok(()) => Ok(()),
            Err(e) => Err(format!(
                "{} and {} are not identical: {}",
                golden.display(),
                actual_output.display(),
                e.to_string()
            )),
        },
        Err(e) => Err(format!("failed to assemble {input_relative_path}: {e}")),
    }
}

#[test]
fn golden_output_assembling_hello_program() {
    assembler_golden_output_test("examples/hello.tx2as", "../examples/hello.tape")
        .expect("actual and golden outputs should have been identical");
}
