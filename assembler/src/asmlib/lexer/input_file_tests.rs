use std::fs::OpenOptions;
use std::io::{BufReader, Read};
use std::path::PathBuf;

use super::{Lexer, Token, Unrecognised};

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

fn scan_file(body: &str) -> Result<Vec<Token>, Unrecognised> {
    let lexer = Lexer::new(body);
    lexer.collect()
}

fn run_scan_test(input_relative_path: &str) {
    let input_file_name = get_test_input_file_name(input_relative_path);

    let input_file = match OpenOptions::new().read(true).open(input_file_name) {
        Err(e) => {
            panic!("failed to open input file {input_relative_path}: {e}");
        }
        Ok(f) => f,
    };

    let source_file_body: String = {
        let mut body = String::new();
        match BufReader::new(input_file).read_to_string(&mut body) {
            Err(e) => {
                panic!("failed to read input file {input_relative_path}: {e}");
            }
            Ok(_) => body,
        }
    };

    if let Err(e) = scan_file(&source_file_body) {
        panic!("should be able to scan file {input_relative_path} with the lexer, but this failed: {e}");
    }
}

#[test]
fn scan_echo() {
    run_scan_test("examples/hello.tx2as");
}
