use std::include_bytes;

const HELLO: &[u8] = include_bytes!("../../../examples/hello.tape");

pub(crate) fn sample_binary_hello() -> &'static [u8] {
    HELLO
}
