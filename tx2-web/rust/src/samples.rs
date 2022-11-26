use std::include_bytes;

const ECHO: &[u8] = include_bytes!("../../../examples/echo.tape");
const HELLO: &[u8] = include_bytes!("../../../examples/hello.tape");

pub(crate) fn sample_binary_echo() -> &'static [u8] {
    ECHO
}
pub(crate) fn sample_binary_hello() -> &'static [u8] {
    HELLO
}
