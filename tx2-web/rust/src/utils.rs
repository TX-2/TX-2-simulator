// This code is derived from
// https://github.com/rustwasm/wasm-pack-template/blob/a3acfd295f0a10f2ddb6eebf6db10e057369df6a/src/utils.rs

pub(crate) fn set_panic_hook() {
    // When the `console_error_panic_hook` feature is enabled, we can call the
    // `set_panic_hook` function at least once during initialization, and then
    // we will get better error messages if our code ever panics.
    //
    // For more details see
    // https://github.com/rustwasm/console_error_panic_hook#readme
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
}
