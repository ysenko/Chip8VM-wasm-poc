//! Test suite for the Web and headless browsers.

#![cfg(target_arch = "wasm32")]

extern crate wasm_bindgen_test;
use chip8_wasm::new_vm;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
fn test_get_display_size() {
    let vm = new_vm();

    assert_eq!(128, vm.get_display_width());
    assert_eq!(64, vm.get_display_height());
}
