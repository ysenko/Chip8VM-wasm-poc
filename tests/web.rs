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

#[wasm_bindgen_test]
fn test_load_data_into_ram() {
    let data = vec![0x01, 0x02, 0x03, 0x04, 0xFF];
    let target_addr = 0x100u16;

    let mut vm = new_vm();

    assert_eq!(
        data.len() as u16,
        vm.load_bytes(data, target_addr)
    );
}