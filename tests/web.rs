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
    let rom = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0xFF];
    let target_addr = 0x100u16;

    let mut vm = new_vm();

    assert_eq!(rom.len(), vm.load_rom(rom));
    assert!(vm.is_rom_loaded());
}

#[wasm_bindgen_test]
fn test_keypress_and_release() {
    let mut vm = new_vm();

    vm.key_pressed(0xA);
    vm.key_pressed(0xB);
    vm.key_pressed(0x0);

    assert!(vm.is_key_pressed(0xA));
    assert!(vm.is_key_pressed(0xB));
    assert!(vm.is_key_pressed(0x0));

    vm.key_released(0xA);
    assert!(!vm.is_key_pressed(0xA));

    vm.key_released(0xB);
    assert!(!vm.is_key_pressed(0xB));

    vm.key_released(0x0);
    assert!(!vm.is_key_pressed(0x0));
}
