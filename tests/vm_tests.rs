use chip8_wasm::new_vm;

#[test]
fn test_read_stored_keypress() {
    let mut vm = new_vm();

    vm.key_pressed(0xA);
    assert!(vm.is_key_pressed(0xA))
}

#[test]
fn test_read_unset_keypress_returns_none() {
    let mut vm = new_vm();

    vm.key_pressed(0x1);
    vm.key_pressed(0x2);
    vm.key_released(0x1);

    assert!(!vm.is_key_pressed(0x1));
    assert!(vm.is_key_pressed(0x2));
}
