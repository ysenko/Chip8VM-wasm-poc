use chip8_wasm::new_vm;

#[test]
fn test_read_stored_keypress() {
    let mut vm = new_vm();

    vm.store_keypress(1);
    assert_eq!(1, vm.read_keypress().unwrap())
}

#[test]
fn test_read_unset_keypress_returns_none() {
    let mut vm = new_vm();
    assert!(vm.read_keypress().is_none());
}