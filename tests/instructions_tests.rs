use chip8_wasm::chip_vm;
use chip8_wasm::chip_vm::{Instruction, I};

fn get_ins_bytes(ins_code: u16) -> (u8, u8) {
    ((ins_code >> 8) as u8, (ins_code & 0x00FF) as u8)
}

#[test]
fn test_parse_SYS() {
    let (b1, b2) = get_ins_bytes(0x0123);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());
    let i_data = i.unwrap();
    assert_eq!(i_data.i_type, I::SYS);
    assert!(i_data.addr.is_none());
    assert!(i_data.byte.is_none());
    assert!(i_data.nibble.is_none());
    assert!(i_data.vx.is_none());
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_CLS() {
    let (b1, b2) = get_ins_bytes(0x00E0);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());
    let i_data = i.unwrap();
    assert_eq!(i_data.i_type, I::CLS);
    assert!(i_data.addr.is_none());
    assert!(i_data.byte.is_none());
    assert!(i_data.nibble.is_none());
    assert!(i_data.vx.is_none());
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_RET() {
    let (b1, b2) = get_ins_bytes(0x00EE);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());
    let i_data = i.unwrap();
    assert_eq!(i_data.i_type, I::RET);
    assert!(i_data.addr.is_none());
    assert!(i_data.byte.is_none());
    assert!(i_data.nibble.is_none());
    assert!(i_data.vx.is_none());
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_JP_addr() {
    let (b1, b2) = get_ins_bytes(0x1234);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());
    let i_data = i.unwrap();
    assert_eq!(i_data.i_type, I::JP);
    assert_eq!(i_data.addr, Some(0x234));
    assert!(i_data.byte.is_none());
    assert!(i_data.nibble.is_none());
    assert!(i_data.vx.is_none());
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_CALL_addr() {
    let (b1, b2) = get_ins_bytes(0x2345);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());
    let i_data = i.unwrap();
    assert_eq!(i_data.i_type, I::CALL);
    assert_eq!(i_data.addr, Some(0x345));
    assert!(i_data.byte.is_none());
    assert!(i_data.nibble.is_none());
    assert!(i_data.vx.is_none());
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_SE_vx_byte() {
    let (b1, b2) = get_ins_bytes(0x3145);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());
    let i_data = i.unwrap();
    assert_eq!(i_data.i_type, I::SE);
    assert!(i_data.addr.is_none());
    assert_eq!(i_data.byte, Some(0x45));
    assert!(i_data.nibble.is_none());
    assert_eq!(i_data.vx, Some(0x1));
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_SNE_vx_byte() {
    let (b1, b2) = get_ins_bytes(0x4145);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());
    let i_data = i.unwrap();
    assert_eq!(i_data.i_type, I::SNE);
    assert!(i_data.addr.is_none());
    assert_eq!(i_data.byte, Some(0x45));
    assert!(i_data.nibble.is_none());
    assert_eq!(i_data.vx, Some(0x1));
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_SE_vx_vy() {
    let (b1, b2) = get_ins_bytes(0x5230);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());

    let i_data = i.unwrap();

    assert_eq!(i_data.i_type, I::SE);
    assert!(i_data.addr.is_none());
    assert!(i_data.byte.is_none());
    assert!(i_data.nibble.is_none());
    assert_eq!(i_data.vx, Some(0x2));
    assert_eq!(i_data.vy, Some(0x3));
}

#[test]
fn test_parse_LD_vx_byte() {
    let (b1, b2) = get_ins_bytes(0x62AB);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());

    let i_data = i.unwrap();

    assert_eq!(i_data.i_type, I::LD);
    assert!(i_data.addr.is_none());
    assert_eq!(i_data.byte.unwrap(), 0xAB);
    assert!(i_data.nibble.is_none());
    assert_eq!(i_data.vx, Some(0x2));
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_ADD_vx_byte() {
    let (b1, b2) = get_ins_bytes(0x72AB);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());

    let i_data = i.unwrap();

    assert_eq!(i_data.i_type, I::ADD);
    assert!(i_data.addr.is_none());
    assert_eq!(i_data.byte.unwrap(), 0xAB);
    assert!(i_data.nibble.is_none());
    assert_eq!(i_data.vx, Some(0x2));
    assert!(i_data.vy.is_none());
}

#[test]
fn test_parse_LD_vx_vy() {
    let (b1, b2) = get_ins_bytes(0x8230);

    let i = Instruction::from_bytes(b1, b2);

    assert!(i.is_ok());

    let i_data = i.unwrap();

    assert_eq!(i_data.i_type, I::LD);
    assert!(i_data.addr.is_none());
    assert!(i_data.byte.is_none());
    assert!(i_data.nibble.is_none());
    assert_eq!(i_data.vx, Some(0x2));
    assert_eq!(i_data.vy, Some(0x3));
}
