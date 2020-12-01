use wasm_bindgen::prelude::*;
use fixedbitset::FixedBitSet;

const DISPLAY_WIDTH: usize = 128;
const DISPLAY_HEIGHT: usize = 64;

const RAM_SIZE: usize = 4096;

const MSB_MASK: u8 = 0xF0;
const LSB_MASK: u8 = 0x0F;

struct Registers {
    v: [u8; 16],
    i: u16,
    pc: u16,
    sp: u8,
}

#[wasm_bindgen]
pub struct ChipVM {
    video_mem: FixedBitSet,
    io_reg: u8,
    io_flag: bool,
    ram: [u8; 4096],
    regs: Registers,
}

impl ChipVM {
    pub fn new_vm() -> ChipVM {
        ChipVM {
            video_mem: FixedBitSet::with_capacity(DISPLAY_HEIGHT * DISPLAY_WIDTH),
            io_reg: 0,
            io_flag: false,

            ram: [0; RAM_SIZE],

            regs: Registers {
                v: [0; 16],
                i: 0,
                pc: 0,
                sp: 0,
            }
        }
    }

    pub fn read_keypress(&mut self) -> Option<u8> {
        if self.io_flag {
            Some(self.io_reg)
        } else {
            None
        }
    }

    pub fn get_display_buffer(&self) -> FixedBitSet {
        self.video_mem.clone()
    }
}

impl ChipVM {
    fn increment_pc(&mut self) {
        self.regs.pc += 2;
    }
}

#[wasm_bindgen]
impl ChipVM {
    pub fn tick(&mut self) {
        // let ins = self.read_instruction().unwrap();
        // let jmp_flag = self.exec_instruction(ins).unwrap();
        // if !jmp_flag {
        //     self.increment_pc();
        // }

    }

    pub fn video_port(&self) -> *const u32 {
        self.video_mem.as_slice().as_ptr()
    }

    pub fn store_keypress(&mut self, keycode: u8) {
        self.io_reg = keycode;
        self.io_flag = true;
    }

    pub fn get_display_width(&self) -> usize {
        DISPLAY_WIDTH
    }

    pub fn get_display_height(&self) -> usize {
        DISPLAY_HEIGHT
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum I {
    SYS,
    CLS,
    RET,
    JP,
    CALL,
    SE,
    SNE,
    LD,
    ADD,
    OR,
    AND,
    XOR,
    SUB,
    SHR,
    SUBN,
    SHL,
    RND,
    DRW,
    SKP,
    SKPN,
}

fn addr_from_n(n1: u8, n2: u8, n3: u8) -> u16 {
    ((n1 as u16) << 8) +
        ((n2 as u16) << 4) +
        (n3 as u16)
}

fn byte_from_k(k1: u8, k2: u8) -> u8 {
    (k1 << 4) + k2
}

pub struct Instruction {
    pub i_type: I,
    pub addr: Option<u16>,
    pub vx: Option<u8>,
    pub vy: Option<u8>,
    pub byte: Option<u8>,
    pub nibble: Option<u8>,
}

impl Instruction {
    fn with_defaults(ins: I) -> Instruction {
        Instruction {
            i_type: ins,
            addr: None,
            vx: None,
            vy: None,
            byte: None,
            nibble: None,
        }
    }

    pub fn from_bytes(b1: u8, b2: u8) -> Result<Instruction, String> {
        let b1_msb = (b1 & MSB_MASK) >> 4;
        let b1_lsb = b1 & LSB_MASK;
        let b2_msb = (b2 & MSB_MASK) >> 4;
        let b2_lsb = b2 & LSB_MASK;

        match (b1_msb, b1_lsb, b2_msb, b2_lsb) {
            (0, b2_lsb, _, _) if b2_lsb != 0 => {
                Ok(Instruction::with_defaults(I::SYS))
            },
            (0, 0, 0xE, 0) => {
                Ok(Instruction::with_defaults(I::CLS))
            },
            (0, 0, 0xE, 0xE) => {
                Ok(Instruction::with_defaults(I::RET))
            }
            (1, n1, n2, n3) => {
                let mut ins = Instruction::with_defaults(I::JP);
                ins.addr = Some(addr_from_n(n1, n2, n3));
                Ok(ins)
            },
            (2, n1, n2, n3) => {
                let mut ins = Instruction::with_defaults(I::CALL);
                ins.addr = Some(addr_from_n(n1, n2, n3));
                Ok(ins)
            },
            (3, vx, k1, k2) => {
                let mut ins = Instruction::with_defaults(I::SE);
                ins.vx = Some(vx);
                ins.byte = Some(byte_from_k(k1, k2));
                Ok(ins)
            },
            (4, vx, k1, k2) => {
                let mut ins = Instruction::with_defaults(I::SNE);
                ins.vx = Some(vx);
                ins.byte = Some(byte_from_k(k1, k2));
                Ok(ins)
            },
            _ => Err("Unknown instruction".to_string())
        }
    }
}
