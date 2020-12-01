use wasm_bindgen::prelude::*;
use fixedbitset::FixedBitSet;

const DISPLAY_WIDTH: usize = 128;
const DISPLAY_HEIGHT: usize = 64;

const RAM_SIZE: usize = 4096;

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
}

#[wasm_bindgen]
impl ChipVM {
    pub fn tick() {}

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
