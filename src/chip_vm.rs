use wasm_bindgen::prelude::*;
use fixedbitset::FixedBitSet;

const DISPLAY_WIDTH: usize = 128;
const DISPLAY_HEIGHT: usize = 64;

#[wasm_bindgen]
pub struct ChipVM {
    video_mem: FixedBitSet,
    io_reg: u8,
    io_flag: bool,
}

impl ChipVM {
    pub fn new_vm() -> ChipVM {
        ChipVM {
            video_mem: FixedBitSet::with_capacity(DISPLAY_HEIGHT * DISPLAY_WIDTH),
            io_reg: 0,
            io_flag: false,
        }
    }

    pub fn read_keypress(&mut self) -> Option<u8> {
        if self.io_flag {
            Some(self.io_reg)
        } else {
            None
        }
    }
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

#[cfg(test)]
mod tests {

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

