use fixedbitset::FixedBitSet;
use wasm_bindgen::prelude::*;

use super::utils::generate_random_u8;

const DISPLAY_WIDTH: usize = 128;
const DISPLAY_HEIGHT: usize = 64;

const RAM_SIZE: usize = 4096;

const MSB_MASK: u8 = 0xF0;
const LSB_MASK: u8 = 0x0F;

const DEFAULT_SPRITES: [[u8; 5]; 16] = [
    [0xF0, 0x90, 0x90, 0x90, 0xF0], // 0
    [0x20, 0x60, 0x20, 0x20, 0x70], // 1
    [0xF0, 0x10, 0xF0, 0x80, 0xF0], // 2
    [0xF0, 0x10, 0xF0, 0x10, 0xF0], // 3
    [0x90, 0x90, 0xF0, 0x10, 0x10], // 4
    [0xF0, 0x80, 0xF0, 0x10, 0xF0], // 5
    [0xF0, 0x80, 0xF0, 0x90, 0xF0], // 6
    [0xF0, 0x10, 0x20, 0x40, 0x40], // 7
    [0xF0, 0x90, 0xF0, 0x90, 0xF0], // 8
    [0xF0, 0x90, 0xF0, 0x10, 0xF0], // 9
    [0xF0, 0x90, 0xF0, 0x90, 0x90], // A
    [0xE0, 0x90, 0xE0, 0x90, 0xE0], // B
    [0xF0, 0x80, 0x80, 0x80, 0xF0], // C
    [0xE0, 0x90, 0x90, 0x90, 0xE0], // D
    [0xF0, 0x80, 0xF0, 0x80, 0xF0], // E
    [0xF0, 0x80, 0xF0, 0x80, 0x80], // F
];
const DEFAULT_SPRITES_LOAD_ADDR: usize = 0x0;

struct Registers {
    v: [u8; 16],
    i: u16,
    pc: u16,
    stack: Vec<u16>,
}

impl Registers {
    pub fn set_carry(&mut self, carry: bool) {
        self.v[0xF] = if carry { 1 } else { 0 };
    }
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
        let mut vm = ChipVM {
            video_mem: FixedBitSet::with_capacity(DISPLAY_HEIGHT * DISPLAY_WIDTH),
            io_reg: 0,
            io_flag: false,

            ram: [0; RAM_SIZE],

            regs: Registers {
                v: [0; 16],
                i: 0,
                pc: 0,
                stack: vec![],
            },
        };

        vm.load_default_sprites();

        vm
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

type SkipPCIncr = bool;
type ExecResult = Result<SkipPCIncr, ExecError>;

#[derive(Debug, Eq, PartialEq)]
enum ExecError {
    NoAddr,
    MissingInstructionData,
    EmptyStack,
    UnknownError,
}

impl ChipVM {
    fn exec_sys(&mut self, _i: Instruction) -> ExecResult {
        Ok(false)
    }

    fn exec_cls(&mut self, _i: Instruction) -> ExecResult {
        self.video_mem.clear();
        Ok(false)
    }

    fn exec_ret(&mut self, _i: Instruction) -> ExecResult {
        match self.regs.stack.pop() {
            Some(addr) => {
                self.regs.pc = addr;
                Ok(true)
            }
            _ => Err(ExecError::EmptyStack),
        }
    }

    fn exec_jp(&mut self, i: Instruction) -> ExecResult {
        match (i.addr, i.vx) {
            (Some(addr), None) => {
                self.regs.pc = addr;
                Ok(true)
            }
            (Some(addr), Some(0)) => {
                let v0_val = self.regs.v[0x0];
                self.regs.pc = addr + v0_val as u16;
                Ok(true)
            }
            _ => Err(ExecError::MissingInstructionData),
        }
    }

    fn exec_call(&mut self, i: Instruction) -> ExecResult {
        match i.addr {
            Some(addr) => {
                self.regs.stack.push(self.regs.pc);
                self.regs.pc = addr;
                Ok(true)
            }
            _ => Err(ExecError::NoAddr),
        }
    }

    fn exec_se(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() && i.byte.is_some() {
            if self.regs.v[i.vx.unwrap() as usize] == i.byte.unwrap() {
                self.increment_pc();
                self.increment_pc();
                Ok(true)
            } else {
                Ok(false)
            }
        } else if i.vx.is_some() && i.vy.is_some() {
            if self.regs.v[i.vx.unwrap() as usize] == self.regs.v[i.vy.unwrap() as usize] {
                self.increment_pc();
                self.increment_pc();
                Ok(true)
            } else {
                Ok(false)
            }
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_sne(&mut self, i: Instruction) -> ExecResult {
        let (arg1, arg2) = if i.vx.is_some() & i.byte.is_some() {
            let vx = i.vx.unwrap();
            (self.regs.v[vx as usize], i.byte.unwrap())
        } else if i.vx.is_some() & i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            (self.regs.v[vx as usize], self.regs.v[vy as usize])
        } else {
            return Err(ExecError::MissingInstructionData);
        };
        if arg1 != arg2 {
            self.increment_pc();
            self.increment_pc();
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn exec_ld(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() && i.byte.is_some() {
            self.regs.v[i.vx.unwrap() as usize] = i.byte.unwrap();
            Ok(false)
        } else if i.vx.is_some() && i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            self.regs.v[vx as usize] = self.regs.v[vy as usize];
            Ok(false)
        } else if i.addr.is_some() {
            self.regs.i = i.addr.unwrap();
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_add(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() && i.byte.is_some() {
            let vx = i.vx.unwrap();
            let byte = i.byte.unwrap();
            self.regs.v[vx as usize] += byte;
            Ok(false)
        } else if i.vx.is_some() & i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            let (res, carry) = self.regs.v[vx as usize].overflowing_add(self.regs.v[vy as usize]);
            self.regs.v[vx as usize] = res;
            self.regs.set_carry(carry);
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_or(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() && i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            self.regs.v[vx as usize] |= self.regs.v[vy as usize];
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_and(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() & i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            self.regs.v[vx as usize] &= self.regs.v[vy as usize];
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_xor(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() & i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            self.regs.v[vx as usize] ^= self.regs.v[vy as usize];
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_sub(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() & i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            let vx_val = self.regs.v[vx as usize];
            let vy_val = self.regs.v[vy as usize];
            let (res, _) = vx_val.overflowing_sub(vy_val);
            self.regs.set_carry(vx_val >= vy_val);
            self.regs.v[vx as usize] = res;
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_shr(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() {
            let vx = i.vx.unwrap();
            let vx_val = self.regs.v[vx as usize];
            self.regs.v[vx as usize] = vx_val >> 1;
            self.regs.set_carry(vx_val.trailing_ones() > 0);
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_subn(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() & i.vy.is_some() {
            let vx = i.vx.unwrap();
            let vy = i.vy.unwrap();
            let vx_val = self.regs.v[vx as usize];
            let vy_val = self.regs.v[vy as usize];
            let (res, _) = vy_val.overflowing_sub(vx_val);
            self.regs.set_carry(vy_val >= vx_val);
            self.regs.v[vx as usize] = res;
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_shl(&mut self, i: Instruction) -> ExecResult {
        if i.vx.is_some() {
            let vx = i.vx.unwrap();
            let vx_val = self.regs.v[vx as usize];
            self.regs.v[vx as usize] = vx_val << 1;
            self.regs.set_carry(vx_val.leading_ones() > 0);
            Ok(false)
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }

    fn exec_rnd(&mut self, i: Instruction) -> ExecResult {
        match (i.vx, i.byte) {
            (Some(vx), Some(byte)) => {
                let rnd = generate_random_u8();
                self.regs.v[vx as usize] = rnd & byte;
                Ok(false)
            }
            _ => Err(ExecError::MissingInstructionData),
        }
    }

    fn exec_drw(&mut self, i: Instruction) -> ExecResult {
        match (i.vx, i.vy, i.nibble) {
            (Some(vx), Some(vy), Some(nibble)) => {
                self.regs.set_carry(false);
                let width = self.get_display_width();

                let sprite_base_addr = self.regs.i as usize;
                let pixel_base_addr = (vy as usize) * width + (vx as usize);

                for row_offset in 0..(nibble as usize) {
                    for col_offset in 0..8usize {
                        let pixel_addr = pixel_base_addr + row_offset * width + col_offset;
                        let current = self.video_mem.contains(pixel_addr);

                        let sprite_row = self.ram[sprite_base_addr + row_offset].reverse_bits();
                        let mask: u8 = 0x1 << col_offset;
                        let new = (sprite_row & mask) == mask;

                        self.video_mem.set(pixel_addr, current ^ new);

                        let erased = current && (!self.video_mem.contains(pixel_addr));
                        if erased {
                            self.regs.set_carry(erased);
                        }
                    }
                }
                Ok(false)
            }
            _ => Err(ExecError::MissingInstructionData),
        }
    }
}

impl ChipVM {
    fn increment_pc(&mut self) {
        self.regs.pc += 2;
    }

    fn load_default_sprites(&mut self) {
        for (offset, sprite_arr) in DEFAULT_SPRITES.iter().enumerate() {
            let base_addr = DEFAULT_SPRITES_LOAD_ADDR + offset * sprite_arr.len();
            for (byte_offset, sprite_byte) in sprite_arr.clone().iter().enumerate() {
                self.ram[base_addr + byte_offset] = *sprite_byte;
            }
        }
    }

    fn exec_instruction(&mut self, ins: Instruction) -> ExecResult {
        match ins.i_type {
            I::SYS => self.exec_sys(ins),
            I::CLS => self.exec_cls(ins),
            I::RET => self.exec_ret(ins),
            I::JP => self.exec_jp(ins),
            I::CALL => self.exec_call(ins),
            I::SE => self.exec_se(ins),
            I::SNE => self.exec_sne(ins),
            I::LD => self.exec_ld(ins),
            I::ADD => self.exec_add(ins),
            I::OR => self.exec_or(ins),
            I::AND => self.exec_and(ins),
            I::XOR => self.exec_xor(ins),
            I::SUB => self.exec_sub(ins),
            I::SHR => self.exec_shr(ins),
            I::SUBN => self.exec_subn(ins),
            I::SHL => self.exec_shl(ins),
            I::RND => self.exec_rnd(ins),
            I::DRW => self.exec_drw(ins),

            _ => Err(ExecError::UnknownError),
        }
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
    ((n1 as u16) << 8) + ((n2 as u16) << 4) + (n3 as u16)
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

    pub fn set_byte(mut self, byte: u8) -> Self {
        self.byte = Some(byte);
        self
    }

    pub fn set_addr(mut self, addr: u16) -> Self {
        self.addr = Some(addr);
        self
    }

    pub fn set_vx(mut self, vx: u8) -> Self {
        self.vx = Some(vx);
        self
    }

    pub fn set_vy(mut self, vy: u8) -> Self {
        self.vy = Some(vy);
        self
    }

    pub fn set_nibble(mut self, nibble: u8) -> Self {
        self.nibble = Some(nibble);
        self
    }

    pub fn from_bytes(b1: u8, b2: u8) -> Result<Instruction, String> {
        let b1_msb = (b1 & MSB_MASK) >> 4;
        let b1_lsb = b1 & LSB_MASK;
        let b2_msb = (b2 & MSB_MASK) >> 4;
        let b2_lsb = b2 & LSB_MASK;

        match (b1_msb, b1_lsb, b2_msb, b2_lsb) {
            (0, b2_lsb, _, _) if b2_lsb != 0 => Ok(Instruction::with_defaults(I::SYS)),
            (0, 0, 0xE, 0) => Ok(Instruction::with_defaults(I::CLS)),
            (0, 0, 0xE, 0xE) => Ok(Instruction::with_defaults(I::RET)),
            (1, n1, n2, n3) => {
                Ok(Instruction::with_defaults(I::JP).set_addr(addr_from_n(n1, n2, n3)))
            }
            (2, n1, n2, n3) => {
                Ok(Instruction::with_defaults(I::CALL).set_addr(addr_from_n(n1, n2, n3)))
            }
            (3, vx, k1, k2) => Ok(Instruction::with_defaults(I::SE)
                .set_vx(vx)
                .set_byte(byte_from_k(k1, k2))),
            (4, vx, k1, k2) => Ok(Instruction::with_defaults(I::SNE)
                .set_vx(vx)
                .set_byte(byte_from_k(k1, k2))),
            (5, vx, vy, 0) => Ok(Instruction::with_defaults(I::SE).set_vx(vx).set_vy(vy)),
            (6, vx, k1, k2) => Ok(Instruction::with_defaults(I::LD)
                .set_vx(vx)
                .set_byte(byte_from_k(k1, k2))),
            (7, vx, k1, k2) => Ok(Instruction::with_defaults(I::ADD)
                .set_vx(vx)
                .set_byte(byte_from_k(k1, k2))),
            (8, vx, vy, 0) => Ok(Instruction::with_defaults(I::LD).set_vx(vx).set_vy(vy)),
            (8, vx, vy, 1) => Ok(Instruction::with_defaults(I::OR).set_vx(vx).set_vy(vy)),
            (8, vx, vy, 2) => Ok(Instruction::with_defaults(I::AND).set_vx(vx).set_vy(vy)),
            (8, vx, vy, 3) => Ok(Instruction::with_defaults(I::XOR).set_vx(vx).set_vy(vy)),
            (8, vx, vy, 4) => Ok(Instruction::with_defaults(I::ADD).set_vx(vx).set_vy(vy)),
            (8, vx, vy, 5) => Ok(Instruction::with_defaults(I::SUB).set_vx(vx).set_vy(vy)),
            (8, vx, _, 6) => Ok(Instruction::with_defaults(I::SHR).set_vx(vx)),
            (8, vx, vy, 7) => Ok(Instruction::with_defaults(I::SUBN).set_vx(vx).set_vy(vy)),
            (8, vx, _, 0xE) => Ok(Instruction::with_defaults(I::SHL).set_vx(vx)),
            (9, vx, vy, 0) => Ok(Instruction::with_defaults(I::SNE).set_vx(vx).set_vy(vy)),
            (0xA, n1, n2, n3) => {
                Ok(Instruction::with_defaults(I::LD).set_addr(addr_from_n(n1, n2, n3)))
            }
            (0xB, n1, n2, n3) => Ok(Instruction::with_defaults(I::JP)
                .set_addr(addr_from_n(n1, n2, n3))
                .set_vx(0x0)),
            (0xC, vx, k1, k2) => Ok(Instruction::with_defaults(I::RND)
                .set_vx(vx)
                .set_byte(byte_from_k(k1, k2))),
            (0xD, vx, vy, nibble) => Ok(Instruction::with_defaults(I::DRW)
                .set_vx(vx)
                .set_vy(vy)
                .set_nibble(nibble)),

            _ => Err("Unknown instruction".to_string()),
        }
    }
}

#[cfg(test)]
mod test_vm_utils {
    use super::*;

    #[test]
    fn test_load_default_sprites() {
        let vm = ChipVM::new_vm();

        for (offset, sprite_arr) in DEFAULT_SPRITES.iter().enumerate() {
            let start_addr = DEFAULT_SPRITES_LOAD_ADDR + (offset * sprite_arr.len());
            let actual_sprite_arr = &vm.ram[start_addr..(start_addr + sprite_arr.len())];
            assert_eq!(sprite_arr, actual_sprite_arr)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_skip_pc_incr(res: ExecResult) {
        assert!(res.unwrap())
    }

    fn assert_no_skip_pc_increment(res: ExecResult) {
        assert!(!res.unwrap())
    }

    fn assert_carry(vm: &ChipVM) {
        assert_eq!(1, vm.regs.v[0xF]);
    }

    fn assert_no_carry(vm: &ChipVM) {
        assert_eq!(0, vm.regs.v[0xF]);
    }

    fn assert_sprite_on_screen(vm: &ChipVM, sprite_row: usize, sprite_col: usize, sprite: &[u8]) {
        let mut actual_pixels: Vec<u8> = vec![];
        let base_pixel_addr = sprite_row * vm.get_display_width() + sprite_col;
        for row_offset in 0..sprite.len() {
            let mut actual_sprite_row = 0u8;
            for col_offset in 0..8 {
                let pixel_add = base_pixel_addr + row_offset * vm.get_display_width() + col_offset;
                actual_sprite_row += (if vm.video_mem.contains(pixel_add) {
                    1
                } else {
                    0
                }) << col_offset;
            }
            actual_pixels.push(actual_sprite_row.reverse_bits());
        }

        assert_eq!(sprite, actual_pixels.as_slice());
    }

    #[test]
    fn test_exec_instruction_sys() {
        let mut vm = ChipVM::new_vm();
        let i = Instruction::with_defaults(I::SYS);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
    }

    #[test]
    fn test_exec_instruction_cls() {
        let mut vm = ChipVM::new_vm();

        vm.video_mem.set_range(128..256, true);
        // Sanity check.
        assert_eq!(
            vm.video_mem.ones().collect::<Vec<usize>>(),
            (128..256).into_iter().collect::<Vec<usize>>()
        );

        let i = Instruction::with_defaults(I::CLS);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(vm.video_mem.ones().collect::<Vec<usize>>(), vec![]);
    }

    #[test]
    fn test_exec_instruction_ret_error_on_empty_stack() {
        let mut vm = ChipVM::new_vm();
        let i = Instruction::with_defaults(I::RET);

        // Stack is empty. This should return an error.
        let res = vm.exec_instruction(i);

        assert!(res.is_err());
        assert_eq!(res.unwrap_err(), ExecError::EmptyStack);
    }

    #[test]
    fn test_exec_instruction_ret() {
        let mut vm = ChipVM::new_vm();
        let ret_addr = 0x1234;
        vm.regs.stack.push(ret_addr);

        let i = Instruction::with_defaults(I::RET);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(ret_addr, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_jp() {
        let mut vm = ChipVM::new_vm();
        let jp_addr = 0x1234;

        let mut i = Instruction::with_defaults(I::JP);
        i.addr = Some(jp_addr);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(jp_addr, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_call() {
        let mut vm = ChipVM::new_vm();
        let call_addr = 0x1234;
        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::CALL);
        i.addr = Some(call_addr);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(call_addr, vm.regs.pc);
        assert_eq!(Some(prev_pc), vm.regs.stack.pop());
    }

    #[test]
    fn test_exec_instruction_call_error_on_no_addr() {
        let mut vm = ChipVM::new_vm();
        let i = Instruction::with_defaults(I::CALL);

        let res = vm.exec_instruction(i);

        assert!(res.is_err());
        assert_eq!(ExecError::NoAddr, res.unwrap_err());
    }

    #[test]
    fn test_exec_instruction_sevx_byte_skip() {
        let vx = 2;
        let vx_val = 42;
        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx] = vx_val;
        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::SE);
        i.vx = Some(vx as u8);
        i.byte = Some(vx_val);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(prev_pc + 4, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_sevx_byte_no_skip() {
        let vx = 2;
        let vx_val = 42;
        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx] = 1;
        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::SE);
        i.vx = Some(vx as u8);
        i.byte = Some(vx_val);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_se_error_on_missing_data() {
        let mut vm = ChipVM::new_vm();
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SE);

        let res = vm.exec_instruction(i);

        assert!(res.is_err());
        assert_eq!(prev_pc, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_snevx_byte_skip() {
        let vx = 2;
        let vx_val = 42;
        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx] = vx_val;
        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::SNE);
        i.vx = Some(vx as u8);
        i.byte = Some(0x1);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(prev_pc + 4, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_snevx_byte_no_skip() {
        let vx = 2;
        let vx_val = 42;
        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx] = vx_val;
        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::SNE);
        i.vx = Some(vx as u8);
        i.byte = Some(vx_val);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_snevx_byte_error_on_missing_data() {
        let mut vm = ChipVM::new_vm();
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SNE);

        let res = vm.exec_instruction(i);

        assert!(res.is_err());
        assert_eq!(prev_pc, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_sevx_vy_skip() {
        let vx = 2;
        let vy = 3;
        let some_val = 42;

        let mut vm = ChipVM::new_vm();

        vm.regs.v[vx] = some_val;
        vm.regs.v[vy] = some_val;

        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::SE);
        i.vx = Some(vx as u8);
        i.vy = Some(vy as u8);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(prev_pc + 4, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_sevx_vy_no_skip() {
        let vx = 2;
        let vy = 3;
        let vx_val = 42;
        let vy_val = 10;

        let mut vm = ChipVM::new_vm();

        vm.regs.v[vx] = vx_val;
        vm.regs.v[vy] = vy_val;

        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::SE);
        i.vx = Some(vx as u8);
        i.vy = Some(vy as u8);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_ldvx_byte() {
        let vx = 2;
        let byte = 0x10;

        let mut vm = ChipVM::new_vm();
        let prev_pc = vm.regs.pc;
        let mut i = Instruction::with_defaults(I::LD);
        i.vx = Some(vx);
        i.byte = Some(byte);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(vm.regs.v[vx as usize], byte);
    }

    #[test]
    fn test_exec_instruction_ldvx_byte_error_onm_missing_data() {
        let mut vm = ChipVM::new_vm();
        let i = Instruction::with_defaults(I::LD);

        let res = vm.exec_instruction(i);

        assert!(res.is_err());
        assert_eq!(res.unwrap_err(), ExecError::MissingInstructionData);
    }

    #[test]
    fn exec_instruction_add_vx_byte() {
        let vx: u8 = 2;
        let initial_vx_val = 0x2;
        let value_to_add = 0x2;
        let mut vm = ChipVM::new_vm();
        let mut i = Instruction::with_defaults(I::ADD);
        let prev_pc = vm.regs.pc;
        vm.regs.v[vx as usize] = initial_vx_val;

        i.vx = Some(vx);
        i.byte = Some(value_to_add);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(initial_vx_val + value_to_add, vm.regs.v[vx as usize]);
    }

    #[test]
    fn exec_instruction_ld_vx_vy() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0x2;
        let initial_vy_val = 0x3;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let mut i = Instruction::with_defaults(I::LD);
        i.vx = Some(vx);
        i.vy = Some(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(initial_vy_val, vm.regs.v[vx as usize]);
        assert_eq!(vm.regs.v[vx as usize], vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_or_vx_vy() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0xAA;
        let initial_vy_val = 0x55;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::OR).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(initial_vy_val | initial_vx_val, vm.regs.v[vx as usize]);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_and_vx_vy() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0xEE;
        let initial_vy_val = 0x33;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::AND).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(initial_vy_val & initial_vx_val, vm.regs.v[vx as usize]);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_xor_vx_vy() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0xDD;
        let initial_vy_val = 0xDD;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::XOR).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(initial_vy_val ^ initial_vx_val, vm.regs.v[vx as usize]);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_add_vx_vy_with_carry() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0xDD;
        let initial_vy_val = 0xDD;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::ADD).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        let (res, carry) = initial_vx_val.overflowing_add(initial_vy_val);
        assert_eq!(res, vm.regs.v[vx as usize]);
        if carry {
            assert_carry(&vm)
        } else {
            assert_no_carry(&vm)
        };
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_add_vx_vy_no_carry() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0x2;
        let initial_vy_val = 0x3;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::ADD).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        let (res, carry) = initial_vx_val.overflowing_add(initial_vy_val);
        assert_eq!(res, vm.regs.v[vx as usize]);
        if carry {
            assert_carry(&vm)
        } else {
            assert_no_carry(&vm)
        };
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_sub_vx_vy_no_borrow() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0xA;
        let initial_vy_val = 0x5;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SUB).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0x5, vm.regs.v[vx as usize]);
        assert_carry(&vm);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_sub_vx_vy_with_borrow() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0x2;
        let initial_vy_val = 0x3;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SUB).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0xFF, vm.regs.v[vx as usize]);
        assert_no_carry(&vm);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_shr_vx_vy_with_carry() {
        let vx: u8 = 2;
        let initial_vx_val = 0x9;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SHR).set_vx(vx);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0x4, vm.regs.v[vx as usize]);
        assert_carry(&vm);
    }

    #[test]
    fn exec_instruction_shr_vx_vy_no_carry() {
        let vx: u8 = 2;
        let initial_vx_val = 0x8;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SHR).set_vx(vx);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0x4, vm.regs.v[vx as usize]);
        assert_no_carry(&vm);
    }

    #[test]
    fn exec_instruction_subn_vx_vy_no_borrow() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0x5;
        let initial_vy_val = 0xA;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SUBN).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0x5, vm.regs.v[vx as usize]);
        assert_carry(&vm);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_subn_vx_vy_with_borrow() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0x3;
        let initial_vy_val = 0x2;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SUBN).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0xFF, vm.regs.v[vx as usize]);
        assert_no_carry(&vm);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
    }

    #[test]
    fn exec_instruction_shl_vx_vy_with_carry() {
        let vx: u8 = 2;
        let initial_vx_val = 0x81;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SHL).set_vx(vx);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0x2, vm.regs.v[vx as usize]);
        assert_carry(&vm);
    }

    #[test]
    fn exec_instruction_shl_vx_vy_no_carry() {
        let vx: u8 = 2;
        let initial_vx_val = 0x1;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SHL).set_vx(vx);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(0x2, vm.regs.v[vx as usize]);
        assert_no_carry(&vm);
    }

    #[test]
    fn exec_instruction_sne_vx_vy_skip() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0x1;
        let initial_vy_val = 0x2;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SNE).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(prev_pc + 4, vm.regs.pc);

        assert_eq!(initial_vx_val, vm.regs.v[vx as usize]);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
        assert_no_carry(&vm);
    }

    #[test]
    fn exec_instruction_sne_vx_vy_no_skip() {
        let vx: u8 = 2;
        let vy: u8 = 3;
        let initial_vx_val = 0x1;
        let initial_vy_val = 0x1;

        let mut vm = ChipVM::new_vm();
        vm.regs.v[vx as usize] = initial_vx_val;
        vm.regs.v[vy as usize] = initial_vy_val;
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::SNE).set_vx(vx).set_vy(vy);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);

        assert_eq!(initial_vx_val, vm.regs.v[vx as usize]);
        assert_eq!(initial_vy_val, vm.regs.v[vy as usize]);
        assert_no_carry(&vm);
    }

    #[test]
    fn test_exec_instruction_ld_i_addr() {
        let addr = 0x123;
        let mut vm = ChipVM::new_vm();
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::LD).set_addr(addr);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(addr, vm.regs.i);
        assert_eq!(prev_pc, vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_jp_v0_addr() {
        let addr = 0x123;
        let v0_val = 0x1;
        let mut vm = ChipVM::new_vm();
        vm.regs.v[0x0] = v0_val;

        let i = Instruction::with_defaults(I::JP).set_addr(addr).set_vx(0x0);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_skip_pc_incr(res);
        assert_eq!(addr + (v0_val as u16), vm.regs.pc);
    }

    #[test]
    fn test_exec_instruction_rnd_vx_byte() {
        let byte = 0xFF;
        let vx: u8 = 2;
        let mut vm = ChipVM::new_vm();
        let prev_pc = vm.regs.pc;

        let i = Instruction::with_defaults(I::RND).set_byte(byte).set_vx(vx);

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_eq!(prev_pc, vm.regs.pc);
        assert_eq!(byte & 0x42, vm.regs.v[vx as usize]); // random() test functions always returns 0x42
    }

    #[test]
    fn test_exec_instruction_drw_no_pixels_erased() {
        let i = Instruction::with_defaults(I::DRW)
            .set_vx(0x0)
            .set_vy(0x0)
            .set_nibble(0x5);

        let mut vm = ChipVM::new_vm();
        vm.regs.i = DEFAULT_SPRITES_LOAD_ADDR as u16;

        let res = vm.exec_instruction(i);

        assert!(res.is_ok());
        assert_no_skip_pc_increment(res);
        assert_no_carry(&vm);
        assert_sprite_on_screen(
            &vm,
            0,
            0,
            &vm.ram[DEFAULT_SPRITES_LOAD_ADDR..(DEFAULT_SPRITES_LOAD_ADDR + 5)],
        );
    }

    #[test]
    fn test_exec_instruction_drw_all_pixels_erased() {
        let draw_zero = Instruction::with_defaults(I::DRW)
            .set_vx(0x0)
            .set_vy(0x0)
            .set_nibble(0x5);

        let erase_zero = Instruction::with_defaults(I::DRW)
            .set_vx(0x0)
            .set_vy(0x0)
            .set_nibble(0x5);

        let mut vm = ChipVM::new_vm();
        vm.regs.i = DEFAULT_SPRITES_LOAD_ADDR as u16;

        let res = vm.exec_instruction(draw_zero);
        assert!(res.is_ok());
        assert_no_carry(&vm);

        let res = vm.exec_instruction(erase_zero);
        assert!(res.is_ok());
        assert_sprite_on_screen(&vm, 0x0, 0x0, &[0; 5]);
        assert_carry(&vm);
    }
}
