use fixedbitset::FixedBitSet;
use wasm_bindgen::prelude::*;

const DISPLAY_WIDTH: usize = 128;
const DISPLAY_HEIGHT: usize = 64;

const RAM_SIZE: usize = 4096;

const MSB_MASK: u8 = 0xF0;
const LSB_MASK: u8 = 0x0F;

struct Registers {
    v: [u8; 16],
    i: u16,
    pc: u16,
    stack: Vec<u16>,
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
                stack: vec![],
            },
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
        match i.addr {
            Some(addr) => {
                self.regs.pc = addr;
                Ok(true)
            }
            _ => Err(ExecError::NoAddr),
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
        match (i.vx, i.byte) {
            (Some(vx), Some(byte)) => {
                if self.regs.v[vx as usize] != byte {
                    self.increment_pc();
                    self.increment_pc();
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            _ => Err(ExecError::MissingInstructionData),
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
        } else {
            Err(ExecError::MissingInstructionData)
        }
    }
}

impl ChipVM {
    fn increment_pc(&mut self) {
        self.regs.pc += 2;
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
                let mut ins = Instruction::with_defaults(I::JP);
                ins.addr = Some(addr_from_n(n1, n2, n3));
                Ok(ins)
            }
            (2, n1, n2, n3) => {
                let mut ins = Instruction::with_defaults(I::CALL);
                ins.addr = Some(addr_from_n(n1, n2, n3));
                Ok(ins)
            }
            (3, vx, k1, k2) => {
                let mut ins = Instruction::with_defaults(I::SE);
                ins.vx = Some(vx);
                ins.byte = Some(byte_from_k(k1, k2));
                Ok(ins)
            }
            (4, vx, k1, k2) => {
                let mut ins = Instruction::with_defaults(I::SNE);
                ins.vx = Some(vx);
                ins.byte = Some(byte_from_k(k1, k2));
                Ok(ins)
            }
            (5, vx, vy, 0) => {
                let mut ins = Instruction::with_defaults(I::SE);
                ins.vx = Some(vx);
                ins.vy = Some(vy);
                Ok(ins)
            }
            (6, vx, k1, k2) => {
                let mut ins = Instruction::with_defaults(I::LD);
                ins.vx = Some(vx);
                ins.byte = Some(byte_from_k(k1, k2));
                Ok(ins)
            }
            (7, vx, k1, k2) => {
                let mut ins = Instruction::with_defaults(I::ADD);
                ins.vx = Some(vx);
                ins.byte = Some(byte_from_k(k1, k2));
                Ok(ins)
            }
            (8, vx, vy, 0) => {
                let mut ins = Instruction::with_defaults(I::LD);
                ins.vx = Some(vx);
                ins.vy = Some(vy);
                Ok(ins)
            }

            _ => Err("Unknown instruction".to_string()),
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
}
