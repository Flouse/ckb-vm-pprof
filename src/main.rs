use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::mem::transmute;
use std::path::Path;
use std::rc::Rc;

use ckb_vm::decoder::build_decoder;
use ckb_vm::instructions::{
    blank_instruction, execute_instruction, extract_opcode, instruction_length, is_basic_block_end_instruction,
};
use ckb_vm::machine::asm::{ckb_vm_asm_labels, ckb_vm_x64_execute, AsmCoreMachine, AsmMachine};
use ckb_vm::machine::VERSION0;
use ckb_vm::{Bytes, CoreMachine, DefaultMachineBuilder, Error, Machine, Register, SupportMachine, ISA_MOP};
use ckb_vm_definitions::asm::{
    calculate_slot, Trace, RET_CYCLES_OVERFLOW, RET_DECODE_TRACE, RET_DYNAMIC_JUMP, RET_EBREAK, RET_ECALL,
    RET_INVALID_PERMISSION, RET_MAX_CYCLES_EXCEEDED, RET_OUT_OF_BOUND, RET_SLOWPATH, TRACE_ITEM_LENGTH,
};
use ckb_vm_definitions::instructions::OP_CUSTOM_TRACE_END;

mod cost_model;

#[allow(dead_code)]
fn sprint_loc_file_line(loc: &Option<addr2line::Location>) -> String {
    if let Some(ref loc) = *loc {
        let mut list = vec![];
        let file = loc.file.as_ref().unwrap();
        let path = Path::new(file);
        list.push(path.display().to_string());
        if let Some(line) = loc.line {
            list.push(format!("{}", line));
        } else {
            list.push(String::from("??"));
        }
        list.join(":")
    } else {
        String::from("??:??")
    }
}

fn sprint_loc_file(loc: &Option<addr2line::Location>) -> String {
    if let Some(ref loc) = *loc {
        let file = loc.file.as_ref().unwrap();
        let path = Path::new(file);
        path.display().to_string()
    } else {
        String::from("??")
    }
}

#[allow(dead_code)]
fn sprint_fun(
    mut frame_iter: addr2line::FrameIter<
        addr2line::gimli::EndianReader<addr2line::gimli::RunTimeEndian, std::rc::Rc<[u8]>>,
    >,
) -> String {
    let mut stack: Vec<String> = vec![String::from("??")];
    loop {
        let frame = frame_iter.next().unwrap();
        if frame.is_none() {
            break;
        }
        let frame = frame.unwrap();
        let function = frame.function.unwrap();
        let function_name = String::from(addr2line::demangle_auto(
            Cow::from(function.raw_name().unwrap()),
            function.language,
        ));

        stack.push(function_name)
    }
    stack.last().unwrap().to_string()
}

// Use tree structure to store ckb vm's runtime data. At present, we care about cycles, but we may add other things in
// the future, for example, the number of times a certain instruction appears.
#[derive(Clone, Debug)]
struct PProfRecordTreeNode {
    name: String, // FILENAME + FUNCTION_NAME as expected.
    parent: Option<Rc<RefCell<PProfRecordTreeNode>>>,
    childs: Vec<Rc<RefCell<PProfRecordTreeNode>>>,
    cycles: u64,
}

impl PProfRecordTreeNode {
    // Create a new PProfRecordTreeNode with a user defined name(e.g. Function name).
    fn root() -> Self {
        Self {
            name: String::from("??:??"),
            parent: None,
            childs: vec![],
            cycles: 0,
        }
    }

    fn display_flamegraph(&self, prefix: &str, writer: &mut impl std::io::Write) {
        let prefix_name = prefix.to_owned() + self.name.as_str();
        writer
            .write_all(format!("{} {}\n", prefix_name, self.cycles).as_bytes())
            .unwrap();
        for e in &self.childs {
            e.borrow()
                .display_flamegraph(&(prefix_name.as_str().to_owned() + "; "), writer);
        }
    }
}

// Main handler.
pub struct PProfLogger {
    atsl_context:
        addr2line::Context<addr2line::gimli::EndianReader<addr2line::gimli::RunTimeEndian, std::rc::Rc<[u8]>>>,
    tree_root: Rc<RefCell<PProfRecordTreeNode>>,
    tree_node: Rc<RefCell<PProfRecordTreeNode>>,
    ra_dict: HashMap<u64, Rc<RefCell<PProfRecordTreeNode>>>,
}

impl PProfLogger {
    pub fn from_path(filename: String) -> Result<Self, Box<dyn std::error::Error>> {
        let file = std::fs::File::open(filename)?;
        let mmap = unsafe { memmap::Mmap::map(&file)? };
        let object = object::File::parse(&*mmap)?;
        let ctx = addr2line::Context::new(&object)?;
        let tree_root = Rc::new(RefCell::new(PProfRecordTreeNode::root()));
        Ok(Self {
            atsl_context: ctx,
            tree_root: tree_root.clone(),
            tree_node: tree_root,
            ra_dict: HashMap::new(),
        })
    }
    pub fn from_data(program: &Bytes) -> Result<Self, Box<dyn std::error::Error>> {
        let object = object::File::parse(&program)?;
        let ctx = addr2line::Context::new(&object)?;
        let tree_root = Rc::new(RefCell::new(PProfRecordTreeNode::root()));
        Ok(Self {
            atsl_context: ctx,
            tree_root: tree_root.clone(),
            tree_node: tree_root,
            ra_dict: HashMap::new(),
        })
    }
}

impl PProfLogger {
    fn on_step_old<'a>(&mut self, machine: &mut AsmMachine<'a>) {
        let pc = machine.machine.pc().to_u64();
        let mut decoder = ckb_vm::decoder::build_decoder::<u64>(machine.machine.isa());
        let inst = decoder.decode(machine.machine.memory_mut(), pc).unwrap();
        let inst_length = instruction_length(inst) as u64;
        let opcode = extract_opcode(inst);
        let cycles = machine
            .machine
            .instruction_cycle_func()
            .as_ref()
            .map(|f| f(inst))
            .unwrap_or(0);
        self.tree_node.borrow_mut().cycles += cycles;

        let once = |s: &mut Self, addr: u64, link: u64| {
            let loc = s.atsl_context.find_location(addr).unwrap();
            let loc_string = sprint_loc_file(&loc);
            let frame_iter = s.atsl_context.find_frames(addr).unwrap();
            let fun_string = sprint_fun(frame_iter);
            let tag_string = format!("{}:{}", loc_string, fun_string);
            let chd = Rc::new(RefCell::new(PProfRecordTreeNode {
                name: tag_string,
                parent: Some(s.tree_node.clone()),
                childs: vec![],
                cycles: 0,
            }));
            s.tree_node.borrow_mut().childs.push(chd.clone());
            s.ra_dict.insert(link, s.tree_node.clone());
            s.tree_node = chd;
        };

        if opcode == ckb_vm::instructions::insts::OP_JAL {
            let inst = ckb_vm::instructions::Utype(inst);
            // The standard software calling convention uses x1 as the return address register and x5 as an alternate
            // link register.
            if inst.rd() == ckb_vm::registers::RA || inst.rd() == ckb_vm::registers::T0 {
                let addr = pc.wrapping_add(inst.immediate_s() as u64) & 0xfffffffffffffffe;
                let link = pc + inst_length;
                once(self, addr, link);
            }
        };
        if opcode == ckb_vm::instructions::insts::OP_JALR {
            let inst = ckb_vm::instructions::Itype(inst);
            let base = machine.machine.registers()[inst.rs1()].to_u64();
            let addr = base.wrapping_add(inst.immediate_s() as u64) & 0xfffffffffffffffe;
            let link = pc + inst_length;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                once(self, addr, link);
            }
        };
        if opcode == ckb_vm::instructions::insts::OP_FAR_JUMP_ABS {
            let inst = ckb_vm::instructions::Utype(inst);
            let addr = (inst.immediate_s() as u64) & 0xfffffffffffffffe;
            let link = pc + inst_length;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                once(self, addr, link);
            }
        }
        if opcode == ckb_vm::instructions::insts::OP_FAR_JUMP_REL {
            let inst = ckb_vm::instructions::Utype(inst);
            let addr = pc.wrapping_add(inst.immediate_s() as u64) & 0xfffffffffffffffe;
            let link = pc + inst_length;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                once(self, addr, link);
            }
        }
    }

    fn on_step<'a>(&mut self, machine: &AsmMachine<'a>, slot: usize) {
        let trace = &machine.machine.inner.traces[slot];

        let mut end_index = trace.instructions.len() - 2;
        for (i, e) in trace.thread.iter().enumerate() {
            if *e == 0 {
                end_index = i.wrapping_sub(2);
                if end_index > i {
                    return;
                }
                break;
            }
        }

        self.tree_node.borrow_mut().cycles += trace.cycles;
        let inst = trace.instructions[end_index];
        let inst_length = instruction_length(inst) as u64;
        let pc = trace.address + trace.length as u64 - inst_length;
        let opcode = extract_opcode(inst);

        let once = |s: &mut Self, addr: u64, link: u64| {
            let loc = s.atsl_context.find_location(addr).unwrap();
            let loc_string = sprint_loc_file(&loc);
            let frame_iter = s.atsl_context.find_frames(addr).unwrap();
            let fun_string = sprint_fun(frame_iter);
            let tag_string = format!("{}:{}", loc_string, fun_string);
            let chd = Rc::new(RefCell::new(PProfRecordTreeNode {
                name: tag_string,
                parent: Some(s.tree_node.clone()),
                childs: vec![],
                cycles: 0,
            }));
            s.tree_node.borrow_mut().childs.push(chd.clone());
            s.ra_dict.insert(link, s.tree_node.clone());
            s.tree_node = chd;
        };

        if opcode == ckb_vm::instructions::insts::OP_JAL {
            let inst = ckb_vm::instructions::Utype(inst);
            // The standard software calling convention uses x1 as the return address register and x5 as an alternate
            // link register.
            if inst.rd() == ckb_vm::registers::RA || inst.rd() == ckb_vm::registers::T0 {
                let addr = *machine.machine.pc();
                let link = trace.address + trace.length as u64;
                once(self, addr, link);
            }
        };
        if opcode == ckb_vm::instructions::insts::OP_JALR {
            let inst = ckb_vm::instructions::Itype(inst);
            // let base = machine.machine.registers()[inst.rs1()].to_u64();
            let addr = *machine.machine.pc();
            let link = trace.address + trace.length as u64;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                once(self, addr, link);
            }
        };
        if opcode == ckb_vm::instructions::insts::OP_FAR_JUMP_ABS {
            let inst = ckb_vm::instructions::Utype(inst);
            let addr = *machine.machine.pc();
            let link = trace.address + trace.length as u64;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                once(self, addr, link);
            }
        }
        if opcode == ckb_vm::instructions::insts::OP_FAR_JUMP_REL {
            let inst = ckb_vm::instructions::Utype(inst);
            let addr = *machine.machine.pc();
            let link = trace.address + trace.length as u64;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                once(self, addr, link);
            }
        }
    }

    // fn on_exit<'a>(&mut self, machine: &mut AsmMachine<'a>) {
    //     assert_eq!(machine.machine.exit_code(), 0);
    //     self.tree_root.borrow().display_flamegraph("", &mut std::io::stdout());
    // }
}

pub struct PProfMachine<'a> {
    pub machine: AsmMachine<'a>,
    pprof_logger: Option<PProfLogger>,
}

impl CoreMachine for PProfMachine<'_> {
    type REG = u64;
    type MEM = Box<AsmCoreMachine>;

    fn pc(&self) -> &Self::REG {
        &self.machine.machine.pc()
    }

    fn update_pc(&mut self, pc: Self::REG) {
        self.machine.machine.update_pc(pc)
    }

    fn commit_pc(&mut self) {
        self.machine.machine.commit_pc()
    }

    fn memory(&self) -> &Self::MEM {
        self.machine.machine.memory()
    }

    fn memory_mut(&mut self) -> &mut Self::MEM {
        self.machine.machine.memory_mut()
    }

    fn registers(&self) -> &[Self::REG] {
        self.machine.machine.registers()
    }

    fn set_register(&mut self, idx: usize, value: Self::REG) {
        self.machine.machine.set_register(idx, value)
    }

    fn isa(&self) -> u8 {
        self.machine.machine.isa()
    }

    fn version(&self) -> u32 {
        self.machine.machine.version()
    }
}

impl Machine for PProfMachine<'_> {
    fn ecall(&mut self) -> Result<(), Error> {
        self.machine.machine.ecall()
    }

    fn ebreak(&mut self) -> Result<(), Error> {
        self.machine.machine.ebreak()
    }
}

impl<'a> PProfMachine<'a> {
    pub fn new(machine: AsmMachine<'a>) -> Self {
        Self {
            machine,
            pprof_logger: None,
        }
    }

    pub fn load_program(&mut self, program: &Bytes, args: &[Bytes]) -> Result<u64, Error> {
        self.pprof_logger = Some(PProfLogger::from_data(program).or(Err(Error::ParseError))?);
        self.machine.load_program(program, args)
    }

    pub fn run(&mut self) -> Result<i8, Error> {
        if self.machine.machine.isa() & ISA_MOP != 0 && self.machine.machine.version() == VERSION0 {
            return Err(Error::InvalidVersion);
        }
        let mut decoder = build_decoder::<u64>(self.machine.machine.isa());
        self.machine.machine.set_running(true);
        while self.machine.machine.running() {
            if self.machine.machine.reset_signal() {
                decoder.reset_instructions_cache();
                self.machine.aot_code = None;
            }
            let result = if let Some(aot_code) = &self.machine.aot_code {
                if let Some(offset) = aot_code.labels.get(self.machine.machine.pc()) {
                    let base_address = aot_code.base_address();
                    let offset_address = base_address + u64::from(*offset);
                    let f = unsafe { transmute::<u64, fn(*mut AsmCoreMachine, u64) -> u8>(base_address) };
                    f(&mut (**self.machine.machine.inner_mut()), offset_address)
                } else {
                    let slot = calculate_slot(*self.machine.machine.pc());
                    let r = unsafe { ckb_vm_x64_execute(&mut (**self.machine.machine.inner_mut())) };
                    if let Some(pprof_logger) = &mut self.pprof_logger {
                        pprof_logger.on_step(&self.machine, slot);
                    }
                    r
                }
            } else {
                let slot = calculate_slot(*self.machine.machine.pc());
                let r = unsafe { ckb_vm_x64_execute(&mut (**self.machine.machine.inner_mut())) };
                if let Some(pprof_logger) = &mut self.pprof_logger {
                    pprof_logger.on_step(&self.machine, slot);
                }
                r
            };
            match result {
                RET_DECODE_TRACE => {
                    let pc = *self.machine.machine.pc();
                    let slot = calculate_slot(pc);
                    let mut trace = Trace::default();
                    let mut current_pc = pc;
                    let mut i = 0;
                    while i < TRACE_ITEM_LENGTH {
                        let instruction = decoder.decode(self.machine.machine.memory_mut(), current_pc)?;
                        let end_instruction = is_basic_block_end_instruction(instruction);
                        current_pc += u64::from(instruction_length(instruction));
                        trace.instructions[i] = instruction;
                        trace.cycles += self
                            .machine
                            .machine
                            .instruction_cycle_func()
                            .as_ref()
                            .map(|f| f(instruction))
                            .unwrap_or(0);
                        let opcode = extract_opcode(instruction);
                        // Here we are calculating the absolute address used in direct threading
                        // from label offsets.
                        trace.thread[i] = unsafe {
                            u64::from(*(ckb_vm_asm_labels as *const u32).offset(opcode as u8 as isize))
                                + (ckb_vm_asm_labels as *const u32 as u64)
                        };
                        i += 1;
                        if end_instruction {
                            break;
                        }
                    }
                    trace.instructions[i] = blank_instruction(OP_CUSTOM_TRACE_END);
                    trace.thread[i] = unsafe {
                        u64::from(*(ckb_vm_asm_labels as *const u32).offset(OP_CUSTOM_TRACE_END as isize))
                            + (ckb_vm_asm_labels as *const u32 as u64)
                    };
                    trace.address = pc;
                    trace.length = (current_pc - pc) as u8;
                    self.machine.machine.inner_mut().traces[slot] = trace;
                }
                RET_ECALL => self.machine.machine.ecall()?,
                RET_EBREAK => self.machine.machine.ebreak()?,
                RET_DYNAMIC_JUMP => (),
                RET_MAX_CYCLES_EXCEEDED => return Err(Error::InvalidCycles),
                RET_CYCLES_OVERFLOW => return Err(Error::CyclesOverflow),
                RET_OUT_OF_BOUND => return Err(Error::OutOfBound),
                RET_INVALID_PERMISSION => return Err(Error::InvalidPermission),
                RET_SLOWPATH => {
                    let pc = *self.machine.machine.pc() - 4;
                    let instruction = decoder.decode(self.machine.machine.memory_mut(), pc)?;
                    execute_instruction(instruction, &mut self.machine.machine)?;
                }
                _ => return Err(Error::Asm(result)),
            }
        }
        Ok(self.machine.machine.exit_code())

        // let mut decoder = build_decoder::<u64>(self.isa());
        // self.machine.machine.set_running(true);
        // if let Some(pprof_logger) = self.pprof_logger.as_mut() {
        //     while self.machine.machine.running() {
        //         pprof_logger.on_step(&mut self.machine);
        //         self.machine.step(&mut decoder)?;
        //     }
        //     pprof_logger.on_exit(&mut self.machine);
        // } else {
        //     unreachable!();
        // }
        // Ok(self.machine.machine.exit_code())

        // self.machine.run()
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let flag_parser = clap::App::new("ckb-vm-pprof")
        .version("0.1")
        .about("A pprof tool for CKB VM")
        .arg(
            clap::Arg::with_name("bin")
                .long("bin")
                .value_name("filename")
                .help("Specify the name of the executable")
                .required(true),
        )
        .arg(
            clap::Arg::with_name("arg")
                .long("arg")
                .value_name("arguments")
                .help("Pass arguments to binary")
                .multiple(true),
        )
        .get_matches();
    let fl_bin = flag_parser.value_of("bin").unwrap();
    let fl_arg: Vec<_> = flag_parser.values_of("arg").unwrap_or_default().collect();

    let code_data = std::fs::read(fl_bin)?;
    let code = Bytes::from(code_data);

    let asm_core_machine = AsmCoreMachine::new(
        ckb_vm::ISA_IMC | ckb_vm::ISA_B | ckb_vm::ISA_MOP,
        ckb_vm::machine::VERSION1,
        u64::MAX,
    );
    let default_machine = DefaultMachineBuilder::new(asm_core_machine)
        .instruction_cycle_func(Box::new(cost_model::instruction_cycles))
        .build();
    let asm_machine = AsmMachine::new(default_machine, None);
    let mut machine = PProfMachine::new(asm_machine);

    let mut args = vec![fl_bin.to_string().into()];
    args.append(&mut fl_arg.iter().map(|x| Bytes::from(x.to_string())).collect());
    machine.load_program(&code, &args).unwrap();
    machine.run()?;

    machine
        .pprof_logger
        .unwrap()
        .tree_root
        .borrow()
        .display_flamegraph("", &mut std::io::stdout());

    Ok(())
}
