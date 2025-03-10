use std::collections::{HashMap, HashSet};
use std::ops::Deref;


use crate::ir::*;
use crate::opt::FunctionPass;
use crate::*;

pub type Deadcode = FunctionPass<Repeat<DeadcodeInner>>;

#[derive(Default, Clone, Copy, Debug)]
pub struct DeadcodeInner {}

impl Optimize<FunctionDefinition> for DeadcodeInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut replaces = HashMap::<Operand, Operand>::new();
        let mut allocs = HashSet::<Operand>::new();
        // collect the use of local var
        for (i, dtype) in code.allocations.iter().enumerate() {
            let rid = RegisterId::Local { aid: i };
            let _unused = allocs.insert(Operand::Register { rid, dtype: dtype.clone().into_inner() });
        }
        // remove unused local allocations
        code.walk(|e| {
            if allocs.contains(e) {
                let _unused = allocs.remove(e);
            }
        });

        if !allocs.is_empty() {
            let mut count = 0;
            let mut vec = Vec::new();
            for (i, dtype) in code.allocations.iter().enumerate() {
                let rid = RegisterId::Local { aid: i };
                let operand = Operand::Register { rid, dtype: dtype.clone().into_inner() };
                if !allocs.contains(&operand) {
                    if i != count {
                        let rid = RegisterId::Local { aid: count };
                        let _unused = replaces.insert(operand,
                            Operand::Register { rid, dtype: dtype.clone().into_inner() });
                        
                    } else {
                        vec.push(i);
                    }
                    count += 1;
                }
            }
            vec.reverse();
            for i in vec.iter() {
                code.allocations.remove(*i);
            }
        }

        let mut unused_instrs = HashSet::<Operand>::new();
        // remove nop instruction
        let mut nops = HashMap::<BlockId, Vec<usize>>::new();
        for (bid, block) in &code.blocks {
            for (i, instr) in block.instructions.iter().enumerate() {
                if !instr.deref().has_no_side_effects() {
                    continue;
                }
                match instr.deref() {
                    Instruction::Nop => {
                        nops.entry(*bid).and_modify(|e| e.push(i)).or_insert(vec![i]);
                    }
                    Instruction::BinOp { lhs, rhs, dtype, ..  } => {
                        unused_instrs.remove(lhs);
                        unused_instrs.remove(rhs);
                        let rid = RegisterId::Temp { bid: *bid, iid: i };
                        let _unused = unused_instrs.insert(Operand::Register { rid, dtype: dtype.clone() });
                    }
                    Instruction::UnaryOp { operand, dtype, .. } => {
                        unused_instrs.remove(operand);
                        let rid = RegisterId::Temp { bid: *bid, iid: i };
                        let _unused = unused_instrs.insert(Operand::Register { rid, dtype: dtype.clone() });

                    }
                    Instruction::GetElementPtr { ptr, offset, dtype } => {
                        unused_instrs.remove(ptr);
                        unused_instrs.remove(offset);
                        let rid = RegisterId::Temp { bid: *bid, iid: i };
                        let _unused = unused_instrs.insert(Operand::Register { rid, dtype: dtype.clone() });

                    }
                    Instruction::Load { ptr } => {
                        unused_instrs.remove(ptr);
                        let rid = RegisterId::Temp { bid: *bid, iid: i };
                        let inner = ptr.dtype();
                        let dtype = inner.get_pointer_inner().unwrap();
                        let _unused = unused_instrs.insert(Operand::Register { rid, dtype: dtype.clone() });
                    }
                    Instruction::TypeCast { value, target_dtype } => {
                        unused_instrs.remove(value);
                        let rid = RegisterId::Temp { bid: *bid, iid: i };
                        let _unused = unused_instrs.insert(Operand::Register { rid, dtype: target_dtype.clone() });

                    }
                    _ => {}
                }
            }
        }

        for (bid, vec) in &mut nops {
            let entry = some_or!(code.blocks.get_mut(&bid), panic!("must contain bid"));
            vec.reverse();
            for item in vec {
                entry.instructions.remove(*item);

            }
        }

        // remove unused computation value



        true
    }
}
