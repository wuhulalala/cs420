use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::{Deref, DerefMut};

use super::opt_utils::*;
use crate::ir::*;
use crate::opt::FunctionPass;
use crate::*;

pub type Mem2reg = FunctionPass<Mem2regInner>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum OperandVar {
    Operand(Operand),
    Phi((usize, BlockId)),
}

impl OperandVar {
    pub fn lookup(&self, dtype: Dtype, indexes: &HashMap<(usize, BlockId), usize>) -> Operand {
        match self {
            Self::Operand(operand) => operand.clone(),
            Self::Phi((aid, bid)) => {
                let index = some_or!(
                    indexes.get(&(*aid, *bid)),
                    return Operand::Constant(Constant::Undef { dtype })
                );
                let rid = RegisterId::Arg {
                    bid: *bid,
                    aid: *index,
                };
                Operand::register(rid, dtype)
            }
        }
    }
}
// struct JoinTable<'s> {
// inner: HashMap<(usize, BlockId), BlockId>,
// domtree: &'s Domtree,
// joins: &'s HashMap<usize, HashSet<BlockId>>,
// }

// impl<'s> JoinTable<'s> {
// pub fn new(domtree: &'s Domtree, joins: &'s HashMap<usize, HashSet<BlockId>>) -> Self {
// Self {
// inner: HashMap::new(),
// domtree,
// joins,
// }
// }

// pub fn lookup(&mut self, aid: usize, bid: BlockId) -> BlockId {
// let ret = if let Some(ret) = self.inner.get(&(aid, bid)) {
// *ret
// } else if self.joins.get(&aid).unwrap().contains(&bid) {
// bid
// } else {
// some_or!(self.domtree.idom(bid), bid)
// };

// let _unused = self.inner.insert((aid, bid), ret);

// ret
// }
// }

#[inline]
fn mark_inpromotable(inpromotable: &mut HashSet<usize>, operand: &Operand) {
    let (rid, _) = some_or!(operand.get_register(), return);
    if let RegisterId::Local { aid } = rid {
        let _unused = inpromotable.insert(*aid);
    }
}
#[derive(Default, Clone, Copy, Debug)]
pub struct Mem2regInner {}

impl Optimize<FunctionDefinition> for Mem2regInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        // collect inpromotable local memory allocations and stores.

        // A local allocation is promotable only if it is used only as the pointer of
        // store/load instructions
        let mut inpromotable = HashSet::new();

        // Stores to each promotable local allocations.
        let mut stores = HashMap::<usize, Vec<BlockId>>::new();

        for (bid, block) in &code.blocks {
            for instr in &block.instructions {
                match instr.deref() {
                    Instruction::Nop => {}
                    Instruction::BinOp { lhs, rhs, .. } => {
                        mark_inpromotable(&mut inpromotable, lhs);
                        mark_inpromotable(&mut inpromotable, rhs);
                    }
                    Instruction::UnaryOp { operand, .. } => {
                        mark_inpromotable(&mut inpromotable, operand);
                    }
                    Instruction::Store { ptr, value } => {
                        mark_inpromotable(&mut inpromotable, value);

                        let (rid, dtype) = some_or!(ptr.get_register(), continue);
                        if let Dtype::Struct { .. } = dtype.get_pointer_inner().unwrap() {
                            let (rid, _) = some_or!(value.get_register(), continue);
                            if let RegisterId::Arg { aid, .. } = rid {
                                stores.entry(*aid).or_insert_with(Vec::new).push(*bid);
                                continue;
                            }
                            mark_inpromotable(&mut inpromotable, ptr);
                            continue;
                        }
                        if let RegisterId::Local { aid } = rid {
                            stores.entry(*aid).or_insert_with(Vec::new).push(*bid);
                        }
                    }
                    Instruction::Load { .. } => {}
                    Instruction::Call { callee, args, .. } => {
                        mark_inpromotable(&mut inpromotable, callee);
                        for arg in args {
                            mark_inpromotable(&mut inpromotable, arg);
                        }
                    }
                    Instruction::TypeCast { value, .. } => {
                        mark_inpromotable(&mut inpromotable, value);
                    }
                    Instruction::GetElementPtr { ptr, offset, .. } => {
                        mark_inpromotable(&mut inpromotable, offset);
                        let (_rid, dtype) = some_or!(ptr.get_register(), continue);
                        if let Dtype::Struct { .. } = dtype.get_pointer_inner().unwrap() {
                            mark_inpromotable(&mut inpromotable, ptr);
                            continue;
                        }
                    }
                }
            }
        }
        // If no local allocations are promotable, bail out.
        if (0..code.allocations.len()).all(|i| inpromotable.contains(&i)) {
            return false;
        }

        // Draws CFG, reverse CFG, and dominator tree
        let cfg = make_cfg(code);
        let reverse_cfg = reverse_cfg(&cfg);
        let domtree = Domtree::new(code.bid_init, &cfg, &reverse_cfg);

        // Calculates the join blocks with which a phinode may be inserted for each promotable
        // location.
        let joins: HashMap<usize, HashSet<BlockId>> = stores
            .iter()
            .filter(|(aid, _)| !inpromotable.contains(*aid))
            .map(|(aid, bids)| {
                (*aid, {
                    let mut stack = bids.clone();
                    let mut visited = HashSet::new();
                    while let Some(bid) = stack.pop() {
                        let bid_frontiers = some_or!(domtree.frontiers(bid), continue);
                        for bid_frontier in bid_frontiers {
                            if visited.insert(*bid_frontier) {
                                stack.push(*bid_frontier);
                            }
                        }
                    }
                    visited
                })
            })
            .collect();

        // Table for the nearest join block according to the dominator tree.
        // let mut _join_table = JoinTable::new(&domtree, &joins);

        // Repacement dictionary
        let mut replaces = HashMap::<RegisterId, OperandVar>::new();

        // Phinodes to be inserted. if `(aid, bid)` is in this set, then a phinode for `aid` should
        // be the value at the beginning of `bid`
        let mut phinode_indexes = HashSet::<(usize, BlockId)>::new();

        // The values stored in local allocations at the end of each block. If `(aid, bid) |-> X`,
        // then the value stored in `aid` at the end of `bid` is `X`.
        let mut end_values = HashMap::<(usize, BlockId), OperandVar>::new();

        for (bid, block) in &code.blocks {
            for (i, instr) in block.instructions.iter().enumerate() {
                match instr.deref() {
                    Instruction::Store { ptr, value } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }
                            let _unused =
                                end_values.insert((*aid, *bid), OperandVar::Operand(value.clone()));
                        }
                    }
                    Instruction::Load { ptr } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }
                            let mut cur_bid = *bid;
                            loop {
                                let end_value_join = end_values.get(&(*aid, cur_bid)).cloned();
                                if let Some(var) = end_value_join {
                                    let _unused = end_values
                                        .entry((*aid, *bid))
                                        .and_modify(|e| *e = var.clone())
                                        .or_insert(var.clone());
                                    let result =
                                        replaces.insert(RegisterId::temp(*bid, i), var.clone());
                                    assert_eq!(result, None);
                                    break;
                                } else if joins.get(aid).unwrap().contains(&cur_bid) {
                                    let var = end_values.entry((*aid, *bid)).or_insert_with(|| {
                                        end_value_join.unwrap_or_else(|| {
                                            let _unused = phinode_indexes.insert((*aid, cur_bid));
                                            OperandVar::Phi((*aid, cur_bid))
                                        })
                                    });
                                    let result =
                                        replaces.insert(RegisterId::temp(*bid, i), var.clone());
                                    assert_eq!(result, None);
                                    break;
                                } else {
                                    cur_bid = some_or!(domtree.idom(cur_bid), {
                                        let var =
                                            end_values.entry((*aid, *bid)).or_insert_with(|| {
                                                end_value_join.unwrap_or_else(|| {
                                                    let _unused =
                                                        phinode_indexes.insert((*aid, cur_bid));
                                                    OperandVar::Phi((*aid, cur_bid))
                                                })
                                            });
                                        let result =
                                            replaces.insert(RegisterId::temp(*bid, i), var.clone());
                                        assert_eq!(result, None);
                                        break;
                                    });
                                }
                            }
                            // let bid_join = join_table.lookup(*aid, *bid);
                            // let end_value_join = end_values.get(&(*aid, bid_join)).cloned();
                            // let var = end_values.entry((*aid, *bid)).or_insert_with(|| {
                            // end_value_join.unwrap_or_else(|| {
                            // let _unused = phinode_indexes.insert((*aid, bid_join));
                            // OperandVar::Phi((*aid, bid_join))
                            // })
                            // });
                            // let result = replaces.insert(RegisterId::temp(*bid, i), var.clone());
                            // assert_eq!(result, None);
                        }
                    }
                    _ => {}
                }
            }
        }

        // Generates phinodes recursively
        let mut phinode_visited = phinode_indexes;
        let mut phinode_stack = phinode_visited.iter().cloned().collect::<Vec<_>>();
        let mut phinodes =
            BTreeMap::<(usize, BlockId), (Dtype, HashMap<BlockId, OperandVar>)>::new();
        while let Some((aid, bid)) = phinode_stack.pop() {
            let mut cases = HashMap::new();
            let prevs = some_or!(reverse_cfg.get(&bid), continue);
            for (bid_prev, _) in prevs {
                let mut cur_bid = *bid_prev;
                loop {
                    let end_value = end_values.get(&(aid, cur_bid));
                    if let Some(var) = end_value {
                        let _unused = cases.insert(*bid_prev, var.clone());
                        break;
                    } else if joins.get(&aid).unwrap().contains(&cur_bid) {
                        if phinode_visited.insert((aid, cur_bid)) {
                            phinode_stack.push((aid, cur_bid));
                        }
                        let end_value = OperandVar::Phi((aid, cur_bid));
                        let _unused = cases.insert(*bid_prev, end_value);
                        break;
                    } else {
                        cur_bid = some_or!(domtree.idom(cur_bid), {
                            if phinode_visited.insert((aid, cur_bid)) {
                                phinode_stack.push((aid, cur_bid));
                            }
                            let end_value = OperandVar::Phi((aid, cur_bid));
                            let _unused = cases.insert(*bid_prev, end_value);
                            break;
                        })
                    }
                }
                // let end_value = end_values.get(&var_prev).cloned().unwrap_or_else(|| {
                // let bid_prev_phinode = join_table.lookup(aid, *bid_prev);
                // let var_prev_phinode = (aid, bid_prev_phinode);
                // if phinode_visited.insert(var_prev_phinode) {
                // phinode_stack.push(var_prev_phinode);
                // }
                // OperandVar::Phi(var_prev_phinode)
                // });
                // let _unused = cases.insert(*bid_prev, end_value);
            }

            let _unused = phinodes.insert(
                (aid, bid),
                (code.allocations.get(aid).unwrap().deref().clone(), cases),
            );
        }

        // The phinodes indexes for promoted allocations in each block
        let mut phinode_indexes = HashMap::<(usize, BlockId), usize>::new();

        // Inserts phinodes.
        for ((aid, bid), (dtype, _)) in &phinodes {
            let name = code.allocations.get(*aid).unwrap().name();
            let block = code.blocks.get_mut(bid).unwrap();
            let index = block.phinodes.len();
            block
                .phinodes
                .push(Named::new(name.cloned(), dtype.clone()));
            let _unused = phinode_indexes.insert((*aid, *bid), index);
        }

        // Insert phinode arguments
        for ((aid, bid), (dtype, phinode)) in &phinodes {
            let index = *phinode_indexes.get(&(*aid, *bid)).unwrap();
            for (bid_prev, operand_prev) in phinode {
                let block_prev = code.blocks.get_mut(bid_prev).unwrap();
                let operand_prev = operand_prev.lookup(dtype.clone(), &phinode_indexes);
                block_prev.exit.walk_jump_args(|arg| {
                    if &arg.bid == bid {
                        assert_eq!(arg.args.len(), index);
                        arg.args.push(operand_prev.clone());
                    }
                });
            }
        }

        // Replaces the values loaded from promotable allocations.
        code.walk(|operand| {
            let (rid, dtype) = some_or!(operand.get_register(), return);
            let mut operand_var = some_or!(replaces.get(rid), return);
            operand_var = loop {
                if let OperandVar::Operand(operand) = operand_var {
                    if let Some((rid, _)) = operand.get_register() {
                        operand_var = some_or!(replaces.get(rid), break operand_var);
                        continue;
                    } else {
                        break operand_var;
                    }
                } else {
                    break operand_var;
                }
            };
            *operand = operand_var.lookup(dtype.clone(), &phinode_indexes);
        });

        // Remove store/load instructions
        for block in code.blocks.values_mut() {
            for instr in block.instructions.iter_mut() {
                match instr.deref().deref() {
                    Instruction::Store { ptr, .. } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *instr.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    Instruction::Load { ptr } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *instr.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        true
    }
}
