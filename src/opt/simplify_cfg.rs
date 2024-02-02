use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use itertools::izip;

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::FunctionPass;
use crate::*;
pub type SimplifyCfg = FunctionPass<
    Repeat<(
        SimplifyCfgConstProp,
        (SimplifyCfgReach, (SimplifyCfgMerge, SimplifyCfgEmpty)),
    )>,
>;

/// Simplifies block exits by propagating constants.
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgConstProp {}

/// Retains only those blocks that are reachable from the init.
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgReach {}

/// Merges two blocks if a block is pointed to only by another
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgMerge {}

/// Removes empty blocks
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgEmpty {}

impl Optimize<FunctionDefinition> for SimplifyCfgConstProp {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        code.blocks
            .iter_mut()
            .map(|(_, block)| {
                if let Some(exit) = self.simplify_block_exit(&block.exit) {
                    block.exit = exit;
                    true
                } else {
                    false
                }
            })
            .any(|r| r)
    }
}

impl SimplifyCfgConstProp {
    fn simplify_block_exit(&self, exit: &BlockExit) -> Option<BlockExit> {
        match exit {
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                if arg_then == arg_else {
                    return Some(BlockExit::Jump {
                        arg: arg_then.clone(),
                    });
                }
                if let Some(c) = condition.get_constant() {
                    match c {
                        Constant::Int { value: 0, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_else.clone(),
                            })
                        }
                        Constant::Int { value: 1, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_then.clone(),
                            })
                        }
                        _ => {
                            panic!("condition should be bool")
                        }
                    }
                }
                None
            }
            BlockExit::Switch {
                value,
                default,
                cases,
            } => {
                if cases.iter().all(|(_, bid)| default == bid) {
                    return Some(BlockExit::Jump {
                        arg: default.clone(),
                    });
                }

                if let Some(v) = value.get_constant() {
                    return Some(BlockExit::Jump {
                        arg: if let Some((_, arg)) = cases.iter().find(|(c, _)| v == c) {
                            arg.clone()
                        } else {
                            default.clone()
                        },
                    });
                }

                None
            }
            _ => None,
        }
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgReach {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let graph = make_cfg(code);

        let mut queue = vec![code.bid_init];
        let mut visited = HashSet::new();
        let _unused = visited.insert(code.bid_init);
        while let Some(bid) = queue.pop() {
            if let Some(args) = graph.get(&bid) {
                for arg in args {
                    if visited.insert(arg.bid) {
                        queue.push(arg.bid);
                    }
                }
            }
        }

        let size_orig = code.blocks.len();
        code.blocks.retain(|bid, _| visited.contains(bid));
        code.blocks.len() < size_orig
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgMerge {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let graph = make_cfg(code);

        let mut indegrees = HashMap::<BlockId, usize>::new();
        for args in graph.values() {
            for arg in args {
                *indegrees.entry(arg.bid).or_insert(0) += 1;
            }
        }

        /*
                   let block_to = code.blocks.remove(&arg.bid).unwrap();
                   let bid_to = arg.bid;
                   let args_to = arg.args.clone();
                   let mut replaces = HashMap::new();

                   // Gather phinode replacements information
                   for (i, (a, p)) in izip!(&args_to, block_to.phinodes.iter()).enumerate() {
                       assert_eq!(a.dtype(), *p.deref());
                       let from = RegisterId::arg(bid_to, i);
                       replaces.insert(from, a.clone());
                   }


                   // Moves instructions
                   let len = block_from.instructions.len();
                   for (i, instr) in block_to.instructions.into_iter().enumerate() {
                       let dtype = instr.dtype();
                       block_from.instructions.push(instr);
                       let from = RegisterId::temp(arg.bid, i);
                       let to =
                           Operand::register(RegisterId::temp(*bid_from, len + i), dtype.clone());
                       replaces.insert(from, to);
                   }

                   // Moves block exit
                   block_from.exit = block_to.exit;

                   result = true;

        */

        let mut result = false;
        let mut from_to = Vec::<Vec<BlockId>>::new();
        let mut args = HashMap::new();
        for (bid_from, block_from) in &code.blocks {
            let mut is_added = false;
            if let BlockExit::Jump { arg } = &block_from.exit {
                if *bid_from != arg.bid && indegrees.get(&arg.bid) == Some(&1) {
                    for path in &mut from_to {
                        if path.last().unwrap() == bid_from {
                            let _unused = args.insert(arg.bid, arg.args.clone());
                            path.push(arg.bid);
                            is_added = true;
                            break;
                        }
                    }
                    if !is_added {
                        from_to.push(vec![*bid_from, arg.bid]);
                        let _unused = args.insert(arg.bid, arg.args.clone());
                    }
                }
            }
        }

        for path in &mut from_to {
            let mut bid_to = path.pop().unwrap();
            while let Some(bid_from) = path.pop() {
                let block_to = code.blocks.remove(&bid_to).unwrap();
                let block_from = code.blocks.get_mut(&bid_from).unwrap();
                let mut replaces = HashMap::new();
                let args_to = args.get(&bid_to).unwrap();
                // Gather phinode replacements information
                for (i, (a, p)) in izip!(args_to, block_to.phinodes.iter()).enumerate() {
                    assert_eq!(a.dtype(), *p.deref());
                    let from = RegisterId::arg(bid_to, i);
                    let _unused = replaces.insert(from, a.clone());
                }

                // Moves instructions
                let len = block_from.instructions.len();
                for (i, instr) in block_to.instructions.into_iter().enumerate() {
                    let dtype = instr.dtype();
                    block_from.instructions.push(instr);
                    let from = RegisterId::temp(bid_to, i);
                    let to = Operand::register(RegisterId::temp(bid_from, len + i), dtype.clone());
                    let _unused = replaces.insert(from, to);
                }
                // Moves block exit
                block_from.exit = block_to.exit;

                code.walk(|operand| replace_operands(operand, &replaces));
                bid_to = bid_from;
                result = true;
            }
        }
        result
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgEmpty {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let empty_blocks = code
            .blocks
            .iter()
            .filter(|(_, block)| block.phinodes.is_empty() && block.instructions.is_empty())
            .map(|(bid, block)| (*bid, block.clone()))
            .collect::<HashMap<_, _>>();

        code.blocks
            .iter_mut()
            .map(|(_, block)| self.simplify_block_exit(&mut block.exit, &empty_blocks))
            .any(|r| r)
    }
}

impl SimplifyCfgEmpty {
    fn simplify_jump_arg(&self, arg: &mut JumpArg, empty_blocks: &HashMap<BlockId, Block>) -> bool {
        let block = some_or!(empty_blocks.get(&arg.bid), return false);

        // An empty block has no phinodes
        assert!(arg.args.is_empty());

        if let BlockExit::Jump { arg: a } = &block.exit {
            *arg = a.clone();
            true
        } else {
            false
        }
    }

    fn simplify_block_exit(
        &self,
        exit: &mut BlockExit,
        empty_blocks: &HashMap<BlockId, Block>,
    ) -> bool {
        match exit {
            BlockExit::Jump { arg } => {
                let block = some_or!(empty_blocks.get(&arg.bid), return false);
                *exit = block.exit.clone();
                true
            }
            BlockExit::ConditionalJump {
                arg_then, arg_else, ..
            } => {
                let changed1 = self.simplify_jump_arg(arg_then, empty_blocks);
                let changed2 = self.simplify_jump_arg(arg_else, empty_blocks);
                changed1 || changed2
            }
            BlockExit::Switch { default, cases, .. } => {
                let result = self.simplify_jump_arg(default, empty_blocks);
                cases
                    .iter_mut()
                    .map(|(_, arg)| self.simplify_jump_arg(arg, empty_blocks))
                    .fold(result, |l, r| l || r)
            }
            BlockExit::Return { .. } | BlockExit::Unreachable => false,
        }
    }
}
