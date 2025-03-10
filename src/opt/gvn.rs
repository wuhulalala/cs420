use std::{collections::HashMap, ops::Deref};

use super::opt_utils::{make_cfg, reverse_cfg, travese_postorder, Domtree};
use crate::ir::*;
use crate::opt::FunctionPass;
use crate::*;
use lang_c::ast;
use rand::Error;

pub type Gvn = FunctionPass<GvnInner>;

#[derive(Clone, PartialEq, Eq)]
enum OperandVar {
    Operand(Operand),
    Phi((Num, BlockId)),
}
impl OperandVar {
    pub fn lookup(&self, dtype: Dtype, indexes: &HashMap<(Num, BlockId), usize>) -> Operand {
        match self {
            Self::Operand(operand) => operand.clone(),
            Self::Phi((num, bid)) => {
                let index = some_or!(
                    indexes.get(&(num.clone(), *bid)),
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

#[derive(PartialEq, Eq, Clone, Hash)]
enum Num {
    Integer(usize),
    Constant(Constant),
}

impl Num {
    fn get_constant(&self) -> Option<Constant> {
        if let Num::Constant(constant) = self {
            Some(constant.clone())
        } else {
            None
        }
    }

    // fn get_integer(&self) -> Option<usize> {
        // if let Num::Integer(int) = self {
            // Some(*int)
        // } else {
            // None
        // }
    // }
}
#[derive(PartialEq, Eq, Clone, Hash)]
enum Expr {
    BinOp {
        op: ast::BinaryOperator,
        lhs: Num,
        rhs: Num,
        dtype: Dtype,
    },
    UnaryOp {
        op: ast::UnaryOperator,
        operand: Num,
        dtype: Dtype,
    },
    TypeCast {
        value: Num,
        target_dtype: Dtype,
    },
    GetElementPtr {
        ptr: Num,
        offset: Num,
        dtype: Dtype,
    },
}

#[derive(Default, Clone, Copy, Debug)]
pub struct GvnInner {}

impl Optimize<FunctionDefinition> for GvnInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        // Draws CFG, reverse CFG, and dominator tree
        let cfg = make_cfg(code);
        let reverse_cfg = reverse_cfg(&cfg);
        let domtree = Domtree::new(code.bid_init, &cfg, &reverse_cfg);

        let mut reverse_post_order = travese_postorder(code.bid_init, &cfg);
        reverse_post_order.reverse();

        let mut register_table = HashMap::<Operand, Num>::new();
        let mut expr_table = HashMap::<Expr, Num>::new();
        let mut leader_tables = HashMap::<BlockId, HashMap<Num, OperandVar>>::new();

        let mut replaces = HashMap::<Operand, OperandVar>::new();

        let mut phinodes = HashMap::<(BlockId, Num), (Dtype, OperandVar)>::new();
        let mut global_count: usize = 0;
        for cur_bid in reverse_post_order {
            for (bid, block) in &code.blocks {
                if cur_bid == *bid {
                    let mut ld_table = if let Some(idom) = domtree.idom(cur_bid) {
                        (*(leader_tables.get(&idom).unwrap())).clone()
                    } else {
                        HashMap::<Num, OperandVar>::new()
                    };
                    // Initialize phinode
                    for (index, phinode) in block.phinodes.iter().enumerate() {
                        let temp_re_table = register_table.clone();
                        let prevs = some_or!(reverse_cfg.get(&cur_bid), {
                            let rid = RegisterId::Arg {
                                bid: cur_bid,
                                aid: index,
                            };
                            let _unused = register_table
                                .entry(Operand::register(rid, phinode.clone().into_inner()))
                                .or_insert(Num::Integer(global_count));
                            global_count += 1;
                            continue;
                        });
                        let args = prevs
                            .iter()
                            .map(|(_, arg)| temp_re_table.get(arg.args.get(index).unwrap()))
                            .collect::<Vec<_>>();
                        if args.iter().all(|e| e.is_some())
                            && args
                                .iter()
                                .map(|e| e.unwrap())
                                .all(|e| e == args.get(0).unwrap().unwrap())
                        {
                            let rid = RegisterId::Arg {
                                bid: cur_bid,
                                aid: index,
                            };
                            let operand = Operand::register(rid, phinode.clone().into_inner());
                            let num = args.get(0).unwrap().unwrap().clone();
                            let _unused =
                                register_table.entry(operand.clone()).or_insert(num.clone());

                            if num.get_constant().is_some() {
                                let constant = num.get_constant().unwrap().clone();
                                let _unused = replaces.insert(
                                    operand.clone(),
                                    OperandVar::Operand(Operand::constant(constant)),
                                );
                            }
                        } else {
                            let rid = RegisterId::Arg {
                                bid: cur_bid,
                                aid: index,
                            };
                            let _unused = register_table
                                .entry(Operand::register(rid, phinode.clone().into_inner()))
                                .or_insert(Num::Integer(global_count));
                            global_count += 1;
                        }
                    }

                    // process the instructions
                    for (i, instr) in block.instructions.iter().enumerate() {
                        match instr.deref() {
                            Instruction::BinOp {
                                op,
                                lhs,
                                rhs,
                                dtype,
                            } => {
                                let lhs = trans_to_num(lhs, &register_table);
                                let rhs = trans_to_num(rhs, &register_table);
                                let expr = Expr::BinOp {
                                    op: op.clone(),
                                    lhs,
                                    rhs,
                                    dtype: dtype.clone(),
                                };

                                let rid = RegisterId::Temp {
                                    bid: cur_bid,
                                    iid: i,
                                };
                                let operand = Operand::register(rid, dtype.clone());
                                let _unused = process_instr(
                                    &mut register_table,
                                    &mut ld_table,
                                    &mut leader_tables,
                                    &mut expr_table,
                                    &mut replaces,
                                    &mut phinodes,
                                    expr,
                                    &operand,
                                    &mut global_count,
                                    &reverse_cfg,
                                    dtype,
                                    cur_bid,
                                    code.bid_init,
                                );
                            }
                            Instruction::UnaryOp { op, operand, dtype } => {
                                let operand = trans_to_num(operand, &register_table);
                                let expr = Expr::UnaryOp {
                                    op: op.clone(),
                                    operand,
                                    dtype: dtype.clone(),
                                };
                                let rid = RegisterId::Temp {
                                    bid: cur_bid,
                                    iid: i,
                                };
                                let operand = Operand::register(rid, dtype.clone());
                                let _unused = process_instr(
                                    &mut register_table,
                                    &mut ld_table,
                                    &mut leader_tables,
                                    &mut expr_table,
                                    &mut replaces,
                                    &mut phinodes,
                                    expr,
                                    &operand,
                                    &mut global_count,
                                    &reverse_cfg,
                                    dtype,
                                    cur_bid,
                                    code.bid_init,
                                );
                            }
                            Instruction::TypeCast {
                                value,
                                target_dtype,
                            } => {
                                let value = trans_to_num(value, &register_table);
                                let expr = Expr::TypeCast {
                                    value,
                                    target_dtype: target_dtype.clone(),
                                };

                                let rid = RegisterId::Temp {
                                    bid: cur_bid,
                                    iid: i,
                                };
                                let operand = Operand::register(rid, target_dtype.clone());
                                let _unused = process_instr(
                                    &mut register_table,
                                    &mut ld_table,
                                    &mut leader_tables,
                                    &mut expr_table,
                                    &mut replaces,
                                    &mut phinodes,
                                    expr,
                                    &operand,
                                    &mut global_count,
                                    &reverse_cfg,
                                    target_dtype,
                                    cur_bid,
                                    code.bid_init,
                                );
                            }

                            Instruction::GetElementPtr { ptr, offset, dtype } => {
                                let ptr = some_or!(register_table.get(ptr), {
                                    let _unused = register_table
                                        .insert(ptr.clone(), Num::Integer(global_count));
                                    global_count += 1;
                                    register_table.get(ptr).unwrap()
                                });

                                let offset = trans_to_num(offset, &register_table);
                                let expr = Expr::GetElementPtr {
                                    ptr: ptr.clone(),
                                    offset,
                                    dtype: dtype.clone(),
                                };
                                let rid = RegisterId::Temp {
                                    bid: cur_bid,
                                    iid: i,
                                };
                                let operand = Operand::register(rid, dtype.clone());
                                let _unused = process_instr(
                                    &mut register_table,
                                    &mut ld_table,
                                    &mut leader_tables,
                                    &mut expr_table,
                                    &mut replaces,
                                    &mut phinodes,
                                    expr,
                                    &operand,
                                    &mut global_count,
                                    &reverse_cfg,
                                    dtype,
                                    cur_bid,
                                    code.bid_init,
                                );
                            }
                            Instruction::Call {
                                return_type: dtype, ..
                            } => {
                                let rid = RegisterId::Temp {
                                    bid: cur_bid,
                                    iid: i,
                                };
                                let operand = Operand::register(rid, dtype.clone());
                                let _unused = register_table
                                    .insert(operand.clone(), Num::Integer(global_count));
                                let _unused = ld_table.insert(
                                    Num::Integer(global_count),
                                    OperandVar::Operand(operand),
                                );
                                global_count += 1;
                            }
                            Instruction::Load { ptr } => {
                                let rid = RegisterId::Temp {
                                    bid: cur_bid,
                                    iid: i,
                                };
                                let operand = Operand::register(
                                    rid,
                                    ptr.dtype().get_pointer_inner().unwrap().clone(),
                                );
                                let _unused = register_table
                                    .insert(operand.clone(), Num::Integer(global_count));
                                let _unused = ld_table.insert(
                                    Num::Integer(global_count),
                                    OperandVar::Operand(operand),
                                );
                                global_count += 1;
                            }
                            _ => {}
                        }
                    }

                    // process block exit
                    match &block.exit {
                        BlockExit::Jump { arg } => {
                            for arg in &arg.args {
                                if arg.get_constant().is_some() {
                                    let _unused = register_table.insert(
                                        arg.clone(),
                                        Num::Constant(arg.get_constant().unwrap().clone()),
                                    );
                                }
                            }
                        }
                        BlockExit::ConditionalJump {
                            arg_then, arg_else, ..
                        } => {
                            for arg in &arg_else.args {
                                if arg.get_constant().is_some() {
                                    let _unused = register_table.insert(
                                        arg.clone(),
                                        Num::Constant(arg.get_constant().unwrap().clone()),
                                    );
                                }
                            }
                            for arg in &arg_then.args {
                                if arg.get_constant().is_some() {
                                    let _unused = register_table.insert(
                                        arg.clone(),
                                        Num::Constant(arg.get_constant().unwrap().clone()),
                                    );
                                }
                            }
                        }
                        BlockExit::Switch { default, cases, .. } => {
                            for arg in &default.args {
                                if arg.get_constant().is_some() {
                                    let _unused = register_table.insert(
                                        arg.clone(),
                                        Num::Constant(arg.get_constant().unwrap().clone()),
                                    );
                                }
                            }
                            for (_, case) in cases {
                                for arg in &case.args {
                                    if arg.get_constant().is_some() {
                                        let _unused = register_table.insert(
                                            arg.clone(),
                                            Num::Constant(arg.get_constant().unwrap().clone()),
                                        );
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                    let _unused = leader_tables.entry(cur_bid).or_insert(ld_table);
                    break;
                }
            }
        }

        let mut phinodes_indexes = HashMap::<(Num, BlockId), usize>::new();

        for ((bid, num), (dtype, _)) in &phinodes {
            let block = code.blocks.get_mut(bid).unwrap();
            let index = block.phinodes.len();
            block.phinodes.push(Named::new(None, dtype.clone()));
            let prevs = reverse_cfg.get(bid).unwrap();
            for (prev_bid, _) in prevs.iter() {
                let block = code.blocks.get_mut(prev_bid).unwrap();
                let ld_table = leader_tables.get(prev_bid).unwrap();
                let operand_prev = ld_table.get(num).unwrap().clone();
                let operand_prev = operand_prev.lookup(dtype.clone(), &phinodes_indexes);
                block.exit.walk_jump_args(|arg| {
                    if &arg.bid == bid {
                        arg.args.push(operand_prev.clone());
                    }
                })
            }
            let _unused = phinodes_indexes.insert((num.clone(), *bid), index);
        }
        // Replaces the values loaded from promotable allocations.
        code.walk(|operand| {
            let (_, dtype) = some_or!(operand.get_register(), return);
            let mut operand_var = some_or!(replaces.get(operand), return);
            operand_var = loop {
                if let OperandVar::Operand(operand) = operand_var {
                    if let Some(_) = operand.get_register() {
                        operand_var = some_or!(replaces.get(operand), break operand_var);
                        continue;
                    } else {
                        break operand_var;
                    }
                } else {
                    break operand_var;
                }
            };
            *operand = operand_var.lookup(dtype.clone(), &phinodes_indexes);
        });
        true
    }
}

fn trans_to_num(operand: &Operand, reg_table: &HashMap<Operand, Num>) -> Num {
    if let Some(_) = operand.get_register() {
        reg_table.get(operand).unwrap().clone()
    } else {
        Num::Constant(operand.get_constant().unwrap().clone())
    }
}

fn process_expr(
    reg_table: &mut HashMap<Operand, Num>,
    expr_table: &mut HashMap<Expr, Num>,
    expr: Expr,
    operand: &Operand,
    global_count: &mut usize,
) -> Result<(), Error> {
    if expr_table.contains_key(&expr) {
        let num = expr_table.get(&expr).unwrap();
        let _unused = reg_table.entry(operand.clone()).or_insert(num.clone());
    } else {
        let _unused = expr_table
            .entry(expr)
            .or_insert(Num::Integer(*global_count));

        let _unused = reg_table
            .entry(operand.clone())
            .or_insert(Num::Integer(*global_count));
        *global_count += 1;
    }

    Ok(())
}

fn process_instr(
    register_table: &mut HashMap<Operand, Num>,
    ld_table: &mut HashMap<Num, OperandVar>,
    leader_tables: &mut HashMap<BlockId, HashMap<Num, OperandVar>>,
    expr_table: &mut HashMap<Expr, Num>,
    replaces: &mut HashMap<Operand, OperandVar>,
    phinodes_indexes: &mut HashMap<(BlockId, Num), (Dtype, OperandVar)>,
    expr: Expr,
    operand: &Operand,
    global_count: &mut usize,
    reverse_cfg: &HashMap<BlockId, Vec<(BlockId, JumpArg)>>,
    dtype: &Dtype,
    cur_bid: BlockId,
    init_bid: BlockId,
) -> Result<(), Error> {
    let _unused = process_expr(register_table, expr_table, expr, &operand, global_count);

    let num = register_table.get(&operand).unwrap();
    if ld_table.contains_key(num) {
        let _unused = replaces.insert(operand.clone(), ld_table.get(num).unwrap().clone());
    } else {
        if cur_bid == init_bid {
            let _unused = ld_table.insert(num.clone(), OperandVar::Operand(operand.clone()));
            return Ok(());
        }
        let prevs = reverse_cfg.get(&cur_bid).unwrap();
        let all_contain = prevs
            .iter()
            .all(|(prev_bid, _)| leader_tables.get(prev_bid).is_some())
            && prevs
                .iter()
                .all(|(prev_bid, _)| leader_tables.get(prev_bid).unwrap().contains_key(num));

        if all_contain && prevs.len() > 1 {
            let phinode = phinodes_indexes
                .entry((cur_bid, num.clone()))
                .or_insert((dtype.clone(), OperandVar::Phi((num.clone(), cur_bid))));

            let _unused = ld_table.insert(num.clone(), phinode.1.clone());

            let _unused = replaces.insert(operand.clone(), phinode.1.clone());
        } else {
            let _unused = ld_table.insert(num.clone(), OperandVar::Operand(operand.clone()));
        }
    }

    Ok(())
}
