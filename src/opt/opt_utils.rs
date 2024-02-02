//! Utilities for implementing optimizations.
//!
//! You can add here utilities commonly used in the implementation of multiple optimizations.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::ir::*;
use crate::*;
use std::cmp::Ordering;

pub fn make_cfg(fdef: &FunctionDefinition) -> HashMap<BlockId, Vec<JumpArg>> {
    fdef.blocks
        .iter()
        .map(|(bid, block)| {
            let mut args = Vec::new();
            match &block.exit {
                BlockExit::Jump { arg } => args.push(arg.clone()),
                BlockExit::ConditionalJump {
                    arg_then, arg_else, ..
                } => {
                    args.push(arg_then.clone());
                    args.push(arg_else.clone());
                }
                BlockExit::Switch { default, cases, .. } => {
                    args.push(default.clone());
                    for (_, arg) in cases {
                        args.push(arg.clone());
                    }
                }
                _ => {}
            }
            (*bid, args)
        })
        .collect()
}

pub fn reverse_cfg(
    cfg: &HashMap<BlockId, Vec<JumpArg>>,
) -> HashMap<BlockId, Vec<(BlockId, JumpArg)>> {
    let mut result = HashMap::new();

    for (bid, jumps) in cfg {
        for jump in jumps {
            result
                .entry(jump.bid)
                .or_insert_with(Vec::new)
                .push((*bid, jump.clone()));
        }
    }
    result
}
pub fn replace_operands(operand: &mut Operand, hashmap: &HashMap<RegisterId, Operand>) {
    if let Some((regid, _)) = operand.get_register() {
        let replace_operand = some_or!(hashmap.get(regid), return);
        *operand = replace_operand.clone();
    }
}

struct PostOrder<'c> {
    visited: HashSet<BlockId>,
    cfg: &'c HashMap<BlockId, Vec<JumpArg>>,
    traversed: Vec<BlockId>,
}

impl<'c> PostOrder<'c> {
    fn traverse(&mut self, bid: BlockId) {
        for jump in self.cfg.get(&bid).unwrap() {
            if self.visited.insert(jump.bid) {
                self.traverse(jump.bid);
            }
        }
        self.traversed.push(bid);
    }
}

fn travese_postorder(bid_init: BlockId, cfg: &HashMap<BlockId, Vec<JumpArg>>) -> Vec<BlockId> {
    let mut post_order = PostOrder {
        visited: HashSet::new(),
        cfg,
        traversed: Vec::new(),
    };
    let _unused = post_order.visited.insert(bid_init);
    post_order.traverse(bid_init);
    post_order.traversed
}

#[derive(Debug)]
pub struct Domtree {
    idoms: HashMap<BlockId, BlockId>,
    frontiers: HashMap<BlockId, Vec<BlockId>>,
    reverse_post_order: Vec<BlockId>,
}

impl Domtree {
    pub fn new(
        bid_init: BlockId,
        cfg: &HashMap<BlockId, Vec<JumpArg>>,
        reverse_cfg: &HashMap<BlockId, Vec<(BlockId, JumpArg)>>,
    ) -> Self {
        let mut reverse_post_order = travese_postorder(bid_init, cfg);
        reverse_post_order.reverse();

        let inverse_reverse_post_order = reverse_post_order
            .iter()
            .enumerate()
            .map(|(i, bid)| (*bid, i))
            .collect::<HashMap<BlockId, usize>>();

        // The immediate dominator (idom) of each block.
        let mut idoms = HashMap::<BlockId, BlockId>::new();

        loop {
            let mut changed = false;
            for bid in &reverse_post_order {
                if *bid == bid_init {
                    continue;
                }

                let mut idom = None;
                for (bid_prev, _) in reverse_cfg.get(bid).unwrap() {
                    if *bid_prev == bid_init || idoms.get(bid_prev).is_some() {
                        idom = Some(intersect_idom(
                            idom,
                            *bid_prev,
                            &inverse_reverse_post_order,
                            &idoms,
                        ));
                    }
                }

                if let Some(idom) = idom {
                    let _unused = idoms
                        .entry(*bid)
                        .and_modify(|v| {
                            if *v != idom {
                                changed = true;
                                *v = idom;
                            }
                        })
                        .or_insert_with(|| {
                            changed = true;
                            idom
                        });
                }
            }
            if !changed {
                break;
            }
        }

        let mut frontiers = HashMap::new();
        for (bid, prevs) in reverse_cfg {
            if prevs.len() <= 1 {
                continue;
            }

            let idom = *some_or!(idoms.get(bid), continue);

            for (bid_prev, _) in prevs {
                let mut runner = *bid_prev;
                while !Self::dominates(&idoms, runner, *bid) {
                    frontiers.entry(runner).or_insert_with(Vec::new).push(*bid);
                    println!("runner: {}, bid: {}, idom: {}", runner, bid, idom);
                    runner = *idoms.get(&runner).unwrap();
                }
            }
        }

        Self {
            idoms,
            frontiers,
            reverse_post_order,
        }
    }

    pub fn idom(&self, bid: BlockId) -> Option<BlockId> {
        self.idoms.get(&bid).cloned()
    }

    pub fn dominates(idoms: &HashMap<BlockId, BlockId>, bid1: BlockId, mut bid2: BlockId) -> bool {
        loop {
            bid2 = *some_or!(idoms.get(&bid2), return false);
            if bid1 == bid2 {
                return true;
            }
        }
    }

    pub fn frontiers(&self, bid: BlockId) -> Option<&Vec<BlockId>> {
        self.frontiers.get(&bid)
    }

    pub fn walk<F>(&self, mut f: F)
    where
        F: FnMut(Option<BlockId>, BlockId),
    {
        for bid in &self.reverse_post_order {
            f(self.idoms.get(bid).cloned(), *bid);
        }
    }
}

fn intersect_idom(
    lhs: Option<BlockId>,
    mut rhs: BlockId,
    inverse_reverse_post_order: &HashMap<BlockId, usize>,
    idoms: &HashMap<BlockId, BlockId>,
) -> BlockId {
    let mut lhs = some_or!(lhs, return rhs);

    loop {
        if lhs == rhs {
            return lhs;
        }
        let lhs_index = inverse_reverse_post_order.get(&lhs).unwrap();
        let rhs_index = inverse_reverse_post_order.get(&rhs).unwrap();

        match lhs_index.cmp(rhs_index) {
            Ordering::Less => rhs = *idoms.get(&rhs).unwrap(),
            Ordering::Greater => lhs = *idoms.get(&lhs).unwrap(),
            Ordering::Equal => panic!("intersect_dom: lhs == rhs cannot happen"),
        }
    }
}
