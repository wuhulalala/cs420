//! # Homework: IR Generation
//!
//! The goal of this homework is to translate the components of a C file into KECC IR. While doing
//! so, you will familarize yourself with the structure of KECC IR, and understand the semantics of
//! C in terms of KECC.
//!
//! We highly recommend checking out the [slides][slides] and [github repo][github-qna-irgen] for
//! useful information.
//!
//! ## Guide
//!
//! ### High Level Guide
//!
//! Please watch the following video from 2020 along the lecture slides.
//! - [Intermediate Representation][ir]
//! - [IRgen (Overview)][irgen-overview]
//!
//! ### Coding Guide
//!
//! We highly recommend you copy-and-paste the code given in the following lecture videos from 2020:
//! - [IRgen (Code, Variable Declaration)][irgen-var-decl]
//! - [IRgen (Code, Function Definition)][irgen-func-def]
//! - [IRgen (Code, Statement 1)][irgen-stmt-1]
//! - [IRgen (Code, Statement 2)][irgen-stmt-2]
//!
//! The skeleton code roughly consists of the code for the first two videos, but you should still
//! watch them to have an idea of what the code is like.
//!
//! [slides]: https://docs.google.com/presentation/d/1SqtU-Cn60Sd1jkbO0OSsRYKPMIkul0eZoYG9KpMugFE/edit?usp=sharing
//! [ir]: https://youtu.be/7CY_lX5ZroI
//! [irgen-overview]: https://youtu.be/YPtnXlKDSYo
//! [irgen-var-decl]: https://youtu.be/HjARCUoK08s
//! [irgen-func-def]: https://youtu.be/Rszt9x0Xu_0
//! [irgen-stmt-1]: https://youtu.be/jFahkyxm994
//! [irgen-stmt-2]: https://youtu.be/UkaXaNw462U
//! [github-qna-irgen]: https://github.com/kaist-cp/cs420/labels/homework%20-%20irgen
#![allow(dead_code)]
use core::convert::TryFrom;
use core::fmt;
use core::mem;
use core::panic;
use std::collections::{BTreeMap, HashMap};
use std::ops::Deref;

use lang_c::ast::*;
use lang_c::driver::Parse;
use lang_c::span::Node;
use ordered_float::OrderedFloat;
use thiserror::Error;
use std::cmp::max;

use crate::ir::{DtypeError, HasDtype, Named};
use crate::*;

use itertools::izip;

use self::write_base::WriteString;

#[derive(Debug)]
pub struct IrgenError {
    pub code: String,
    pub message: IrgenErrorMessage,
}

impl IrgenError {
    pub fn new(code: String, message: IrgenErrorMessage) -> Self {
        Self { code, message }
    }
}

impl fmt::Display for IrgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\r\n\r\ncode: {}", self.message, self.code)
    }
}

#[derive(Debug, PartialEq, Eq, Error)]
pub enum IrgenErrorMessage {
    /// For uncommon error
    #[error("{message}")]
    Misc { message: String },
    #[error("called object `{callee:?}` is not a function or function pointer")]
    NeedFunctionOrFunctionPointer { callee: ir::Operand },
    #[error("redefinition, `{name}`")]
    Redefinition { name: String },
    #[error("`{dtype}` conflicts prototype's dtype, `{protorype_dtype}`")]
    ConflictingDtype {
        dtype: ir::Dtype,
        protorype_dtype: ir::Dtype,
    },
    #[error("{dtype_error}")]
    InvalidDtype { dtype_error: DtypeError },
    #[error("l-value required as {message}")]
    RequireLvalue { message: String },
}

#[derive(Default, Debug)]
pub struct Irgen {
    decls: BTreeMap<String, ir::Declaration>,
    typedefs: HashMap<String, ir::Dtype>,
    structs: HashMap<String, Option<ir::Dtype>>,
    struct_tempid_counter: usize,
}

impl Translate<Parse> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &Parse) -> Result<Self::Target, Self::Error> {
        self.translate(&source.unit)
    }
}

impl Translate<TranslationUnit> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &TranslationUnit) -> Result<Self::Target, Self::Error> {
        for ext_decl in &source.0 {
            match ext_decl.node {
                ExternalDeclaration::Declaration(ref var) => {
                    self.add_declaration(&var.node)?;
                }
                ExternalDeclaration::StaticAssert(_) => {
                    panic!("ExternalDeclaration::StaticAssert is unsupported")
                }
                ExternalDeclaration::FunctionDefinition(ref func) => {
                    self.add_function_definition(&func.node)?;
                }
            }
        }

        let decls = mem::take(&mut self.decls);
        let structs = mem::take(&mut self.structs);
        Ok(Self::Target { decls, structs })
    }
}

impl Irgen {
    const BID_INIT: ir::BlockId = ir::BlockId(0);
    // `0` is used to create `BID_INIT`
    const BID_COUNTER_INIT: usize = 1;
    const TEMPID_COUNTER_INIT: usize = 0;

    /// Add a declaration. It can be either a struct, typedef, or a variable.
    fn add_declaration(&mut self, source: &Declaration) -> Result<(), IrgenError> {
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&source.specifiers).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
        let base_dtype = base_dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("{source:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        let base_dtype = if let ir::Dtype::Struct { name, fields, .. } = &base_dtype {
            if let Some(name) = name {
                let _ = self.structs.entry(name.to_string()).or_insert(None);
            }

            if fields.is_some() {
                base_dtype
                    .resolve_structs(&mut self.structs, &mut self.struct_tempid_counter)
                    .map_err(|e| {
                        IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::InvalidDtype { dtype_error: e },
                        )
                    })?
            } else {
                base_dtype
            }
        } else {
            base_dtype
        };

        for init_decl in &source.declarators {
            let declarator = &init_decl.node.declarator.node;
            let name = name_of_declarator(declarator);
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| {
                    IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::InvalidDtype { dtype_error: e },
                    )
                })?
                .deref()
                .clone();
            let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
            if !is_typedef && is_invalid_structure(&dtype, &self.structs) {
                return Err(IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::Misc {
                        message: "incomplete struct type".to_string(),
                    },
                ));
            }

            if is_typedef {
                // Add new typedef if nothing has been declared before
                let prev_dtype = self
                    .typedefs
                    .entry(name.clone())
                    .or_insert_with(|| dtype.clone());

                if prev_dtype != &dtype {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::ConflictingDtype {
                            dtype,
                            protorype_dtype: prev_dtype.clone(),
                        },
                    ));
                }

                continue;
            }

            // Creates a new declaration based on the dtype.
            let mut decl = ir::Declaration::try_from(dtype.clone()).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;

            // If `initializer` exists, convert initializer to a constant value
            if let Some(initializer) = init_decl.node.initializer.as_ref() {
                if !is_valid_initializer(&initializer.node, &dtype, &self.structs) {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::Misc {
                            message: "initializer is not valid".to_string(),
                        },
                    ));
                }

                match &mut decl {
                    ir::Declaration::Variable {
                        initializer: var_initializer,
                        ..
                    } => {
                        if var_initializer.is_some() {
                            return Err(IrgenError::new(
                                format!("{source:#?}"),
                                IrgenErrorMessage::Redefinition { name },
                            ));
                        }
                        *var_initializer = Some(initializer.node.clone());
                    }
                    ir::Declaration::Function { .. } => {
                        return Err(IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::Misc {
                                message: "illegal initializer (only variables can be initialized)"
                                    .to_string(),
                            },
                        ));
                    }
                }
            }

            self.add_decl(&name, decl)?;
        }

        Ok(())
    }

    /// Add a function definition.
    fn add_function_definition(&mut self, source: &FunctionDefinition) -> Result<(), IrgenError> {
        // Creates name and signature.
        let specifiers = &source.specifiers;
        let declarator = &source.declarator.node;

        let name = name_of_declarator(declarator);
        let name_of_params = name_of_params_from_function_declarator(declarator)
            .expect("declarator is not from function definition");

        let (base_dtype, is_typedef) = ir::Dtype::try_from_ast_declaration_specifiers(specifiers)
            .map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        if is_typedef {
            return Err(IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::Misc {
                    message: "function definition declared typedef".into(),
                },
            ));
        }

        let dtype = base_dtype
            .with_ast_declarator(declarator)
            .map_err(|e| {
                IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?
            .deref()
            .clone();
        let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        let signature = ir::FunctionSignature::new(dtype.clone());

        // Adds new declaration if nothing has been declared before
        let decl = ir::Declaration::try_from(dtype).unwrap();
        self.add_decl(&name, decl)?;

        // Prepare scope for global variable
        let global_scope: HashMap<_, _> = self
            .decls
            .iter()
            .map(|(name, decl)| {
                let dtype = decl.dtype();
                let pointer = ir::Constant::global_variable(name.clone(), dtype);
                let operand = ir::Operand::constant(pointer);
                (name.clone(), operand)
            })
            .collect();

        // Prepares for irgen pass.
        let mut irgen = IrgenFunc {
            return_type: signature.ret.clone(),
            bid_init: Irgen::BID_INIT,
            phinodes_init: Vec::new(),
            allocations: Vec::new(),
            blocks: BTreeMap::new(),
            bid_counter: Irgen::BID_COUNTER_INIT,
            tempid_counter: Irgen::TEMPID_COUNTER_INIT,
            typedefs: &self.typedefs,
            structs: &self.structs,
            // Initial symbol table has scope for global variable already
            symbol_table: vec![global_scope],
        };
        let mut context = Context::new(irgen.bid_init);

        // Enter variable scope for alloc registers matched with function parameters
        irgen.enter_scope();

        // Creates the init block that stores arguments.
        irgen
            .translate_parameter_decl(&signature, irgen.bid_init, &name_of_params, &mut context)
            .map_err(|e| {
                IrgenError::new(format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"), e)
            })?;


        irgen
            .add_phinodes(&signature,  &name_of_params)
            .map_err(|e| {
                IrgenError::new(format!("error about phinode"), e)
            })?;
        // Translates statement.
        irgen.translate_stmt(&source.statement.node, &mut context, None, None)?;

        // Creates the end block
        let ret = signature.ret.set_const(false);
        let value = if ret == ir::Dtype::unit() {
            ir::Operand::constant(ir::Constant::unit())
        } else if ret == ir::Dtype::INT {
            // If "main" function, default return value is `0` when return type is `int`
            if name == "main" {
                ir::Operand::constant(ir::Constant::int(0, ret))
            } else {
                ir::Operand::constant(ir::Constant::undef(ret))
            }
        } else {
            ir::Operand::constant(ir::Constant::undef(ret))
        };

        // Last Block of the function
        irgen.insert_block(context, ir::BlockExit::Return { value });

        // Exit variable scope created above
        irgen.exit_scope();

        let func_def = ir::FunctionDefinition {
            allocations: irgen.allocations,
            blocks: irgen.blocks,
            bid_init: irgen.bid_init,
        };

        let decl = self
            .decls
            .get_mut(&name)
            .unwrap_or_else(|| panic!("The declaration of `{name}` must exist"));
        if let ir::Declaration::Function { definition, .. } = decl {
            if definition.is_some() {
                return Err(IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::Misc {
                        message: format!("the name `{name}` is defined multiple time"),
                    },
                ));
            }

            // Update function definition
            *definition = Some(func_def);
        } else {
            panic!("`{name}` must be function declaration")
        }

        Ok(())
    }

    
    /// Adds a possibly existing declaration.
    ///
    /// Returns error if the previous declearation is incompatible with `decl`.
    fn add_decl(&mut self, name: &str, decl: ir::Declaration) -> Result<(), IrgenError> {
        let old_decl = some_or!(
            self.decls.insert(name.to_string(), decl.clone()),
            return Ok(())
        );

        // Check if type is conflicting for pre-declared one
        if !old_decl.is_compatible(&decl) {
            return Err(IrgenError::new(
                name.to_string(),
                IrgenErrorMessage::ConflictingDtype {
                    dtype: old_decl.dtype(),
                    protorype_dtype: decl.dtype(),
                },
            ));
        }

        Ok(())
    }
}

/// Storage for instructions up to the insertion of a block
#[derive(Debug)]
struct Context {
    /// The block id of the current context.
    bid: ir::BlockId,
    /// Current instructions of the block.
    instrs: Vec<Named<ir::Instruction>>,
}

impl Context {
    /// Create a new context with block number bid
    fn new(bid: ir::BlockId) -> Self {
        Self {
            bid,
            instrs: Vec::new(),
        }
    }

    // Adds `instr` to the current context.
    fn insert_instruction(
        &mut self,
        instr: ir::Instruction,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let dtype = instr.dtype();
        self.instrs.push(Named::new(None, instr));

        Ok(ir::Operand::register(
            ir::RegisterId::temp(self.bid, self.instrs.len() - 1),
            dtype,
        ))
    }
}

/// A C function being translated.
struct IrgenFunc<'i> {
    /// return type of the function.
    return_type: ir::Dtype,
    /// initial block id for the function, typically 0.
    bid_init: ir::BlockId,
    /// arguments represented as initial phinodes. Order must be the same of that given in the C
    /// function.
    phinodes_init: Vec<Named<ir::Dtype>>,
    /// local allocations.
    allocations: Vec<Named<ir::Dtype>>,
    /// Map from block id to basic blocks
    blocks: BTreeMap<ir::BlockId, ir::Block>,
    /// current block id. `blocks` must have an entry for all ids less then this
    bid_counter: usize,
    /// current temporary id. Used to create temporary names in the IR for e.g,
    tempid_counter: usize,
    /// Usable definitions
    typedefs: &'i HashMap<String, ir::Dtype>,
    /// Usable structs
    // TODO: Add examples on how to use properly use this field.
    structs: &'i HashMap<String, Option<ir::Dtype>>,
    /// Current symbol table. The initial symbol table has the global variables.
    symbol_table: Vec<HashMap<String, ir::Operand>>,
}

impl IrgenFunc<'_> {
    /// Allocate a new block id.
    fn alloc_bid(&mut self) -> ir::BlockId {
        let bid = self.bid_counter;
        self.bid_counter += 1;
        ir::BlockId(bid)
    }

    /// Allocate a new temporary id.
    fn alloc_tempid(&mut self) -> String {
        let tempid = self.tempid_counter;
        self.tempid_counter += 1;
        format!("t{tempid}")
    }

    /// Create a new allocation with type given by `alloc`.
    fn insert_alloc(&mut self, alloc: Named<ir::Dtype>) -> usize {
        self.allocations.push(alloc);
        self.allocations.len() - 1
    }

    fn insert_phinodes(&mut self, phinode: Named<ir::Dtype>) -> usize {
        self.phinodes_init.push(phinode);
        self.phinodes_init.len() - 1
    }
    /// Insert a new block `context` with exit instruction `exit`.
    ///
    /// # Panic
    ///
    /// Panics if another block with the same bid as `context` already existed.
    fn insert_block(&mut self, context: Context, exit: ir::BlockExit) {
        let block = ir::Block {
            phinodes: if context.bid == self.bid_init {
                self.phinodes_init.clone()
            } else {
                Vec::new()
            },
            instructions: context.instrs,
            exit,
        };
        if self.blocks.insert(context.bid, block).is_some() {
            panic!("the bid `{}` is defined multiple time", context.bid)
        }
    }

    /// Enter a scope and create a new symbol table entry, i.e, we are at a `{` in the function.
    fn enter_scope(&mut self) {
        self.symbol_table.push(HashMap::new());
    }

    /// Exit a scope and remove the a oldest symbol table entry. i.e, we are at a `}` in the
    /// function.
    ///
    /// # Panic
    ///
    /// Panics if there are no scopes to exit, i.e, the function has a unmatched `}`.
    fn exit_scope(&mut self) {
        let _unused = self.symbol_table.pop().unwrap();
    }

    /// Inserts `var` with `value` to the current symbol table.
    ///
    /// Returns Ok() if the current scope has no previously-stored entry for a given variable.
    fn insert_symbol_table_entry(
        &mut self,
        var: String,
        value: ir::Operand,
    ) -> Result<(), IrgenErrorMessage> {
        let cur_scope = self
            .symbol_table
            .last_mut()
            .expect("symbol table has no valid scope");
        if cur_scope.insert(var.clone(), value).is_some() {
            return Err(IrgenErrorMessage::Redefinition { name: var });
        }

        Ok(())
    }


    /// Translate a declaration 
    fn translate_decl(
        &mut self,
        decl: &Declaration,
        context: &mut Context
    ) -> Result<(), IrgenErrorMessage> {
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&decl.specifiers)
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;


        // We do not cover typedef declaration inside function
        assert!(!is_typedef);

        // consider various declarator format in the future
        for init_decl in &decl.declarators {
            let declarator = init_decl.node.declarator.node.clone();
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(&declarator)
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let dtype = dtype.into_inner()
                    .resolve_typedefs(&self.typedefs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let name = name_of_declarator(&declarator);

                match &dtype {
                    ir::Dtype::Unit { .. } => todo!(),
                    // when applying initializer, type checking is necessary
                    ir::Dtype::Int { .. }
                    | ir::Dtype::Float { .. }
                    | ir::Dtype::Pointer { .. } 
                    | ir::Dtype::Struct { .. }
                    | ir::Dtype::Array { .. } => {
                        // Check whether Iniitalizer is exists
                        if let Some(initializer) = &init_decl.node.initializer {
                            match initializer.node.clone() {
                                Initializer::Expression(_) => {
                                    let value  = Some(self.translate_initializer(&initializer.node, context)?);
                                    let _unused = self.translate_alloc(name.clone(), dtype.clone(), value, context)?;
                                }
                                _ => {
                                    let _unused = self.translate_alloc(name.clone(), dtype.clone(), None, context)?;
                                    let ptr = self.lookup_symbol_table(&name)?;
                                    self.list_initializer(&initializer.node, ptr, dtype.clone(), context)?;
                                }
                            }
                        } else {
                            let _unused = self.translate_alloc(name, dtype.clone(), None, context)?;
                        };

                    }
                    ir::Dtype::Function { .. } => todo!(),
                    ir::Dtype::Typedef { .. } => panic!("typedef should be repalced by real dtype"),
                };

        }
        Ok(())
    }

    fn list_initializer(
        &mut self,
        initializer: &Initializer,
        ptr: ir::Operand,
        dtype: ir::Dtype,
        context: &mut Context
    ) -> Result<(), IrgenErrorMessage> {
        match initializer.clone() {
            Initializer::List(lists) => {
                let ptr = self.conver_array_to_ponter(
                    ptr, 
                    dtype
                    .get_array_inner()
                    .unwrap()
                    .clone(), 
                    context
                )?;
                for (i, initial_item) in izip!(lists).enumerate() {
                    match initial_item.node.initializer.node {
                        Initializer::List(_) => {
                            let offset_bytes = self.get_rest_byte(
                                dtype
                                .get_array_inner()
                                .unwrap()
                                .clone()
                            );
                            let offset_bytes = offset_bytes * i;
                            if offset_bytes != 0 {
                                let offset = context.insert_instruction(
                                    ir::Instruction::BinOp {
                                        op: BinaryOperator::Multiply,
                                        lhs: ir::Operand::Constant(
                                            ir::Constant::Int {
                                                value: 4,
                                                width: 64,
                                                is_signed: true

                                            }
                                        ),
                                        rhs: ir::Operand::Constant(
                                            ir::Constant::Int {
                                                value: offset_bytes as u128,
                                                width: 64,
                                                is_signed: true
                                            }
                                        ),
                                        dtype: ir::Dtype::int(64)
                                    }
                                )?;
                                let _unused = context.insert_instruction(
                                    ir::Instruction::GetElementPtr {
                                        ptr: ptr.clone(),
                                        offset,
                                        dtype: ptr.dtype()
                                    }
                                )?;
                            }

                            let _unused = self.list_initializer( &initial_item.node.initializer.node,
                                ptr.clone(),
                                dtype
                                .get_array_inner()
                                .unwrap()
                                .clone(), 
                                context
                            )?;
                        }
                        Initializer::Expression(expr) => {
                            let offset = i;
                            let offset = context.insert_instruction(
                                ir::Instruction::BinOp {
                                    op: BinaryOperator::Multiply,
                                    lhs: ir::Operand::Constant(
                                        ir::Constant::Int {
                                            value: offset as u128,
                                            width: 64,
                                            is_signed: true
                                        }
                                    ),
                                    rhs: ir::Operand::Constant(
                                        ir::Constant::Int {
                                            value: 4,
                                            width: 64,
                                            is_signed: true
                                        }
                                    ),
                                    dtype: ir::Dtype::int(64) 
                                }
                            )?;
                            let ptr = context.insert_instruction(
                                ir::Instruction::GetElementPtr {
                                    ptr: ptr.clone(),
                                    offset,
                                    dtype: ptr.dtype()
                                })?;
                            
                            let val = self.translate_expr_rvalue(&expr.node, context)?;
                            let _unused = context.insert_instruction(
                                ir::Instruction::Store {
                                    ptr,
                                    value: val
                                })?;

                        }
                    }
                }
                return Ok(());
            }
            Initializer::Expression(_) => {
                panic!("must be list")
            }
        } 
    }

    // Translate Initializer to IR Instructions
    fn translate_initializer(
        &mut self,
        initializer: &Initializer,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match initializer {
            Initializer::Expression(expr) => self.translate_expr_rvalue(&expr.node, context),
            Initializer::List(_initializers) => {
                // for element in initializers {
                    // let sub_initializer = element.node.initializer.node.clone();
                    // match  sub_initializer {
                        // Initializer::List(_) => {
                            // self.translate_initializer(&sub_initializer, context)?;
                        // }
                        // Initializer::Expression(expr) => {
                            // let value = self.translate_expr_rvalue(&expr.node, context)?;

                        // }
                    // }
                // } 
                // Ok(ir::Operand::Constant(ir::Constant::Unit{}))
                todo!()
            }
        }
    }

    /// Translate allocation to IR Instructions
    fn translate_alloc(
        &mut self,
        var: String,
        dtype: ir::Dtype,
        value: Option<ir::Operand>,
        context: &mut Context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // Insert allocation
        let id = self.insert_alloc(Named::new(Some(var.clone()), dtype.clone()));

        // Create pointer
        let pointer_type = ir::Dtype::pointer(dtype.clone());
        let rid = ir::RegisterId::local(id);
        let ptr = ir::Operand::register(rid, pointer_type);
        let _unused = self.insert_symbol_table_entry(var, ptr.clone());

        // Initialize allocated register if `value` is not `None`
        if let Some(value) = value {
            // Implict type cast 
            let value = self.translate_typecast(value, dtype, context)?;

            return context.insert_instruction(ir::Instruction::Store { ptr, value });
        }

        // Return alloc register if there is no store instruction
        Ok(ptr)
    }


    // Look up the symbol table
    fn lookup_symbol_table(
        &mut self,
        name: &String
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        for item in self.symbol_table.iter().rev() {
            if item.contains_key(name) {
                return Ok(
                    item.get(name).unwrap().clone()
                )
            }
        }

        Err(IrgenErrorMessage::Misc { 
            message: "there is no entry for `$name`".to_string()
         })
    }


    fn conver_array_to_ponter(
        &mut self,
        ptr: ir::Operand,
        dtype: ir::Dtype,
        context: &mut Context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        context.insert_instruction(
            ir::Instruction::GetElementPtr {
                ptr,
                offset: ir::Operand::Constant(
                    ir::Constant::int(0, ir::Dtype::INT)
                ),
                dtype: ir::Dtype::pointer(dtype)
            }
        )

    }

    /// Translate r-value Expression to IR instructions
    fn translate_expr_rvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(identifier) => {
                let ptr = self.lookup_symbol_table(&identifier.node.name)?;

                let dtype_of_ptr = ptr.dtype();
                let ptr_inner_type = dtype_of_ptr
                    .get_pointer_inner()
                    .ok_or_else(|| panic!("`Operand` from `symbol_table` must be pointer type"))?;

                // When `ptr` pointer from identifier of which inner type represents
                // `function` or `array` , return `ptr` without `load` instruction
                if ptr_inner_type.get_function_inner().is_some() {
                    return Ok(ptr)
                }

                // let's say two declarations are `int a` and `int b[10]`, `a` and `b` represent
                //`int *` and `[10 x i32]` respectively, when `a` is used as an r-value,, it's an 
                // integer value from `int*` by `load` instruction. On the other hand, when `b` is
                // used as an r-value, it's interpreted as an integer pointer that will be indexed.
                if let Some(array_inner) = ptr_inner_type.get_array_inner() {
                    // we convert array into pointer if, e.g., `b` is used as an r-value
                    return self.conver_array_to_ponter(ptr, array_inner.clone(), context);
                }

                context.insert_instruction(ir::Instruction::Load { ptr })

            }
            Expression::Constant(constant) => {
                let constant = ir::Constant::try_from(&constant.node)
                    .expect("`constant` must be interpreted to `ir::Constant` value");

                Ok(ir::Operand::constant(constant))
            }
            Expression::StringLiteral(_string_lit) => todo!(),
            Expression::Member(_member) => todo!(),
            Expression::Call(call) => self.translate_func_call(&call.node, context),
            Expression::SizeOfTy(type_name) => {
                let dtype = ir::Dtype::try_from(&type_name.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let (size_of, _) = dtype
                    .size_align_of(self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error:e })?;

                // `is_signed` must be `false` in the future
                Ok(ir::Operand::constant(ir::Constant::int(
                    size_of as u128,
                    ir::Dtype::LONG
                )))
            }
            Expression::SizeOfVal(var) => {
                let dtype = self.get_expr_type(var.deref().clone().node.0.node)?;

                let (size_of, _) = dtype
                    .size_align_of(self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error:e })?;
                Ok(ir::Operand::constant(ir::Constant::int(
                    size_of as u128,
                    ir::Dtype::LONG
                )))

            }
            Expression::AlignOf(type_name) => {
                let dtype = ir::Dtype::try_from(&type_name.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let (_, align_of) = dtype
                    .size_align_of(self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                // `is_signed` must be `false` in the future
                Ok(ir::Operand::constant(ir::Constant::Int {
                    value: align_of as u128,
                    width: 8 * ir::Dtype::SIZE_OF_LONG,
                    is_signed: false
                }
                ))

            }

            Expression::UnaryOperator(unary) => self.translate_unary_op(&unary.node, context),
            Expression::Cast(cast) => {
                let target_dtype = ir::Dtype::try_from(&cast.node.type_name.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let target_dtype = target_dtype
                    .resolve_typedefs(&self.typedefs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let operand = self.translate_expr_rvalue(&cast.node.expression.node, context)?;

                self.translate_typecast(operand, target_dtype, context)
            }
            Expression::BinaryOperator(binary) => self.translate_binary_op(
                binary.node.operator.node.clone(),
                &binary.node.lhs.node,
                &binary.node.rhs.node,
                context,
            ),
            Expression::Conditional(conditional) => {
                self.translate_conditional(&conditional.node, context)
            }

            Expression::Comma(exprs) => self.translate_comma(&exprs, context),
            _ => panic!("`is unsupported`"),

        } 
    }

    fn get_expr_type(
        &mut self,
        expr: Expression
    ) -> Result<ir::Dtype, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(identifier) => {
                let ptr = self.lookup_symbol_table(&identifier.node.name)?;

                let dtype_of_ptr = ptr.dtype();
                let ptr_inner_type = dtype_of_ptr
                    .get_pointer_inner()
                    .ok_or_else(|| panic!("`Operand` from `symbol_table` must be pointer type"))?;
                Ok(ptr_inner_type.clone())
            }
            Expression::Constant(constant) => {
                let constant = ir::Constant::try_from(&constant.node)
                    .expect("`constant` must be interpreted to `ir::Constant` value");

                Ok(constant.dtype())
            }
            Expression::StringLiteral(_string_lit) => todo!(),
            Expression::Member(_member) => todo!(),
            Expression::Call(call) => {
                let dtype = self.get_expr_type(call.node.callee.node)?;
                if let Some(rtype) = dtype.get_function_inner() {
                    return Ok(rtype.0.clone())
                }
                Err(IrgenErrorMessage::Misc { message: "should be function inner".to_string() })

            }
            Expression::SizeOfTy(type_name) => {
                let dtype = ir::Dtype::try_from(&type_name.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                Ok(dtype)

            }
            Expression::SizeOfVal(var) => {
                let dtype = self.get_expr_type(var.node.0.node)?;
                Ok(dtype)

            }
            Expression::AlignOf(type_name) => {
                let dtype = ir::Dtype::try_from(&type_name.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                Ok(dtype)
            }

            Expression::UnaryOperator(unary) => {
                match unary.node.operator.node {
                    UnaryOperator::Address => {
                        Ok(ir::Dtype::pointer(ir::Dtype::default()))
                    }
                    _ => {
                        self.get_expr_type(unary.node.operand.node)
                    } 
                }
            }
            Expression::Cast(cast) => {
                let target_dtype = ir::Dtype::try_from(&cast.node.type_name.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let target_dtype = target_dtype
                    .resolve_typedefs(&self.typedefs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                Ok(target_dtype)
            }
            Expression::BinaryOperator(binary) => {
                let lhs_type = self.get_expr_type(binary.node.lhs.node)?;
                let rhs_type = self.get_expr_type(binary.node.rhs.node)?;
                let dtype = self.merge_dtype(lhs_type, rhs_type)?;
                Ok(dtype)
            },
            Expression::Conditional(conditional) => {
                let lhs_type = self.get_expr_type(conditional.node.then_expression.node)?;
                let rhs_type = self.get_expr_type(conditional.node.else_expression.node)?;
                let dtype = self.merge_dtype(lhs_type, rhs_type)?;
                Ok(dtype)
                
            }

            Expression::Comma(exprs) => self.get_expr_type(
                exprs
                    .deref()
                    .clone()
                    .pop()
                    .unwrap()
                    .node
                    ),
            _ => panic!("`is unsupported`"),

        }  
    }

    /// Translate unary expression
    fn translate_unary_op(
        &mut self,
        expr: &UnaryOperatorExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr.operator.node {
            UnaryOperator::PostDecrement => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;

                let ptr = self.translate_expr_lvalue(&expr.operand.node, context)?;
                let value :ir::Operand;
                match val.dtype() {
                    ir::Dtype::Int { width, is_signed,.. } => {
                        value = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Minus,
                        lhs: val.clone(), 
                        rhs: ir::Operand::Constant(
                            ir::Constant::Int {
                                value: 1,
                                width,
                                is_signed,
                            }
                        ),
                        dtype: val.dtype()
                        })?;

                    }
                    ir::Dtype::Pointer { .. } => {
                        let offset = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Multiply,
                        rhs: ir::Operand::Constant(
                            ir::Constant::int(u128::MAX, ir::Dtype::int(64))
                        ),
                        lhs: ir::Operand::Constant(
                            ir::Constant::int(4, ir::Dtype::int(64))
                        ),
                        dtype: ir::Dtype::Int { width: 64, is_signed: true, is_const: false }
                        })?;

                        value = context.insert_instruction(ir::Instruction::GetElementPtr {
                            ptr: val.clone(),
                            offset,
                            dtype: val.dtype()
                        })?;
                    }
                    _ => panic!("only int and pointer")
                }
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value,
                })?;

                Ok(val)
                 
            }
            UnaryOperator::PreDecrement => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;

                let ptr = self.translate_expr_lvalue(&expr.operand.node, context)?;
                let value :ir::Operand;
                match val.dtype() {
                    ir::Dtype::Int { width, is_signed,.. } => {
                        value = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Minus,
                        lhs: val.clone(), 
                        rhs: ir::Operand::Constant(
                            ir::Constant::Int {
                                value: 1,
                                width,
                                is_signed,
                            }
                        ),
                        dtype: val.dtype()
                        })?;

                    }
                    ir::Dtype::Pointer { .. } => {
                        let offset = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Multiply,
                        rhs: ir::Operand::Constant(
                            ir::Constant::int(u128::MAX, ir::Dtype::int(64))
                        ),
                        lhs: ir::Operand::Constant(
                            ir::Constant::int(4, ir::Dtype::int(64))
                        ),
                        dtype: ir::Dtype::Int { width: 64, is_signed: true, is_const: false }
                        })?;

                        value = context.insert_instruction(ir::Instruction::GetElementPtr {
                            ptr: val.clone(),
                            offset,
                            dtype: val.dtype()
                        })?;
                    }
                    _ => panic!("only int and pointer")
                }
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;

                Ok(value)

            }
            UnaryOperator::PostIncrement => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;

                let ptr = self.translate_expr_lvalue(&expr.operand.node, context)?;

                let value :ir::Operand;
                match val.dtype() {
                    ir::Dtype::Int { width, is_signed,.. } => {
                        value = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Plus,
                        lhs: val.clone(), 
                        rhs: ir::Operand::Constant(
                            ir::Constant::Int {
                                value: 1,
                                width,
                                is_signed,
                            }
                        ),
                        dtype: val.dtype()
                        })?;

                    }
                    ir::Dtype::Pointer { .. } => {
                        let offset = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Multiply,
                        rhs: ir::Operand::Constant(
                            ir::Constant::int(1, ir::Dtype::int(64))
                        ),
                        lhs: ir::Operand::Constant(
                            ir::Constant::int(4, ir::Dtype::int(64))
                        ),
                        dtype: ir::Dtype::Int { width: 64, is_signed: true, is_const: false }
                        })?;

                        value = context.insert_instruction(ir::Instruction::GetElementPtr {
                            ptr: val.clone(),
                            offset,
                            dtype: val.dtype()
                        })?;
                    }
                    _ => panic!("only int and pointer")
                }
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;

                Ok(val)

            }
            UnaryOperator::PreIncrement => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;

                let ptr = self.translate_expr_lvalue(&expr.operand.node, context)?;
                let value: ir::Operand;
                match val.dtype() {
                    ir::Dtype::Int { width, is_signed,.. } => {
                        value = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Plus,
                        lhs: val.clone(), 
                        rhs: ir::Operand::Constant(
                            ir::Constant::Int {
                                value: 1,
                                width,
                                is_signed,
                            }
                        ),
                        dtype: val.dtype()
                        })?;

                    }
                    ir::Dtype::Pointer { .. } => {
                        let offset = context.insert_instruction(ir::Instruction::BinOp { 
                        op: BinaryOperator::Multiply,
                        rhs: ir::Operand::Constant(
                            ir::Constant::int(1, ir::Dtype::int(64))
                        ),
                        lhs: ir::Operand::Constant(
                            ir::Constant::int(4, ir::Dtype::int(64))
                        ),
                        dtype: ir::Dtype::Int { width: 64, is_signed: true, is_const: false }
                        })?;

                        value = context.insert_instruction(ir::Instruction::GetElementPtr {
                            ptr: val.clone(),
                            offset,
                            dtype: val.dtype()
                        })?;
                    }
                    _ => panic!("only int and pointer")
                }
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;

                Ok(value)

            }
            UnaryOperator::Minus => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;

                let value = context.insert_instruction(ir::Instruction::UnaryOp { 
                    op: UnaryOperator::Minus,
                    operand: val.clone(),
                    dtype: val.dtype()
                })?;
                Ok(value)

            }
            UnaryOperator::Plus => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;

                let value = context.insert_instruction(ir::Instruction::UnaryOp { 
                    op: UnaryOperator::Plus,
                    operand: val.clone(),
                    dtype: val.dtype()
                })?;
                Ok(value)


            }
            UnaryOperator::Negate => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;
                match val.dtype() {
                    ir::Dtype::Int { width,.. } => {
                        if width == 1 {
                            let value = context.insert_instruction(ir::Instruction::UnaryOp { 
                                op: UnaryOperator::Negate,
                                operand: val.clone(),
                                dtype: val.dtype()
                            })?;
                            return Ok(value)

                        }
                        Ok(val)
                    }
                    _ => {
                        todo!()
                    }
                }

            }
            UnaryOperator::Complement => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::BitwiseXor,
                    lhs: val.clone(), 
                    rhs: ir::Operand::Constant(
                        ir::Constant::Int {
                            value: u128::MAX,
                            width: val.dtype().get_int_width().unwrap(),
                            is_signed: true
                        }
                    ),
                    dtype: val.dtype()
                })?;
                Ok(value)
            }

            UnaryOperator::Address => {
                let val = self.translate_expr_lvalue(&expr.operand.node, context)?;
                
                Ok(val)
            }
            UnaryOperator::Indirection => {
                let val = self.translate_expr_rvalue(&expr.operand.node, context)?;
                context.insert_instruction(
                    ir::Instruction::Load {
                        ptr: val
                    }
                )
            }

        }
    }

    /// Translate binary expression
    fn translate_binary_op(
        &mut self,
        opt: BinaryOperator,
        lhs: &Expression,
        rhs: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match opt {
            BinaryOperator::Assign => {

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(
                    val_rhs.clone(),
                    ptr.dtype().get_pointer_inner().unwrap().clone(),
                    context
                )?;


                let _unused = context.insert_instruction(ir::Instruction::Store { 
                    ptr, value: val_rhs.clone()
                })?;
                Ok(val_rhs)

            }
            BinaryOperator::AssignBitwiseAnd => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::BitwiseAnd,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone()
                })?;
                Ok(value)
            }
            BinaryOperator::AssignBitwiseOr => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::BitwiseOr,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)

            }
            BinaryOperator::AssignBitwiseXor => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::BitwiseXor,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)
            }
            BinaryOperator::AssignDivide => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::Divide,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)

            }
            BinaryOperator::AssignMinus => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::Minus,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)
            }
            BinaryOperator::AssignModulo => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::Modulo,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)
            }
            BinaryOperator::AssignMultiply => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::Multiply,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)

            }
            BinaryOperator::AssignPlus => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::Plus,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)

            }
            BinaryOperator::AssignShiftLeft => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::ShiftLeft,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)
            }
            BinaryOperator::AssignShiftRight => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let val_rhs = self.translate_typecast(val_rhs, val_lhs.dtype(), context)?;

                let ptr = self.translate_expr_lvalue(lhs, context)?;
                let value = context.insert_instruction(ir::Instruction::BinOp { 
                    op: BinaryOperator::ShiftRight,
                    lhs: val_lhs.clone(), 
                    rhs: val_rhs.clone(), 
                    dtype: val_lhs.dtype()
                })?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr,
                    value: value.clone(),
                })?;
                Ok(value)
            }
            BinaryOperator::Equals
            | BinaryOperator::Greater 
            | BinaryOperator::GreaterOrEqual
            | BinaryOperator::Less
            | BinaryOperator::LessOrEqual
            | BinaryOperator::NotEquals=> {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let dtype = self.merge_dtype(
                    val_lhs.dtype(),
                    val_rhs.dtype()
                )?;

                let val_lhs = self.translate_typecast(val_lhs, dtype.clone(), context)?;
                let val_rhs = self.translate_typecast(val_rhs, dtype.clone(), context)?;
                context.insert_instruction(
                    ir::Instruction::BinOp {
                        op: opt,
                        lhs: val_lhs,
                        rhs: val_rhs,
                        dtype: ir::Dtype::Int {
                            width: 1,
                            is_signed: false,
                            is_const: false,
                        }
                })
            }
            BinaryOperator::Multiply
            | BinaryOperator::Divide
            | BinaryOperator::Plus
            | BinaryOperator::Minus
            | BinaryOperator::Modulo
            | BinaryOperator::ShiftLeft
            | BinaryOperator::ShiftRight
            | BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseOr
            | BinaryOperator::BitwiseXor => {
                let val_lhs = self.translate_expr_rvalue(lhs, context)?;
                let val_rhs = self.translate_expr_rvalue(rhs, context)?;
                let dtype = self.merge_dtype(
                    val_lhs.dtype(),
                    val_rhs.dtype()
                )?;

                let val_lhs = self.translate_typecast(val_lhs, dtype.clone(), context)?;
                let val_rhs = self.translate_typecast(val_rhs, dtype.clone(), context)?;
                context.insert_instruction(
                    ir::Instruction::BinOp {
                        op: opt,
                        lhs: val_lhs,
                        rhs: val_rhs,
                        dtype,
                })

            } 

            BinaryOperator::LogicalAnd => {
                let bid_second = self.alloc_bid();
                let bid_temp = self.alloc_bid();
                let bid_end = self.alloc_bid();


                let _unused = self.translate_condition(
                    lhs,
                    mem::replace(context, Context::new(bid_end)),
                    bid_second,
                    bid_temp,
                )?;

                let mut context_second = Context::new(bid_second);
                let val_second = 
                    self.translate_expr_rvalue(rhs, &mut context_second)?;

                let val_second = 
                    self.translate_typecast_to_bool(val_second, &mut context_second)?;




                let mut context_temp = Context::new(bid_temp);


                // Allocate at stack
                let var = self.alloc_tempid();
                let ptr = self.translate_alloc(
                    var,
                    ir::Dtype::Int {
                        width: 1,
                        is_signed: false,
                        is_const: false,
                    },
                    None,
                    context
                )?;

                // Finish the second branch
                let _unused = context_second.insert_instruction(
                    ir::Instruction::Store {
                        ptr: ptr.clone(),
                        value: val_second,
                    }
                )?;

                self.insert_block(
                    context_second,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new())
                    }
                );

                // Finish the temp branch
                let _unused = context_temp.insert_instruction(
                    ir::Instruction::Store {
                        ptr: ptr.clone(),
                        value: ir::Operand::Constant(ir::Constant::Int {
                            value: 0,
                            width: 1,
                            is_signed: false
                        }),
                    }
                )?;

                self.insert_block(
                    context_temp,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new())
                    }
                );


                context.insert_instruction(ir::Instruction::Load { ptr })





            }
            BinaryOperator::LogicalOr => {
                let bid_second = self.alloc_bid();
                let bid_temp = self.alloc_bid();
                let bid_end = self.alloc_bid();


                let _unused = self.translate_condition(
                    lhs,
                    mem::replace(context, Context::new(bid_end)),
                    bid_temp,
                    bid_second,
                )?;

                let mut context_second = Context::new(bid_second);
                let val_second = 
                    self.translate_expr_rvalue(rhs, &mut context_second)?;

                let val_second = 
                    self.translate_typecast_to_bool(val_second, &mut context_second)?;



                let mut context_temp = Context::new(bid_temp);


                // Allocate at stack
                let var = self.alloc_tempid();
                let ptr = self.translate_alloc(
                    var,
                    ir::Dtype::Int {
                        width: 1,
                        is_signed: false,
                        is_const: false,
                    },
                    None,
                    context
                )?;

                // Finish the second branch
                let _unused = context_second.insert_instruction(
                    ir::Instruction::Store {
                        ptr: ptr.clone(),
                        value: val_second,
                    }
                )?;

                self.insert_block(
                    context_second,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new())
                    }
                );

                // Finish the temp branch
                let _unused = context_temp.insert_instruction(
                    ir::Instruction::Store {
                        ptr: ptr.clone(),
                        value: ir::Operand::Constant(ir::Constant::Int {
                            value: 1,
                            width: 1,
                            is_signed: false
                        }),
                    }
                )?;

                self.insert_block(
                    context_temp,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new())
                    }
                );

                context.insert_instruction(ir::Instruction::Load { ptr })



            }
            BinaryOperator::Index => {
                let index = self.translate_expr_rvalue(rhs, context)?;
                let ptr_add = self.translate_expr_rvalue(lhs, context)?;
                let index = self.translate_typecast(
                    index,
                    ir::Dtype::int(64),
                    context
                )?;


                let rest_bytes = self.get_rest_byte(
                    ptr_add
                    .dtype()
                    .get_pointer_inner()
                    .unwrap()
                    .clone()
                );
                 
                let offset = context.insert_instruction(
                    ir::Instruction::BinOp {
                        op: BinaryOperator::Multiply,
                        lhs: index.clone(),
                        rhs: ir::Operand::Constant(
                            ir::Constant::int(4 * (rest_bytes as u128), index.dtype())

                        ),
                        dtype: index.dtype()
                    }
                )?;

                let ptr_add = context.insert_instruction(
                    ir::Instruction::GetElementPtr {
                        ptr: ptr_add.clone(),
                        offset,
                        dtype: ptr_add.dtype()
                    }
                )?;

                match ptr_add.dtype().get_pointer_inner().unwrap().clone() {
                    ir::Dtype::Array { inner , .. } => {
                        context.insert_instruction(
                            ir::Instruction::GetElementPtr {
                                ptr: ptr_add.clone(),
                                offset: ir::Operand::Constant(
                                    ir::Constant::int(
                                        0,
                                        ir::Dtype::INT)) ,
                                dtype: ir::Dtype::pointer(inner.deref().clone())
                            }
                        )

                    }
                    _ => {
                        context.insert_instruction(
                            ir::Instruction::Load {
                                ptr: ptr_add
                            }
                        )

                    }

                }
            }
        
            
        }

    }

    fn get_rest_byte(
        &mut self,
        dtype: ir::Dtype
    ) -> usize {
        match dtype.clone() {
            ir::Dtype::Array {  size , .. } => {
                self.get_rest_byte(dtype.get_array_inner().unwrap().clone()) * size
            }
            _ => 1
        }
    }


    // Translate conditional expression to IR instructions
    fn translate_conditional(
        &mut self,
        conditional_expr: &ConditionalExpression,
        context: &mut Context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let bid_then = self.alloc_bid();
        let bid_else = self.alloc_bid();
        let bid_end = self.alloc_bid();

        self.translate_condition(
            &conditional_expr.condition.node,
            mem::replace(context, Context::new(bid_end)),
            bid_then,
            bid_else,
        )?;

        // Translates the then branch
        let mut context_then = Context::new(bid_then);

        let val_then = 
            self.translate_expr_rvalue(&conditional_expr.then_expression.node, &mut context_then)?;

        // Translates the else branch
        let mut context_else = Context::new(bid_else);
        let val_else = 
            self.translate_expr_rvalue(&conditional_expr.else_expression.node, &mut context_else)?;


        let merged_dtype = self.merge_dtype(val_then.dtype(), val_else.dtype())?;
        let val_then = 
            self.translate_typecast(val_then, merged_dtype.clone(), &mut context_then)?;
        let val_else = 
            self.translate_typecast(val_else, merged_dtype.clone(), &mut context_else)?;

        // Allocates at stack.
        let var = self.alloc_tempid();
        let ptr = self.translate_alloc(var, merged_dtype, None, context)?;


        // Finished the then branch
        let _unused = context_then.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: val_then,
        });

        self.insert_block(
            context_then,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new())
            }
        );


        // Finished the else branch
        let _unused = context_else.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: val_else,
        });

        self.insert_block(
            context_else,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new())
            }
        );
        
        context.insert_instruction(ir::Instruction::Load { ptr })

    }


    fn merge_dtype(
        &mut self,
        lhs: ir::Dtype,
        rhs: ir::Dtype,
    ) -> Result<ir::Dtype, IrgenErrorMessage> {
        match lhs {
            ir::Dtype::Float { width: lhs_width, ..   } => {
                match rhs {
                    ir::Dtype::Float { width: rhs_width, .. } => {
                        return Ok(ir::Dtype::float(max(rhs_width, lhs_width)))
                    }
                    ir::Dtype::Int { .. } => {
                        return Ok(ir::Dtype::float(lhs_width)) 
                    }
                    _ => panic!("lhs and rhs should be same type")
                }
            }
            ir::Dtype::Int { width: lhs_width, is_signed: lhs_signed,  .. } => {
                match rhs {
                    ir::Dtype::Float { width,.. } => {
                        return Ok(ir::Dtype::float(width)) 
                    }
                    ir::Dtype::Int { width: rhs_width, is_signed: rhs_signed, .. } => {
                        let int_width = ir::Dtype::SIZE_OF_INT * ir::Dtype::BITS_OF_BYTE;
                        if max(lhs_width, rhs_width) < int_width {
                            return Ok(ir::Dtype::INT)
                        } else if max(lhs_width, rhs_width) == int_width {
                            if lhs_width == rhs_width {
                                if !lhs_signed || !rhs_signed {
                                    return Ok(ir::Dtype::Int {
                                        width: int_width,
                                        is_signed: false,
                                        is_const: false,
                                    })
                                } else {
                                    return Ok(ir::Dtype::INT)
                                }
                            } else if lhs_width == int_width {
                                if !lhs_signed {
                                    return Ok(ir::Dtype::Int {
                                        width: int_width,
                                        is_signed: false,
                                        is_const: false,
                                    })
                                } else {
                                    return Ok(ir::Dtype::INT)
                                }
                            } else {
                                if !rhs_signed {
                                    return Ok(ir::Dtype::Int {
                                        width: int_width,
                                        is_signed: false,
                                        is_const: false,
                                    })
                                } else {
                                    return Ok(ir::Dtype::INT)
                                }

                            }
                            
                        } else {
                            if lhs_width == rhs_width {
                                if !lhs_signed || !rhs_signed {
                                    return Ok(ir::Dtype::Int {
                                        width: lhs_width,
                                        is_signed: false,
                                        is_const: false,
                                    })
                                } else {
                                    return Ok(ir::Dtype::int(lhs_width))
                                }
                            } else if lhs_width > int_width {
                                if !lhs_signed {
                                    return Ok(ir::Dtype::Int {
                                        width: lhs_width,
                                        is_signed: false,
                                        is_const: false,
                                    })
                                } else {
                                    return Ok(ir::Dtype::int(lhs_width))
                                }
                            } else {
                                if !rhs_signed {
                                    return Ok(ir::Dtype::Int {
                                        width: rhs_width,
                                        is_signed: false,
                                        is_const: false,
                                    })
                                } else {
                                    return Ok(ir::Dtype::int(rhs_width))
                                }

                            }

                        }
                    }
                    _ => panic!("lhs and rhs should be same type")
                }
            }
            _ => todo!()
        }
    }
    /// Translate comma expression to IR instrunction
    fn translate_comma(
        &mut self,
        exprs: &[Node<Expression>],
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let mut result = exprs 
            .iter()
            .map(|e| self.translate_expr_rvalue(&e.node, context))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(result.pop().expect("Comma expression expected expressions"))
    }
    


    /// Translate function call to IR instructinos
    fn translate_func_call(
        &mut self,
        call: &CallExpression,
        context: &mut Context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // Extract function signature of callee
        let callee = self.translate_expr_rvalue(&call.callee.node, context)?;
        let function_pointer_type = callee.dtype();
        let function = function_pointer_type.get_pointer_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer { 
                callee: callee.clone()
            }
        })?;

        let (return_type, parameters) = function.get_function_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer { 
                callee: callee.clone()
             }
        })?;

        let args = call
            .arguments
            .iter()
            .map(|a| self.translate_expr_rvalue(&a.node, context))
            .collect::<Result<Vec<_>, _>>()?;

        // Implicit type casting 
        if args.len() != parameters.len() {
            return Err(IrgenErrorMessage::Misc { 
                message: format!("too few arguments to function `{}`", callee.write_string()),
            });
        }

        let args = izip!(args, parameters)
            .map(|(a, p)| self.translate_typecast(a, p.clone(), context))
            .collect::<Result<Vec<_>, _>>()?;

        let return_type  = return_type.clone().set_const(false);
        context.insert_instruction(ir::Instruction::Call {
            callee,
            args,
            return_type,
        })
        
    }


    fn translate_index_op(
        &mut self,
        lhs: &Expression,
        rhs: &Expression,
        context: &mut Context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let ptr_add = self.translate_expr_rvalue(lhs, context)?;
        let index = self.translate_expr_rvalue(rhs, context)?;
        let index = self.translate_typecast(
            index,
            ir::Dtype::int(64),
            context
        )?;
        // let mut offset_byte: usize = 1;
        // if let Some(inner) = ptr_add.dtype().get_pointer_inner() {
            // match inner {
                // &ir::Dtype::Array {  size , ..  } => {
                    // offset_byte = size;
                        // offset = context.insert_instruction(
                        // ir::Instruction::BinOp {
                            // op: BinaryOperator::Multiply,
                            // lhs: index.clone(),
                            // rhs: ir::Operand::Constant(
                                // ir::Constant::int(4 * (offset_byte as u128), index.dtype())

                            // ),
                            // dtype: index.dtype()
                        // }
                    // )?;
                // }
                // &ir::Dtype::Pointer { .. } => {
                    // todo!() 
                // }
                // _ => ()
            // }
        // }

        let offset = context.insert_instruction(
        ir::Instruction::BinOp {
            op: BinaryOperator::Multiply,
            lhs: index.clone(),
            rhs: ir::Operand::Constant(
                ir::Constant::int(4 , index.dtype())

            ),
            dtype: index.dtype()
            }
        )?;


        let ptr_add = context.insert_instruction(
            ir::Instruction::GetElementPtr {
                ptr: ptr_add.clone(),
                offset,
                dtype: ptr_add.dtype()
            }
        )?;

        Ok(ptr_add)
    }

    /// Translate l-value Expression to IR instructions
    fn translate_expr_lvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(identifier) => self.lookup_symbol_table(&identifier.node.name),
            Expression::UnaryOperator(unary) => match &unary.node.operator.node {
                UnaryOperator::Indirection => {
                    self.translate_expr_rvalue(&unary.node.operand.node, context)
                }
                _ => Err(IrgenErrorMessage::Misc { 
                    message: "This error occured at `IrgenFunc::translate_expr_lvalue`"
                            .to_string()   
                 })
            }
            Expression::BinaryOperator(binary) => match &binary.node.operator.node {
                BinaryOperator::Index => {
                    self.translate_index_op(&binary.node.lhs.node, &binary.node.rhs.node, context)
                }
                _ => Err(IrgenErrorMessage::Misc { 
                    message: "binary operator expression cannot be used as l-value except \
                              index operator expression"
                              .to_string()
                 })
            },
            Expression::StringLiteral(_string_lit) => todo!(),
            Expression::Member(_member) => todo!(),
            Expression::Conditional(_) 
            | Expression::Constant(_)
            | Expression::Call(_)
            | Expression::Comma(_)
            | Expression::SizeOfTy(_)
            | Expression::AlignOf(_)
            | Expression::Cast(_)
            | Expression::SizeOfVal(_) => {
                Err(IrgenErrorMessage::Misc { 
                    message: "This error occured at `IrgenFunc::translate_expr_lvalue`".to_string(),
                 })
            }
            _ => panic!("`is unsupported`"),

        }
    }
    // Type cast 
    fn translate_typecast(
        &mut self,
        value: ir::Operand,
        dtype: ir::Dtype,
        context: &mut Context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match (value.dtype(), dtype.clone()) {
            (ir::Dtype::Int { width, is_signed, .. },
            ir::Dtype::Int { width: target_width, is_signed: target_sign,.. }) => {
                if width == target_width && is_signed == target_sign {
                    return Ok(value)
                }
            }
            (ir::Dtype::Float { width, .. },
            ir::Dtype::Float { width: target_width, .. }) => {
                if width == target_width {
                    return Ok(value)
                }
            }
            (ir::Dtype::Pointer { inner,.. },
            ir::Dtype::Pointer { inner: target_inner, .. }) => {
                if inner.deref().clone() == target_inner.deref().clone() {
                    return Ok(value)
                }
            }
            _ => {}
        }
        if value.dtype() == dtype {
            Ok(value)
        } else {
            context.insert_instruction(
                ir::Instruction::TypeCast { value, target_dtype: dtype }
            )
        }
    }


    fn translate_condition(
        &mut self,
        condition: &Expression,
        mut context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        let condition = self.translate_expr_rvalue(condition, &mut context)?;

        let condition = self.translate_typecast_to_bool(condition, &mut context)?;

        self.insert_block(
            context,
            ir::BlockExit::ConditionalJump {
                condition,
                arg_then: ir::JumpArg::new(bid_then, Vec::new()),
                arg_else: ir::JumpArg::new(bid_else, Vec::new()),
            },
        );

        Ok(())
    }

    /// Translate initializer statement of for-loop to IR block
    fn translate_for_initializer(
        &mut self,
        initializer: &ForInitializer,
        context: &mut Context
    ) -> Result<(), IrgenErrorMessage> {
        match initializer {
            ForInitializer::Empty => (),
            ForInitializer::Expression(expr) => {
                let _unused = self.translate_expr_rvalue(&expr.node, context)?;
            }
            ForInitializer::Declaration(decl) => {
                return self.translate_decl(&decl.node, context);
            }
            ForInitializer::StaticAssert(_) => {
                panic!("ForInitializer::StaticAssert is unsupported")
            }
        }
        Ok(())
    }


    /// Translate conditon
    fn translate_opt_condition(
        &mut self,
        condition: &Option<Box<Node<Expression>>>,
        context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        if let Some(condition) = condition {
            self.translate_condition(&condition.node, context, bid_then, bid_else)
        } else {
            self.insert_block(
                context,
                ir::BlockExit::Jump {
                    arg: ir::JumpArg::new(bid_then, Vec::new()),
                }
            );
            Ok(())

        }
    }

    /// Translate switch body 
    fn translate_switch_body(
        &mut self,
        stmt: &Statement,
        bid_end: ir::BlockId
    ) -> Result<(Vec<(ir::Constant, ir::JumpArg)>, ir::BlockId), IrgenError> {
        let mut cases = Vec::new();
        let mut default = None;

        let items = if let Statement::Compound(items) = stmt {
            items
        } else {
            panic!("`Statement` in the `switch` is unsupported except `Statement::Compoind`")
        };

        // Enter variable scope for compound statement
        self.enter_scope();
        
        for item in items {
            // Extract Statement from Block Item
            match &item.node {
                BlockItem::Statement(stmt) => {
                    self.translate_switch_body_inner(&stmt.node, &mut cases, &mut default, bid_end)?;

                }
                _ => panic!("is unsupported"),
            }

        }

        self.exit_scope();

        let default = default.unwrap_or(bid_end);

        Ok((cases, default))
    }

    fn translate_switch_body_inner(
        &mut self,
        stmt: &Statement,
        cases: &mut Vec<(ir::Constant, ir::JumpArg)>,
        default: &mut Option<ir::BlockId>,
        bid_end: ir::BlockId,
    ) -> Result<(), IrgenError> {
        let label_stmt = if let Statement::Labeled(label_stmt) = stmt {
            &label_stmt.node
        } else {
            panic!("`BlockItem::Statement` in the `Statement::Compound` of the `switch` \
                    is unsupported except `Statement::Labeled`"
                )
        };

        let bid = self.alloc_bid();
        let case = self.translate_switch_body_label_statement(label_stmt, bid, bid_end)?;

        if let Some(case) = case {
            if !case.is_integer_constant() {
                return Err(IrgenError::new(
                    label_stmt.label.write_string(),
                    IrgenErrorMessage::Misc { 
                        message: "exception is not an integer constant expression".to_string()
                     },
                ));
            }

            // consider the cases that same `value` but different `width`
            if cases.iter().any(|(c, _)| &case == c) {
                return Err(IrgenError::new(
                    label_stmt.label.write_string(),
                    IrgenErrorMessage::Misc { 
                        message: "duplicate case value".to_string(),
                     }
                ));
            }
            cases.push((case, ir::JumpArg::new(bid, Vec::new())));

        } else {
            if default.is_some() {
                return Err(IrgenError::new(
                    label_stmt.label.write_string(),
                    IrgenErrorMessage::Misc {
                        message: "previous default already exists".to_string(),
                    }        
                ));
            }
            *default = Some(bid);
        }
        Ok(())
    }
    
    fn translate_switch_body_label_statement(
        &mut self,
        label_stmt: &LabeledStatement,
        bid: ir::BlockId,
        bid_end: ir::BlockId
    ) -> Result<Option<ir::Constant>, IrgenError> {
        let case = match &label_stmt.label.node {
            Label::Identifier(_) => panic!("`Lable::Identifier` is unsupported"),
            Label::Case(expr) => {
                let constant = ir::Constant::try_from(&expr.node)
                        .map_err(|_| {
                            IrgenError::new(
                                expr.write_string(),
                                IrgenErrorMessage::Misc { 
                                    message: "case lable does not reduce to an integer constant"
                                            .to_string()   
                                 }
                            )
                        })?;
                Some(constant)
            }
            Label::Default => None,
            _ => panic!("is unsuported"),
        };

        let items = if let Statement::Compound(items) = &label_stmt.statement.node {
            items
        } else {
            panic!("`Statement ` in the `label` is unsupported except `Statement::Compound`")
        };

        // Enter variable scope for compound statement 
        self.enter_scope();
        
        // Split last and all the rest of the elements of the `Compound` items
        let (last, items) = items
            .split_last()
            .expect("`Statement::Compound` has no item");

        let mut context = Context::new(bid);
        for item in items {
            match &item.node {
                BlockItem::Declaration(decl) => {
                    self.translate_decl(&decl.node, &mut context)
                        .map_err(|e| IrgenError::new(decl.write_string(), e))?;
                }
                BlockItem::Statement(stmt) => {
                    self.translate_stmt(&stmt.node, &mut context, None, None)?
                }
                _ => panic!("is unsupported")
            }
        }


        // The last element of the `Compound` items must be `Statement::Break`
        let stmt = if let BlockItem::Statement(stmt) = &last.node {
            &stmt.node
        } else {
            panic!(
                "`BlockItem` in the `Statement::Compound` of the `label` 
                is unsupported except `BlockItem::Statement`"
            )
        };

        assert_eq!(
            stmt,
            &Statement::Break,
            "the last `BlockItem` in the `Statement::Compound` \
            of the `label` must be `Statement::Break`"
        );

        // Translate `Statement::break` to IR
        self.insert_block(
            context,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );
        self.exit_scope();
        Ok(case)


    }

    /// Implicit typecast to bool
    fn translate_typecast_to_bool(
        &mut self,
        condition: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match condition.clone() {
            ir::Operand::Constant(constant) => {
                match constant {
                    ir::Constant::Int {  width, is_signed , .. } => {
                        if width == 1 && is_signed == false {
                            return Ok(condition.clone())
                        }
                        
                        context.insert_instruction(
                            ir::Instruction::BinOp {
                                op: BinaryOperator::NotEquals,
                                lhs: condition.clone(),
                                rhs: ir::Operand::Constant(ir::Constant::Int {
                                    value: 0,
                                    width,
                                    is_signed,
                                }),
                                dtype: ir::Dtype::BOOL

                            }
                        )

                    }
                    _ => {
                        Ok(condition.clone())
                    }

                }
            }
            ir::Operand::Register { dtype , .. } => {
                match dtype {
                    ir::Dtype::Int { width, is_signed, .. } => {
                        if width == 1 && !is_signed {
                            return Ok(condition.clone())
                        }
                        context.insert_instruction(
                            ir::Instruction::BinOp {
                                op: BinaryOperator::NotEquals,
                                lhs: condition.clone(),
                                rhs: ir::Operand::Constant(
                                    ir::Constant::Int {
                                        value: 0,
                                        width,
                                        is_signed
                                    }
                                ),
                                dtype: ir::Dtype::INT
                            }
                        ) 
                    }
                    ir::Dtype::Float { width, ..  } => {
                        context.insert_instruction(
                            ir::Instruction::BinOp {
                                op: BinaryOperator::NotEquals,
                                lhs: condition.clone(),
                                rhs: ir::Operand::Constant(
                                    ir::Constant::Float {
                                        value: OrderedFloat::<f64>::from(0.0),
                                        width,
                                    }
                                ),
                                dtype: ir::Dtype::FLOAT
                            }
                        ) 

                    }
                    _ => {
                        panic!()
                    }
                }
            }
        }
    }

    /// Transalte a C statement `stmt` under the current block `context`, with `continue` block
    /// `bid_continue` and break block `bid_break`.
    fn translate_stmt(
        &mut self,
        stmt: &Statement,
        context: &mut Context,
        bid_continue: Option<ir::BlockId>,
        bid_break: Option<ir::BlockId>,
    ) -> Result<(), IrgenError> {
        match stmt {
            Statement::Compound(items) => {
                //Enter variable scope for compound statement
                self.enter_scope();

                for item in items {
                    match &item.node {
                        BlockItem::Declaration(decl) => {
                            self.translate_decl(&decl.node, context)
                                .map_err(|e| IrgenError::new(decl.write_string(), e))?;
                        }
                        BlockItem::StaticAssert(_) => {
                            panic!("BlockItem::StaticAssert is unsupported")
                        }
                        BlockItem::Statement(stmt) => {
                            self.translate_stmt(&stmt.node, context, bid_continue, bid_break)?;
                        }
                    }
                }

                // Exit variable scope created above
                self.exit_scope();
                
                Ok(())
            }
            Statement::Expression(expr) => {
                // Translates expr
                if let Some(expr) = expr {
                    let _unused = self
                            .translate_expr_rvalue(&expr.node, context)
                            .map_err(|e| IrgenError::new(expr.write_string(), e))?;

                }
                Ok(())
            }
            Statement::If(stmt) => {
                let bid_then = self.alloc_bid();
                let bid_else = self.alloc_bid();
                let bid_end = self.alloc_bid();

                self.translate_condition(
                    &stmt.node.condition.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_then,
                    bid_else,
                )
                .map_err(|e| IrgenError::new(stmt.node.condition.write_string(), e))?;
                
                // Translates then branch
                let mut context_then = Context::new(bid_then);
                self.translate_stmt(
                    &stmt.node.then_statement.node,
                    &mut context_then,
                    bid_continue,
                    bid_break
                )?;

                self.insert_block(
                    context_then,
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                     },
                );


                // Translate else branch
                let mut context_else = Context::new(bid_else);
                if let Some(else_stmt) = &stmt.node.else_statement {
                    self.translate_stmt(
                        &else_stmt.node,
                        &mut context_else,
                        bid_continue,
                        bid_break
                    )?;
                }
                self.insert_block(
                    context_else,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    }
                );

                Ok(())
                
            }

            Statement::Return(expr) => {
                let value = match expr {
                    Some(expr) => self 
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError::new(expr.write_string(), e))?,
                    None => ir::Operand::constant(ir::Constant::unit()),
                };

                // Implicit type casting
                let value = self
                    .translate_typecast(value, self.return_type.clone(), context)
                    .map_err(|e| IrgenError::new(expr.write_string(), e))?;

                let bid_end = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::Return { value },
                );

                Ok(())

            }

            Statement::For(for_stmt) => {
                let for_stmt = &for_stmt.node;

                // Jump to the for-loop initializer block
                let bid_init = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_init)),
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_init, Vec::new())
                     }
                );

                // Enter variable scope for for-loop initialier
                self.enter_scope();

                self.translate_for_initializer(&for_stmt.initializer.node, context)
                    .map_err(|e| IrgenError::new(for_stmt.initializer.write_string(), e))?;

                // Jump to the for-loop conditional block
                let bid_cond = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_cond, Vec::new())
                     }
                );

                let bid_body = self.alloc_bid();
                let bid_step = self.alloc_bid();
                let bid_end = self.alloc_bid();
                self.translate_opt_condition(
                    &for_stmt.condition,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(for_stmt.condition.write_string(), e))?;


                // Enter variable scope for for-loop body
                self.enter_scope();

                let mut context_body = Context::new(bid_body);
                self.translate_stmt(
                    &for_stmt.statement.node,
                    &mut context_body,
                    Some(bid_step),
                    Some(bid_end),
                )?;

                // Exit variable scope for for-loop body
                self.exit_scope();

                self.insert_block(
                    context_body,
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_step, Vec::new()),
                     }
                );

                let mut context_step = Context::new(bid_step);
                if let Some(step_expr) = &for_stmt.step {
                    let _unused = self
                            .translate_expr_rvalue(&step_expr.node, &mut context_step)
                            .map_err(|e| IrgenError::new(for_stmt.step.write_string(), e))?;
                }

                self.insert_block(
                    context_step,
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                     }
                );

                // Exit variable scope for for-loop body initializer
                self.exit_scope();

                Ok(())
            }   

            Statement::While(while_stmt) => {
                let while_stmt = &while_stmt.node;
                // Jump to starting block of while-loop
                let bid_cond = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_cond, Vec::new())
                     }
                );

                let bid_body = self.alloc_bid();
                let bid_end = self.alloc_bid();
                self.translate_condition(
                    &while_stmt.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end
                )
                .map_err(|e| IrgenError::new(while_stmt.expression.write_string(), e))?;

                // Enter variable scope for while-loop
                self.enter_scope();

                let mut context_body = Context::new(bid_body);
                self.translate_stmt(
                    &while_stmt.statement.node,
                    &mut context_body,
                    Some(bid_cond),
                    Some(bid_end)
                )?;

                self.insert_block(
                    context_body,
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                     },
                );

                // Exit variable scope created above
                self.exit_scope();

                Ok(())
            }

            Statement::DoWhile(do_while_stmt) => {
                let while_stmt = &do_while_stmt.node;

                // Jump to starting block of do-while-loop
                let bid_body = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_body)),
                    ir::BlockExit::Jump{
                        arg: ir::JumpArg::new(bid_body, Vec::new())
                    },
                );

                // Enter variable scope for do-while-loop body
                self.enter_scope();

                let bid_cond = self.alloc_bid();
                let bid_end = self.alloc_bid();
                self.translate_stmt(
                    &while_stmt.statement.node,
                    context,
                    Some(bid_cond),
                    Some(bid_end)
                )?;

                // Exit variable scope created above
                self.exit_scope();

                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_cond, Vec::new())
                     }
                );

                self.translate_condition(
                    &while_stmt.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(while_stmt.expression.write_string(), e))?;

                Ok(())
            }

            Statement::Switch(switch_stmt) => {
                let value = self
                    .translate_expr_rvalue(&switch_stmt.node.expression.node, context)
                    .map_err(|e| IrgenError::new(switch_stmt.node.expression.write_string(), e))?;

                let bid_end = self.alloc_bid();
                let (cases, bid_default) = 
                    self.translate_switch_body(&switch_stmt.node.statement.node, bid_end)?;

                self.insert_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::Switch {
                        value,
                        default: ir::JumpArg::new(bid_default, Vec::new()),
                        cases,
                    }
                );

                Ok(())
            }

            Statement::Continue => {
                let bid_continue = bid_continue.ok_or_else(|| {
                    IrgenError::new(
                        "continue;".to_string(),
                        IrgenErrorMessage::Misc { 
                            message: "continue statement not within a loop".to_string(),
                         }
                    )
                })?;

                let next_context = Context::new(self.alloc_bid());
                self.insert_block(
                    mem::replace(context, next_context),
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_continue, Vec::new()),
                     }
                );

                Ok(())
            }

            Statement::Break => {
                let bid_break = bid_break.ok_or_else(|| {
                    IrgenError::new(
                        "break;".to_string(),
                        IrgenErrorMessage::Misc { 
                            message: "break statement not within a loop or switch".to_string(),
                         }
                    )
                })?;

                let next_context = Context::new(self.alloc_bid());
                self.insert_block(
                    mem::replace(context, next_context),
                    ir::BlockExit::Jump { 
                        arg: ir::JumpArg::new(bid_break, Vec::new()),
                     }
                );

                Ok(())

            }

            Statement::Labeled(label_stmt) => Err(IrgenError::new(
                label_stmt.node.label.write_string(),
                IrgenErrorMessage::Misc { 
                    message: "label statement not within a switch".to_string(),
                 }
            )),

            _ => todo!()
        } 
    }

    /// Translate parameter declaration of the functions to IR.
    ///
    /// For example, given the following C function from [`foo.c`][foo]:
    ///
    /// ```C
    /// int foo(int x, int y, int z) {
    ///    if (x == y) { return y; }
    ///    else { return z; }
    /// }
    /// ```
    ///
    /// The IR before this function looks roughly as follows:
    ///
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    /// ```
    ///
    /// With the following arguments :
    /// ```ignore
    /// signature = FunctionSignature { ret: ir::INT, params: vec![ir::INT, ir::INT, ir::INT] }
    /// bid_init = 0
    /// name_of_params = ["x", "y", "z"]
    /// context = // omitted
    ///  ```
    ///
    /// Resulting IR after this function should be roughly follows:
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///       %l0:i32:x
    ///       %l1:i32:y
    ///       %l2:i32:z
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    ///     %b0:i0:unit = store %b0:p0:i32 %l0:i32*
    ///     %b0:i1:unit = store %b0:p1:i32 %l1:i32*
    ///     %b0:i2:unit = store %b0:p2:i32 %l2:i32*
    /// ```
    ///
    /// In particular, note that it is added to the local allocation list and store them to the
    /// initial phinodes.
    ///
    /// Note that the resulting IR is **a** solution. If you can think of a better way to
    /// translate parameters, feel free to do so.
    ///
    /// [foo]: https://github.com/kaist-cp/kecc-public/blob/main/examples/c/foo.c
    fn translate_parameter_decl(
        &mut self,
        signature: &ir::FunctionSignature,
        bid_init: ir::BlockId,
        name_of_params: &[String],
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        if signature.params.len() != name_of_params.len() {
            panic!("length of `parameters` and `name_of_params` must be same")
        } 
        for (i, (dtype, var)) in izip!(&signature.params, name_of_params).enumerate() {
            let value = Some(ir::Operand::register(
                ir::RegisterId::arg(bid_init, i),
                     dtype.clone()
            ));
            let _unused = self.translate_alloc(var.clone(), dtype.clone(), value, context)?;
        }

        Ok(())
    }

    fn add_phinodes(
        &mut self, 
        signature: &ir::FunctionSignature, 
        name_of_params: &[String], 
    ) -> Result<(), IrgenErrorMessage> {
        if signature.params.len() != name_of_params.len() {
            panic!("length of `parameters` and `name_of_params` must be same")
        } 
        for (_i, (dtype, var)) in izip!(&signature.params, name_of_params).enumerate() {
            let _unused = self.insert_phinodes(ir::Named::new(Some(var.clone()), dtype.clone()));
        }

        Ok(())
    }

    
}





#[inline]
fn name_of_declarator(declarator: &Declarator) -> String {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(identifier) => identifier.node.name.clone(),
        DeclaratorKind::Declarator(declarator) => name_of_declarator(&declarator.node),
    }
}

#[inline]
fn name_of_params_from_function_declarator(declarator: &Declarator) -> Option<Vec<String>> {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(_) => {
            name_of_params_from_derived_declarators(&declarator.derived)
        }
        DeclaratorKind::Declarator(next_declarator) => {
            name_of_params_from_function_declarator(&next_declarator.node)
                .or_else(|| name_of_params_from_derived_declarators(&declarator.derived))
        }
    }
}

#[inline]
fn name_of_params_from_derived_declarators(
    derived_decls: &[Node<DerivedDeclarator>],
) -> Option<Vec<String>> {
    for derived_decl in derived_decls {
        match &derived_decl.node {
            DerivedDeclarator::Function(func_decl) => {
                let name_of_params = func_decl
                    .node
                    .parameters
                    .iter()
                    .map(|p| name_of_parameter_declaration(&p.node))
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                return Some(name_of_params);
            }
            DerivedDeclarator::KRFunction(_kr_func_decl) => {
                // K&R function is allowed only when it has no parameter
                return Some(Vec::new());
            }
            _ => (),
        };
    }

    None
}

#[inline]
fn name_of_parameter_declaration(parameter_declaration: &ParameterDeclaration) -> Option<String> {
    let declarator = some_or!(parameter_declaration.declarator.as_ref(), return None);
    Some(name_of_declarator(&declarator.node))
}

#[inline]
fn is_valid_initializer(
    initializer: &Initializer,
    dtype: &ir::Dtype,
    structs: &HashMap<String, Option<ir::Dtype>>,
) -> bool {
    match initializer {
        Initializer::Expression(expr) => match dtype {
            ir::Dtype::Int { .. } | ir::Dtype::Float { .. } | ir::Dtype::Pointer { .. } => {
                match &expr.node {
                    Expression::Constant(_) => true,
                    Expression::UnaryOperator(unary) => matches!(
                        &unary.node.operator.node,
                        UnaryOperator::Minus | UnaryOperator::Plus
                    ),
                    _ => false,
                }
            }
            _ => false,
        },
        Initializer::List(items) => match dtype {
            ir::Dtype::Array { inner, .. } => items
                .iter()
                .all(|i| is_valid_initializer(&i.node.initializer.node, inner, structs)),
            ir::Dtype::Struct { name, .. } => {
                let name = name.as_ref().expect("struct should have its name");
                let struct_type = structs
                    .get(name)
                    .expect("struct type matched with `name` must exist")
                    .as_ref()
                    .expect("`struct_type` must have its definition");
                let fields = struct_type
                    .get_struct_fields()
                    .expect("`struct_type` must be struct type")
                    .as_ref()
                    .expect("`fields` must be `Some`");

                izip!(fields, items).all(|(f, i)| {
                    is_valid_initializer(&i.node.initializer.node, f.deref(), structs)
                })
            }
            _ => false,
        },
    }
}

#[inline]
fn is_invalid_structure(dtype: &ir::Dtype, structs: &HashMap<String, Option<ir::Dtype>>) -> bool {
    // When `dtype` is `Dtype::Struct`, `structs` has real definition of `dtype`
    if let ir::Dtype::Struct { name, fields, .. } = dtype {
        assert!(name.is_some() && fields.is_none());
        let name = name.as_ref().unwrap();
        let struct_type = some_or!(structs.get(name), return true);

        struct_type.is_none()
    } else {
        false
    }
}
