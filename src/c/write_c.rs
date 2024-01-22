use lang_c::ast::*;
use lang_c::span::Node;

use core::{ops::Deref, panic};
use std::io::{Result, Write};

use crate::{write_base::*, AssertSupported};

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
    }
}

impl<T: WriteString> WriteString for Node<T> {
    fn write_string(&self) -> String {
        self.node.write_string()
    }
}

impl<T: WriteString> WriteString for Box<T> {
    fn write_string(&self) -> String {
        self.deref().write_string()
    }
}

impl<T: WriteString> WriteString for &T {
    fn write_string(&self) -> String {
        (*self).write_string()
    }
}

impl<T: WriteString> WriteString for Option<T> {
    fn write_string(&self) -> String {
        if let Some(this) = self {
            this.write_string()
        } else {
            "".to_string()
        }
    }
}

impl WriteString for String {
    fn write_string(&self) -> String {
        self.to_string()
    }
}

impl WriteLine for TranslationUnit {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        for node in &self.0 {
            node.write_line(indent, write)?;
            writeln!(write)?;
        }
        Ok(())
    }
}

impl WriteLine for ExternalDeclaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Self::Declaration(decl) => decl.write_line(indent, write),
            Self::FunctionDefinition(fdef) => fdef.write_line(indent, write),
            Self::StaticAssert(_) => panic!(),
        }
    }
}

impl WriteLine for Declaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "{};", self.write_string())?;
        Ok(())
    }
}

impl WriteString for Declaration {
    fn write_string(&self) -> String {
        (&self.specifiers, &self.declarators).write_string()
    }
}

impl WriteString for (&Vec<Node<DeclarationSpecifier>>, &Vec<Node<InitDeclarator>>) {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.0
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.1
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl WriteLine for FunctionDefinition {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(
            write,
            "{} ",
            (&self.specifiers, &self.declarator).write_string()
        )?;

        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for Statement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Statement::Labeled(label) => {
                label.write_line(indent, write)?;
                Ok(())
            }
            Statement::Compound(block_items) => {
                writeln!(write, "{{")?;
                for block_item in block_items {
                    block_item.write_line(indent + 1, write)?;
                }
                write_indent(indent, write)?;
                writeln!(write, "}}")?;
                Ok(())
            }
            Statement::Expression(expression) => {
                if let Some(expr) = expression {
                    writeln!(write, "{};", expr.write_string())
                } else {
                    writeln!(write, ";")
                }
            }
            Statement::If(if_statement) => {
                if_statement.write_line(indent, write)?;
                Ok(())
            }
            Statement::Switch(switch_statement) => {
                switch_statement.write_line(indent, write)?;
                Ok(())
            }
            Statement::While(while_statement) => {
                while_statement.write_line(indent, write)?;
                Ok(())
            }
            Statement::DoWhile(do_while_statement) => {
                do_while_statement.write_line(indent, write)?;
                Ok(())
            }
            Statement::For(for_statement) => {
                for_statement.write_line(indent, write)?;
                Ok(())
            }
            Statement::Goto(_identifier) => panic!(),
            Statement::Continue => {
                writeln!(write, "continue;")?;
                Ok(())
            }
            Statement::Break => {
                writeln!(write, "break;")?;
                Ok(())
            }
            Statement::Return(expression) => {
                if let Some(expr) = expression {
                    writeln!(write, "return {};", expr.write_string())
                } else {
                    writeln!(write, "return;")
                }
            }
            Statement::Asm(_asm_statement) => panic!(),
        }
    }
}

impl WriteLine for DoWhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(write, "do ")?;
        self.statement.write_line(indent, write)?;
        write_indent(indent, write)?;
        writeln!(write, "while ({});", self.expression.write_string())?;
        Ok(())
    }
}

impl WriteLine for LabeledStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(write, "{}: ", self.label.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteString for Label {
    fn write_string(&self) -> String {
        match self {
            Self::Default => "default".to_string(),
            Self::Case(case) => format!("case {}", case.write_string()),
            _ => panic!(),
        }
    }
}

impl WriteLine for SwitchStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(write, "switch ({}) ", self.expression.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for WhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(write, "while ({}) ", self.expression.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for IfStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(write, "if ({}) ", self.condition.write_string())?;
        self.then_statement.write_line(indent, write)?;
        if let Some(elstatement) = &self.else_statement {
            write_indent(indent, write)?;
            write!(write, "else ")?;
            elstatement.write_line(indent, write)?;
        }
        Ok(())
    }
}

impl WriteLine for ForStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(
            write,
            "for ({}; {}; {}) ",
            self.initializer.write_string(),
            self.condition.write_string(),
            self.step.write_string()
        )?;

        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteString for ForInitializer {
    fn write_string(&self) -> String {
        match self {
            ForInitializer::Empty => "".to_string(),
            ForInitializer::Expression(expression) => expression.write_string(),
            ForInitializer::Declaration(declaration) => declaration.write_string(),
            ForInitializer::StaticAssert(_) => panic!(),
        }
    }
}

impl WriteString for Expression {
    fn write_string(&self) -> String {
        match self {
            Expression::Identifier(identifier) => identifier.write_string(),
            Expression::Constant(constant) => constant.write_string(),
            Expression::StringLiteral(_) => panic!(),
            Expression::GenericSelection(_) => panic!(),
            Expression::Member(member_expression) => member_expression.write_string(),
            Expression::Call(call_expression) => call_expression.write_string(),
            Expression::CompoundLiteral(_) => panic!(),
            Expression::SizeOfTy(size_of_ty) => size_of_ty.write_string(),
            Expression::SizeOfVal(size_of_val) => size_of_val.write_string(),
            Expression::AlignOf(align_of) => align_of.write_string(),
            Expression::UnaryOperator(unary_operator) => unary_operator.write_string(),
            Expression::Cast(cast_expression) => cast_expression.write_string(),
            Expression::BinaryOperator(binary_operator) => binary_operator.write_string(),
            Expression::Conditional(conditional_expression) => {
                conditional_expression.write_string()
            }
            Expression::Comma(expressions) => {
                format!(
                    "({})",
                    expressions
                        .iter()
                        .map(WriteString::write_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Expression::OffsetOf(_) => panic!(),
            Expression::VaArg(_) => panic!(),
            Expression::Statement(_) => panic!(),
        }
    }
}

impl WriteString for MemberExpression {
    fn write_string(&self) -> String {
        format!(
            "{}{}{}",
            self.expression.write_string(),
            self.operator.write_string(),
            self.identifier.write_string()
        )
    }
}

impl WriteString for MemberOperator {
    fn write_string(&self) -> String {
        match self {
            Self::Direct => ".".to_string(),
            Self::Indirect => "->".to_string(),
        }
    }
}

impl WriteString for SizeOfVal {
    fn write_string(&self) -> String {
        format!("sizeof({})", self.0.write_string())
    }
}

impl WriteString for SizeOfTy {
    fn write_string(&self) -> String {
        format!("sizeof({})", self.0.write_string())
    }
}

impl WriteString for CastExpression {
    fn write_string(&self) -> String {
        format!(
            "({}) {}",
            self.type_name.write_string(),
            self.expression.write_string()
        )
    }
}

impl WriteString for ConditionalExpression {
    fn write_string(&self) -> String {
        format!(
            "({} ? {} : {})",
            self.condition.write_string(),
            self.then_expression.write_string(),
            self.else_expression.write_string()
        )
    }
}
impl WriteString for CallExpression {
    fn write_string(&self) -> String {
        format!(
            "({})({})",
            self.callee.write_string(),
            self.arguments
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}
impl WriteString for UnaryOperatorExpression {
    fn write_string(&self) -> String {
        match self.operator.node {
            UnaryOperator::PostDecrement => format!("({}--)", self.operand.write_string()),
            UnaryOperator::PostIncrement => format!("({}++)", self.operand.write_string()),
            UnaryOperator::PreDecrement => format!("(--{})", self.operand.write_string()),
            UnaryOperator::PreIncrement => format!("(++{})", self.operand.write_string()),
            UnaryOperator::Address => format!("(&{})", self.operand.write_string()),
            UnaryOperator::Indirection => format!("(*{})", self.operand.write_string()),
            UnaryOperator::Plus => format!("(+{})", self.operand.write_string()),
            UnaryOperator::Minus => format!("(-{})", self.operand.write_string()),
            UnaryOperator::Complement => format!("(~{})", self.operand.write_string()),
            UnaryOperator::Negate => format!("(!{})", self.operand.write_string()),
        }
    }
}

impl WriteString for AlignOf {
    fn write_string(&self) -> String {
        format!("_Alignof({})", self.0.write_string())
    }
}

impl WriteString for TypeName {
    fn write_string(&self) -> String {
        (&self.specifiers, &self.declarator).write_string()
    }
}

impl WriteString for (&Vec<Node<SpecifierQualifier>>, &Option<Node<Declarator>>) {
    fn write_string(&self) -> String {
        if let Some(decl) = self.1 {
            format!(
                "{} {}",
                self.0
                    .iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(" "),
                decl.write_string()
            )
        } else {
            self.0
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" ")
        }
    }
}

impl WriteString for SpecifierQualifier {
    fn write_string(&self) -> String {
        match self {
            SpecifierQualifier::TypeSpecifier(type_specifier) => type_specifier.write_string(),
            SpecifierQualifier::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
            SpecifierQualifier::Extension(_) => panic!(),
        }
    }
}

impl WriteString for BinaryOperatorExpression {
    fn write_string(&self) -> String {
        if self.operator.node == BinaryOperator::Index {
            format!("({})[{}]", self.lhs.write_string(), self.rhs.write_string())
        } else {
            format!(
                "(({}) {} ({}))",
                self.lhs.write_string(),
                self.operator.write_string(),
                self.rhs.write_string()
            )
        }
    }
}

impl WriteString for BinaryOperator {
    fn write_string(&self) -> String {
        match self {
            BinaryOperator::Index => "[]".to_string(),
            BinaryOperator::Multiply => "*".to_string(),
            BinaryOperator::Divide => "/".to_string(),
            BinaryOperator::Modulo => "%".to_string(),
            BinaryOperator::Plus => "+".to_string(),
            BinaryOperator::Minus => "-".to_string(),
            BinaryOperator::ShiftLeft => "<<".to_string(),
            BinaryOperator::ShiftRight => ">>".to_string(),
            BinaryOperator::Less => "<".to_string(),
            BinaryOperator::Greater => ">".to_string(),
            BinaryOperator::LessOrEqual => "<=".to_string(),
            BinaryOperator::GreaterOrEqual => ">=".to_string(),
            BinaryOperator::Equals => "==".to_string(),
            BinaryOperator::NotEquals => "!=".to_string(),
            BinaryOperator::BitwiseAnd => "&".to_string(),
            BinaryOperator::BitwiseXor => "^".to_string(),
            BinaryOperator::BitwiseOr => "|".to_string(),
            BinaryOperator::LogicalAnd => "&&".to_string(),
            BinaryOperator::LogicalOr => "||".to_string(),
            BinaryOperator::Assign => "=".to_string(),
            BinaryOperator::AssignMultiply => "*=".to_string(),
            BinaryOperator::AssignDivide => "/=".to_string(),
            BinaryOperator::AssignModulo => "%=".to_string(),
            BinaryOperator::AssignPlus => "+=".to_string(),
            BinaryOperator::AssignMinus => "-=".to_string(),
            BinaryOperator::AssignShiftLeft => "<<=".to_string(),
            BinaryOperator::AssignShiftRight => ">>=".to_string(),
            BinaryOperator::AssignBitwiseAnd => "&=".to_string(),
            BinaryOperator::AssignBitwiseXor => "^=".to_string(),
            BinaryOperator::AssignBitwiseOr => "|=".to_string(),
        }
    }
}

impl WriteLine for BlockItem {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.assert_supported();
        write_indent(indent, write)?;
        match self {
            Self::Declaration(decl) => writeln!(write, "{};", decl.write_string()),
            Self::StaticAssert(_) => todo!(),
            Self::Statement(statement) => statement.write_line(indent, write),
        }
    }
}

impl WriteString for (&Vec<Node<DeclarationSpecifier>>, &Node<Declarator>) {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.0
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.1.write_string()
        )
    }
}

impl WriteString for InitDeclarator {
    fn write_string(&self) -> String {
        if let Some(init) = &self.initializer {
            format!(
                "{} = {}",
                self.declarator.write_string(),
                init.write_string()
            )
        } else {
            self.declarator.write_string()
        }
    }
}

impl WriteString for Declarator {
    fn write_string(&self) -> String {
        assert!(self.extensions.is_empty());
        (&self.kind, &self.derived).write_string()
    }
}

impl WriteString for (&Node<DeclaratorKind>, &Vec<Node<DerivedDeclarator>>) {
    fn write_string(&self) -> String {
        let mut decl = String::new();
        let mut count = 0;
        for item in self.1 {
            if let DerivedDeclarator::Pointer(_) = item.node {
                decl.insert_str(0, item.write_string().as_str());
                count += 1;
            }
        }
        format!(
            "{}{}{}",
            decl,
            self.0.write_string(),
            self.1
                .iter()
                .skip(count)
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join("")
        )
    }
}

impl WriteString for DeclaratorKind {
    fn write_string(&self) -> String {
        match self {
            Self::Abstract => "".to_string(),
            Self::Identifier(ident) => ident.write_string(),
            Self::Declarator(decl) => format!("({})", decl.write_string()),
        }
    }
}

impl WriteString for DerivedDeclarator {
    fn write_string(&self) -> String {
        match self {
            DerivedDeclarator::Pointer(qualifiers) => {
                format!(
                    "*{}",
                    qualifiers
                        .iter()
                        .map(WriteString::write_string)
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            DerivedDeclarator::Array(array_declarator) => {
                format!("[{}]", array_declarator.write_string())
            }
            DerivedDeclarator::Function(function_declarator) => function_declarator.write_string(),
            DerivedDeclarator::KRFunction(identifier) => {
                assert!(identifier.is_empty());
                "()".to_string()
            }
            DerivedDeclarator::Block(_) => todo!(),
        }
    }
}

impl WriteString for PointerQualifier {
    fn write_string(&self) -> String {
        match self {
            Self::TypeQualifier(qualifier) => qualifier.write_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for ArrayDeclarator {
    fn write_string(&self) -> String {
        self.assert_supported();
        match &self.size {
            ArraySize::VariableExpression(expr) => expr.write_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for FunctionDeclarator {
    fn write_string(&self) -> String {
        self.assert_supported();
        format!(
            "({})",
            self.parameters
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl WriteString for (&Vec<Node<DeclarationSpecifier>>, &Option<Node<Declarator>>) {
    fn write_string(&self) -> String {
        if let Some(decl) = self.1 {
            (self.0, decl).write_string()
        } else {
            self.0
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" ")
        }
    }
}
impl WriteString for ParameterDeclaration {
    fn write_string(&self) -> String {
        self.assert_supported();
        (&self.specifiers, &self.declarator).write_string()
    }
}

impl WriteString for DeclarationSpecifier {
    fn write_string(&self) -> String {
        match self {
            DeclarationSpecifier::StorageClass(storage_class_specifier) => {
                storage_class_specifier.write_string()
            }
            DeclarationSpecifier::TypeSpecifier(type_specifier) => type_specifier.write_string(),
            DeclarationSpecifier::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
            DeclarationSpecifier::Function(_) => todo!(),
            DeclarationSpecifier::Alignment(_) => todo!(),
            DeclarationSpecifier::Extension(_) => todo!(),
        }
    }
}

impl WriteString for TypeSpecifier {
    fn write_string(&self) -> String {
        match self {
            TypeSpecifier::Void => "void".to_string(),
            TypeSpecifier::Char => "char".to_string(),
            TypeSpecifier::Short => "short".to_string(),
            TypeSpecifier::Int => "int".to_string(),
            TypeSpecifier::Long => "long".to_string(),
            TypeSpecifier::Float => "float".to_string(),
            TypeSpecifier::Double => "double".to_string(),
            TypeSpecifier::Signed => "signed".to_string(),
            TypeSpecifier::Unsigned => "unsigned".to_string(),
            TypeSpecifier::Bool => "bool".to_string(),
            TypeSpecifier::Complex => todo!(),
            TypeSpecifier::Atomic(_) => todo!(),
            TypeSpecifier::Struct(struct_type) => struct_type.write_string(),
            TypeSpecifier::Enum(_) => todo!(),
            TypeSpecifier::TypedefName(identifier) => identifier.write_string(),
            TypeSpecifier::TypeOf(_) => todo!(),
            TypeSpecifier::TS18661Float(_) => todo!(),
        }
    }
}

impl WriteString for StructType {
    fn write_string(&self) -> String {
        format!(
            "{}{}{}",
            self.kind.write_string(),
            self.identifier.write_string(),
            self.declarations.write_string()
        )
    }
}

impl WriteString for Vec<Node<StructDeclaration>> {
    fn write_string(&self) -> String {
        format!(
            "{{{};}}",
            self.iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join("; ")
        )
    }
}

impl WriteString for StructDeclaration {
    fn write_string(&self) -> String {
        match self {
            Self::Field(field) => field.write_string(),
            Self::StaticAssert(_) => panic!(),
        }
    }
}

impl WriteString for StructField {
    fn write_string(&self) -> String {
        (&self.specifiers, &self.declarators).write_string()
    }
}

impl WriteString for (&Vec<Node<SpecifierQualifier>>, &Vec<Node<StructDeclarator>>) {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.0
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.1
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
        )
    }
}

impl WriteString for StructDeclarator {
    fn write_string(&self) -> String {
        assert!(self.bit_width.is_none());
        self.declarator.write_string()
    }
}

impl WriteString for StructKind {
    fn write_string(&self) -> String {
        match self {
            Self::Struct => "struct ".to_string(),
            Self::Union => "union ".to_string(),
        }
    }
}
impl WriteString for AlignmentSpecifier {
    fn write_string(&self) -> String {
        todo!()
    }
}

impl WriteString for Identifier {
    fn write_string(&self) -> String {
        self.name.to_string()
    }
}

impl WriteString for TypeQualifier {
    fn write_string(&self) -> String {
        match self {
            TypeQualifier::Const => "const".to_string(),
            _ => todo!(),
        }
    }
}

impl WriteLine for StringLiteral {
    fn write_line(&self, _indent: usize, write: &mut dyn Write) -> Result<()> {
        for string in self {
            writeln!(write, r#""{}","#, string)?;
        }
        Ok(())
    }
}
impl WriteString for Constant {
    fn write_string(&self) -> String {
        match self {
            Constant::Integer(integer) => integer.write_string(),
            Constant::Float(float) => float.write_string(),
            Constant::Character(character) => character.to_string(),
        }
    }
}

impl WriteString for Integer {
    fn write_string(&self) -> String {
        let mut integer = String::new();
        match self.base {
            IntegerBase::Binary => integer.push_str("0b"),
            IntegerBase::Octal => integer.push('0'),
            IntegerBase::Hexadecimal => integer.push_str("0x"),
            _ => {}
        }

        integer.push_str(&self.number);
        if self.suffix.unsigned {
            integer.push('U');
        }
        match self.suffix.size {
            IntegerSize::Long => integer.push('l'),
            IntegerSize::LongLong => integer.push_str("ll"),
            _ => {}
        }
        integer
    }
}

impl WriteString for Float {
    fn write_string(&self) -> String {
        let mut float = String::new();
        if self.base == FloatBase::Hexadecimal {
            float.push_str("0x");
        }
        float.push_str(&self.number);
        match self.suffix.format {
            FloatFormat::Float => float.push('f'),
            FloatFormat::LongDouble => float.push_str("ld"),
            FloatFormat::TS18661Format(_) => panic!(),
            _ => {}
        }
        float
    }
}

impl WriteString for FunctionSpecifier {
    fn write_string(&self) -> String {
        match self {
            FunctionSpecifier::Inline => "inline".to_string(),
            FunctionSpecifier::Noreturn => "_Noreturn".to_string(),
        }
    }
}

impl WriteLine for FunctionSpecifier {
    fn write_line(&self, _indent: usize, write: &mut dyn Write) -> Result<()> {
        write!(write, "{}", self.write_string())?;
        Ok(())
    }
}

impl WriteString for StorageClassSpecifier {
    fn write_string(&self) -> String {
        match self {
            StorageClassSpecifier::Typedef => "typedef".to_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for Initializer {
    fn write_string(&self) -> String {
        match self {
            Initializer::Expression(expression) => expression.write_string(),
            Initializer::List(initializer_list) => {
                format!(
                    "{{{}}}",
                    initializer_list
                        .iter()
                        .map(WriteString::write_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

impl WriteString for InitializerListItem {
    fn write_string(&self) -> String {
        assert!(self.designation.is_empty());
        self.initializer.write_string()
    }
}
