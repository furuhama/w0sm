use crate::wat_parser::{WatNode, WatParser};
use std::collections::HashMap;
use std::vec::Vec;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    I32(i32),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ValueType {
    I32,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    Nop,
    Return,
    I32Const(i32),
    I32Add,
    GlobalGet(usize),
    GlobalSet(usize),
}

#[derive(Debug, Error)]
pub enum VmError {
    #[error("Stack underflow")]
    StackUnderflow,
    #[error("Type mismatch")]
    TypeMismatch,
    #[error("Invalid instruction pointer")]
    InvalidInstructionPointer,
    #[error("Not yet implemented: {0}")]
    NotImplemented(String),
    #[error("Invalid global index")]
    InvalidGlobalIndex,
    #[error("Attempt to modify immutable global")]
    ImmutableGlobal,
}

#[derive(Debug, Clone)]
pub struct Global {
    #[allow(unused)]
    value_type: ValueType,
    mutable: bool,
}

#[derive(Debug, Clone)]
pub struct GlobalInstance {
    global: Global,
    value: Value,
}

#[derive(Debug)]
pub struct Vm {
    stack: Vec<Value>,
    instructions: Vec<Instruction>,
    pc: usize,
    globals: Vec<GlobalInstance>,
}

impl Vm {
    pub fn new(instructions: Vec<Instruction>) -> Self {
        Vm {
            stack: Vec::new(),
            instructions,
            pc: 0,
            globals: Vec::new(),
        }
    }

    // this does not have its own instruction, because global variables are defined in the module.
    // this is defined for debug purpose so far.
    pub fn add_global(
        &mut self,
        value_type: ValueType,
        mutable: bool,
        initial_value: Value,
    ) -> usize {
        let global = Global {
            value_type,
            mutable,
        };
        let instance = GlobalInstance {
            global,
            value: initial_value,
        };
        self.globals.push(instance);
        self.globals.len() - 1
    }

    pub fn get_global(&self, index: usize) -> Result<Value, VmError> {
        self.globals
            .get(index)
            .map(|instance| instance.value.clone())
            .ok_or(VmError::InvalidGlobalIndex)
    }

    pub fn set_global(&mut self, index: usize, value: Value) -> Result<(), VmError> {
        let instance = self
            .globals
            .get_mut(index)
            .ok_or(VmError::InvalidGlobalIndex)?;

        if !instance.global.mutable {
            return Err(VmError::ImmutableGlobal);
        }

        instance.value = value;
        Ok(())
    }

    pub fn run(&mut self) -> Result<Option<Value>, VmError> {
        while self.pc < self.instructions.len() {
            let instruction = self
                .instructions
                .get(self.pc)
                .ok_or(VmError::InvalidInstructionPointer)?
                .clone();

            // for debug
            // println!("Executing @{}: {:?}", self.pc, instruction);

            match instruction {
                Instruction::I32Const(val) => {
                    self.stack.push(Value::I32(val));
                    self.pc += 1;
                }
                Instruction::I32Add => {
                    let rhs = self.pop_i32()?;
                    let lhs = self.pop_i32()?;
                    self.stack.push(Value::I32(lhs.wrapping_add(rhs)));
                    self.pc += 1;
                }
                Instruction::GlobalGet(index) => {
                    let value = self.get_global(index)?;
                    self.stack.push(value);
                    self.pc += 1;
                }
                Instruction::GlobalSet(index) => {
                    let value = self.stack.pop().ok_or(VmError::StackUnderflow)?;
                    self.set_global(index, value)?;
                    self.pc += 1;
                }
                Instruction::Nop => {
                    self.pc += 1;
                }
                Instruction::Return => {
                    return Ok(self.stack.pop());
                }
                #[allow(unreachable_patterns)]
                _ => return Err(VmError::NotImplemented(format!("{:?}", instruction))),
            }
        }
        Ok(self.stack.pop())
    }

    fn pop_i32(&mut self) -> Result<i32, VmError> {
        match self.stack.pop() {
            Some(Value::I32(val)) => Ok(val),
            Some(_) => Err(VmError::TypeMismatch),
            None => Err(VmError::StackUnderflow),
        }
    }

    pub fn from_wat(wat: &str) -> Result<Self, String> {
        let mut parser = WatParser::new(wat);
        let ast = parser.parse()?;
        let mut vm = Vm::new(vec![]);
        let mut instructions = Vec::new();
        let mut global_indices = HashMap::new();

        if let WatNode::Instruction(name, nodes) = ast {
            if name == "module" {
                for node in nodes {
                    if let WatNode::Instruction(subname, subnodes) = node {
                        match subname.as_str() {
                            "global" => {
                                let mut var_name = None;
                                let mut mutable = false;
                                let mut value_type = ValueType::I32;
                                let mut initial_value = Value::I32(0);
                                for sub in subnodes {
                                    match sub {
                                        WatNode::Identifier(s) if s.starts_with('$') => {
                                            var_name = Some(s.clone())
                                        }
                                        WatNode::Instruction(iname, ivals) if iname == "mut" => {
                                            mutable = true;
                                            if let WatNode::Identifier(s) = &ivals[0] {
                                                if s == "i32" {
                                                    value_type = ValueType::I32;
                                                }
                                            }
                                        }
                                        WatNode::Identifier(s) if s == "i32" => {
                                            value_type = ValueType::I32
                                        }
                                        WatNode::Instruction(iname, ivals)
                                            if iname == "i32.const" =>
                                        {
                                            if let WatNode::Number(n) = ivals[0] {
                                                initial_value = Value::I32(n);
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                                let idx = vm.add_global(value_type, mutable, initial_value);
                                if let Some(name) = var_name {
                                    global_indices.insert(name.clone(), idx);
                                }
                            }
                            "func" => {
                                for instr in subnodes {
                                    match instr {
                                        WatNode::Instruction(iname, ivals) => {
                                            match iname.as_str() {
                                                "i32.const" => {
                                                    if let WatNode::Number(n) = &ivals[0] {
                                                        instructions
                                                            .push(Instruction::I32Const(*n));
                                                    }
                                                }
                                                "i32.add" => instructions.push(Instruction::I32Add),
                                                "global.get" => {
                                                    if let WatNode::Identifier(gname) = &ivals[0] {
                                                        if let Some(idx) =
                                                            global_indices.get(gname.as_str())
                                                        {
                                                            instructions
                                                                .push(Instruction::GlobalGet(*idx));
                                                        } else {
                                                            return Err(format!(
                                                                "Unknown global: {}",
                                                                gname
                                                            ));
                                                        }
                                                    }
                                                }
                                                "global.set" => {
                                                    if let WatNode::Identifier(gname) = &ivals[0] {
                                                        if let Some(idx) =
                                                            global_indices.get(gname.as_str())
                                                        {
                                                            instructions
                                                                .push(Instruction::GlobalSet(*idx));
                                                        } else {
                                                            return Err(format!(
                                                                "Unknown global: {}",
                                                                gname
                                                            ));
                                                        }
                                                    }
                                                }
                                                "nop" => instructions.push(Instruction::Nop),
                                                "return" => instructions.push(Instruction::Return),
                                                _ => {
                                                    return Err(format!(
                                                        "Unknown instruction: {}",
                                                        iname
                                                    ));
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        vm.instructions = instructions;
        Ok(vm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i32_add() {
        let instructions = vec![
            Instruction::I32Const(1),
            Instruction::I32Const(2),
            Instruction::I32Add,
        ];
        let mut vm = Vm::new(instructions);
        let result = vm.run();
        assert!(result.is_ok(), "Execution failed: {:?}", result.err());
        assert_eq!(result.unwrap(), Some(Value::I32(3)));
        assert!(vm.stack.is_empty(), "Stack should be empty after run");
    }

    #[test]
    fn test_global_variables() {
        let mut vm = Vm::new(vec![]);

        // グローバル変数の追加
        let global_index = vm.add_global(
            ValueType::I32,
            true,           // ミュータブル
            Value::I32(42), // 初期値
        );

        // グローバル変数の値を取得
        let value = vm.get_global(global_index).unwrap();
        assert_eq!(value, Value::I32(42));

        // グローバル変数の値を設定
        vm.set_global(global_index, Value::I32(100)).unwrap();
        let value = vm.get_global(global_index).unwrap();
        assert_eq!(value, Value::I32(100));
    }

    #[test]
    fn test_immutable_global() {
        let mut vm = Vm::new(vec![]);

        // イミュータブルなグローバル変数の追加
        let global_index = vm.add_global(
            ValueType::I32,
            false,          // イミュータブル
            Value::I32(42), // 初期値
        );

        // イミュータブルなグローバル変数の値を変更しようとするとエラー
        let result = vm.set_global(global_index, Value::I32(100));
        assert!(result.is_err());
        assert!(matches!(result.err().unwrap(), VmError::ImmutableGlobal));
    }

    #[test]
    fn test_global_instructions() {
        let mut vm = Vm::new(vec![]);

        // グローバル変数の追加
        let global_index = vm.add_global(ValueType::I32, true, Value::I32(42));

        // グローバル変数を使用する命令の実行
        let instructions = vec![
            Instruction::GlobalGet(global_index),
            Instruction::I32Const(1),
            Instruction::I32Add,
            Instruction::GlobalSet(global_index),
            Instruction::GlobalGet(global_index),
        ];

        vm.instructions = instructions;
        let result = vm.run().unwrap();
        assert_eq!(result, Some(Value::I32(43)));

        // グローバル変数の値が更新されていることを確認
        let value = vm.get_global(global_index).unwrap();
        assert_eq!(value, Value::I32(43));
    }

    #[test]
    fn test_i32_add_return() {
        let instructions = vec![
            Instruction::I32Const(5),
            Instruction::I32Const(10),
            Instruction::I32Add,
            Instruction::Return,
            Instruction::I32Const(99), // unreachable
        ];
        let mut vm = Vm::new(instructions);
        let result = vm.run();
        assert!(result.is_ok(), "Execution failed: {:?}", result.err());
        assert_eq!(result.unwrap(), Some(Value::I32(15)));
    }

    #[test]
    fn test_empty_instructions() {
        let instructions = vec![];
        let mut vm = Vm::new(instructions);
        let result = vm.run();
        assert!(result.is_ok(), "Execution failed: {:?}", result.err());
        assert_eq!(result.unwrap(), None);
    }

    #[test]
    fn test_stack_underflow() {
        let instructions = vec![Instruction::I32Add];
        let mut vm = Vm::new(instructions);
        let result = vm.run();
        assert!(result.is_err());
        assert!(matches!(result.err().unwrap(), VmError::StackUnderflow));
    }

    #[test]
    fn test_from_wat_simple() {
        let wat = r#"
            (module
                (func $add
                    (i32.const 1)
                    (i32.const 2)
                    (i32.add)
                    (return)
                )
            )
        "#;
        let vm = Vm::from_wat(wat).unwrap();
        let mut vm = vm;
        let result = vm.run().unwrap();
        assert_eq!(result, Some(Value::I32(3)));
    }

    #[test]
    fn test_from_wat_with_globals() {
        let wat = r#"
            (module
                (global $x (mut i32) (i32.const 42))
                (global $y i32 (i32.const 100))
                (func $test
                    (global.get $x)
                    (i32.const 1)
                    (i32.add)
                    (global.set $x)
                    (global.get $x)
                    (return)
                )
            )
        "#;
        let vm = Vm::from_wat(wat).unwrap();
        let mut vm = vm;
        let result = vm.run().unwrap();
        assert_eq!(result, Some(Value::I32(43)));
    }

    #[test]
    fn test_from_wat_immutable_global_error() {
        let wat = r#"
            (module
                (global $x i32 (i32.const 42))
                (func $test
                    (global.get $x)
                    (i32.const 1)
                    (i32.add)
                    (global.set $x)
                    (return)
                )
            )
        "#;
        let vm = Vm::from_wat(wat).unwrap();
        let mut vm = vm;
        let result = vm.run();
        assert!(result.is_err());
        assert!(matches!(result.err().unwrap(), VmError::ImmutableGlobal));
    }

    #[test]
    fn test_from_wat_unknown_global() {
        let wat = r#"
            (module
                (func $test
                    (global.get $unknown)
                    (return)
                )
            )
        "#;
        let result = Vm::from_wat(wat);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown global"));
    }

    #[test]
    fn test_from_wat_unknown_instruction() {
        let wat = r#"
            (module
                (func $test
                    (unknown_instruction)
                    (return)
                )
            )
        "#;
        let result = Vm::from_wat(wat);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown instruction"));
    }
}
