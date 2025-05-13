use std::vec::Vec;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    I32(i32),
    I64(i64),
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
}
