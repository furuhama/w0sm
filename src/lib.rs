use std::vec::Vec;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    I32(i32),
    I64(i64),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    Nop,
    Return,
    I32Const(i32),
    I32Add,
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
}

pub struct Vm {
    stack: Vec<Value>,
    instructions: Vec<Instruction>,
    pc: usize,
}

impl Vm {
    pub fn new(instructions: Vec<Instruction>) -> Self {
        Vm {
            stack: Vec::new(),
            instructions,
            pc: 0,
        }
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
                Instruction::Nop => {
                    self.pc += 1;
                }
                Instruction::Return => {
                    return Ok(self.stack.pop());
                }
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
