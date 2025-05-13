use w0sm::{Instruction, Vm, VmError};

fn main() -> Result<(), VmError> {
    println!("w0sm: A simple Wasm VM");

    let instructions = vec![
        Instruction::I32Const(10),
        Instruction::I32Const(20),
        Instruction::I32Add,
        // Instruction::Return,
    ];

    let mut vm = Vm::new(instructions);

    println!("Running VM...");
    match vm.run() {
        Ok(Some(result)) => println!("Execution finished. Result: {:?}", result),
        Ok(None) => println!("Execution finished with no return value."),
        Err(e) => {
            eprintln!("Error during execution: {}", e);
            return Err(e);
        }
    }

    Ok(())
}
