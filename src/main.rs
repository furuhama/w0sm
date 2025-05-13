use w0sm::{Vm, VmError};

fn main() -> Result<(), VmError> {
    println!("w0sm: A simple Wasm VM");

    let wat = r#"
        (module
            (global $g0 (mut i32) (i32.const 10))
            (func $main
                (global.get $g0)
                (i32.const 5)
                (i32.add)
                (global.set $g0)
                (global.get $g0)
                (return)
            )
        )
    "#;

    let mut vm = Vm::from_wat(wat).expect("Failed to parse WAT");
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
