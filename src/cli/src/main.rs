fn main() {
    // input file name from command line argument

    // collect command line arguments
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <input_file>", args[0]);
        std::process::exit(1);
    }
    for arg in args.iter() {
        println!("Arg: {}", arg);
    }
    // file name is the first argument
    let input_file = &args[1];
    let content = std::fs::read_to_string(input_file).expect("Failed to read input file");
    println!("Input file: {}", input_file);

    let modules = front::parse::str_parse_modules(&content).unwrap();
    let mut glenv = front::resolver::GlobalEnvironment::default();
    for module in modules {
        eprintln!("Module: {:?}", module);
        let res = glenv.new_module(&module);
        for log in glenv.logs() {
            match log {
                either::Either::Left(der) => {
                    println!("Derivation \n{}", der);
                }
                either::Either::Right(log) => {
                    println!("Log: \n{}", log);
                }
            }
        }
        match res {
            Ok(_) => {
                continue;
            }
            Err(err) => {
                // exit with error
                eprintln!("Error: {:?}", err);
                std::process::exit(1);
            }
        }
    }
}
