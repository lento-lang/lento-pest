use std::io::Write;

use lento::parser::{parse_program, print_pairs};

fn read_line(prompt: Option<&str>) -> String {
    if let Some(prompt) = prompt {
        print!("{}", prompt);
        std::io::stdout().flush().unwrap();
    }
    let mut input = String::new();
    match std::io::stdin().read_line(&mut input) {
        Ok(_) => input.trim_end().to_string(),
        Err(_) => String::from(""),
    }
}

fn main() {
    loop {
        let input = read_line(Some(">>> "));
        match parse_program(&input) {
            Ok(pairs) => print_pairs(pairs),
            Err(e) => println!("Error: {}", e),
        }
    }
}
