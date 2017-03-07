// (a start on) a simple forth-like thing in rust
use std::io;
use std::io::Write;

fn read()->String {
    let mut buf = String::new();
    print!("> ");
    io::stdout().flush()                 .expect("couldn't flush stdout.");
    io::stdin().read_line(&mut buf)      .expect("failed to read line.");
    (buf)
}

fn main() {
    let mut data: Vec<i32> = Vec::new();
    let line = read();
    // for ch in line.chars() { println!("{}", ch); }
    for word in line.split_whitespace() {
        match word {
            _     => if let Ok(w)=i32::from_str_radix(word, 10) { data.push(w); }
                     else { println!("[{}]", word) },
        }
    }
    println!("done with execution. stack contents:");
    for x in data { print!("{} ", x); } println!("");
}
