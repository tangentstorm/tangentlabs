// (a start on) a simple forth-like thing in rust
use std::io;
use std::io::Write;

fn read()->String {
  let mut buf = String::new();
  print!("> ");
  io::stdout().flush()                 .expect("couldn't flush stdout.");
  io::stdin().read_line(&mut buf)      .expect("failed to read line.");
  buf}

fn swap(data: &mut Vec<i32>) {
  let p = data.len()-1;
  if p > 1 {
    let t = data[p-1];
    data[p-1]=data[p];
    data[p]=t;  }}

fn show(data: &Vec<i32>) {
  for x in data { print!("{} ", x); } println!("");}

fn main() {
  let mut data: Vec<i32> = Vec::new();
  'main: loop {
    let line = read();
    for word in line.split_whitespace() {
      match word {
        "?" => show(&data),
        "q" => break 'main,
        "swap" => swap(&mut data),
        _ => if let Ok(w)=i32::from_str_radix(word, 10) { data.push(w); }
             else { println!("[{}]", word) }}}}}
