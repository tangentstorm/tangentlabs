// hackerrank problem:
// https://www.hackerrank.com/contests/w30/challenges/find-the-minimum-number
//
// basically: generate an 'expression' to find the minimum of 2 ≤ n ≤ 50 ints.
// example:       4 -> min(int, min(int, min(int, int)))
fn mins(i:u8)->String {
    if i==1 { format!("int") } // <shrug> this is what they ask for.
    else { format!("min(int, {})", mins(i-1)) }
}

fn main(){
    let mut s = String::new();
    std::io::stdin().read_line(&mut s)  .expect("failed to read input line.");
    let i:u8 = s.trim().parse()         .expect("failed to parse number");
    println!("{}", mins(i));
}
