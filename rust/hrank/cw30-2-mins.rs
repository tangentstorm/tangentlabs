// hackerrank problem:
// https://www.hackerrank.com/contests/w30/challenges/find-the-minimum-number
//
// basically: generate an 'expression' to find the minimum of 2 ≤ n ≤ 50 ints.
// example:       4 -> min(int, min(int, min(int, int)))
// except i do:   4 -> min(min(int, int), min(int, int))
// (i.e., i do n*log2(n) comparisons rather than n).
//
// ... except i don't really, because hackerrank only accepts the O(n) version.
fn mins(i:u8)->String {
    if i==1 { format!("int") } // <shrug> this is what they ask for.
    // else { let h0 = i>>1; let h1 = i-h0; format!("min({}, {})", mins(h0), mins(h1)) }
    else { format!("min(int, {})", mins(i-1)) }     // dumb O(n) version
}

fn main(){
    let mut s = String::new();
    std::io::stdin().read_line(&mut s)  .expect("failed to read input line.");
    let i:u8 = s.trim().parse()         .expect("failed to parse number");
    println!("{}", mins(i));
}
