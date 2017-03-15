// hackerrank problem:
// https://www.hackerrank.com/contests/w30/challenges/candy-replenishing-robot

fn read_ints()->Vec<u32> {
    let mut line = String::new();
    let mut ints = Vec::new();
    std::io::stdin().read_line(&mut line).expect("failed to read line.");
    for tok in line.split_whitespace() {
        let u:u32 = tok.parse().expect("malformed integer:");
        ints.push(u);
    }
    (ints)
}

fn main() {
    let nt = read_ints();
    let mut b = nt[0];                        // current number of candies in bowl
    let mut a = 0;                            // total candies added
    for (i, &ci) in read_ints().iter().enumerate() {
        if i+1 >= nt[1] as usize { break };   // if party is over, we're done
        b -= ci;                              // otherwise, remove ci candies
        if b < 5 { a += nt[0]-b; b=nt[0]; }   // refill bowl and note how many added
    }
    println!("{}", a);
}
