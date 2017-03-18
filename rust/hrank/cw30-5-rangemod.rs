// hackerrank codeweek 30 #5: range modular queries

fn read_ints()->Vec<usize> {
    let mut line = String::new();
    let mut ints = Vec::new();
    std::io::stdin().read_line(&mut line).expect("failed to read line.");
    for tok in line.split_whitespace() {
        let u:usize = tok.parse().expect("malformed integer:");
        ints.push(u);
    }
    (ints)
}

fn main() {
    let nq = read_ints();
    let a = read_ints();
    for _ in 0..nq[1] {
        let lrxy = read_ints();
        let (left,right,x,y) = (lrxy[0], lrxy[1], lrxy[2], lrxy[3]);
        let mut c = 0;
        for i in left .. (right+1)  {
            if a[i] % x == y { c+= 1; }
        }
        println!("{}", c);
    }
}
