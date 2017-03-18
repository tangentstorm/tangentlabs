// hackerrank problem:
//

fn read_pair()->(usize,usize) {
    let mut line = String::new();
    let mut ints = Vec::new();
    std::io::stdin().read_line(&mut line).expect("failed to read line.");
    for tok in line.split_whitespace() {
        let u:usize = tok.parse().expect("malformed integer:");
        ints.push(u);
    }
    (ints[0],ints[1])
}


fn main() {
    let (k, n) = read_pair();
    let mut x = Vec::new();
    let mut w = Vec::new();
    for _ in 0..k {
        let (xi, wi) = read_pair();
        x.push(xi); w.push(wi);
    }
    println!("{:?}", x);

    // position all the piles at the bottom
    let mut p = Vec::new();
    for i in 0..n { p.push(x[i]); }
    println!("{:?}", p);

    // calculate the cost of this arrangement
    // start at bottom, and mutliply weight of each pole by distance to last item
    let mut b = 0;  // p[b] is the currenty 'base' pile that we're moving to
    let mut t = 0;  // total cost
    for i in 0..k {
        if b+1 < n && x[i] >= p[b+1] { b+=1; }
        let c = w[i] * (x[i] - p[b]);
        t += c;
        println!("{} | {:2} {:2} {:4}", x[i], w[i], x[i]-p[b], t);
    }
    println!("t: {}", t);
}
