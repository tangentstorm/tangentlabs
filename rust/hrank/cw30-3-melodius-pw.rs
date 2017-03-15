// program to generate all 'melodius' passwords of a given length

fn cv(i:u32)->Vec<String> {
    let mut res = Vec::new();
    let chs = "bcdfghjklmnpqrstvwxz".chars();
    if i == 1 { for c in chs { res.push(format!("{}", c)) }}
    else { for c in chs { for s in vc(i-1) { res.push(format!("{}{}", c, s)) }}}
    return res;
}

fn vc(i:u32)->Vec<String> {
    let mut res = Vec::new();
    let chs = "aeiou".chars();
    if i == 1 { for c in chs { res.push(format!("{}", c)) }}
    else { for c in chs { for s in cv(i-1) { res.push(format!("{}{}", c, s)) }}}
    return res;
}


fn main() {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).expect("no input given");
    let n:u32 = line.trim().parse().expect("expected a positive integer");
    for s in cv(n) { println!("{}", s); }
    for s in vc(n) { println!("{}", s); }
}
