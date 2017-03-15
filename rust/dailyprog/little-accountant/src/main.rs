// little accountant
// https://www.reddit.com/r/dailyprogrammer/comments/5wnbsi/20170228_challenge_304_easy_little_accountant/

extern crate csv;

fn main() {
    // let argv:Vec<String> = env::args().skip(1).collect();
    // println!("{:?}", argv);
    let mut reader = csv::Reader::from_file("data/journal.txt")
        .expect("unable to open file")
        .has_headers(true)
        .delimiter(b';');
    for line in reader.records() {
        if let Ok(v) = line { println!("{:?}", v) }
    }
}
