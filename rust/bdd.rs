/// binary decision diagrams in rust
/// there are better bdd implementations in rust out there.
/// i'm just doing this as a learning exercise.
use std::ops::Index;
use std::clone::Clone;

#[derive(PartialEq,Debug,Clone,Copy)]
struct BDDNode { nid:i32, var:i32, hi:i32, lo:i32 }
static O:BDDNode = BDDNode { nid: 0, var: 0, hi: 0, lo: 0 };
static I:BDDNode = BDDNode { nid:!0, var: 0, hi:!0, lo:!0 };

struct Base {
  count: u32, nodes: Vec<Box<BDDNode>>
}

impl Base {
  fn new() -> Base {
    Base { count: 1, nodes: vec![Box::new(O.clone())] }
  }
  fn vars(&mut self, names:&[&str]) -> Vec<Box<BDDNode>> {
    let mut result = vec!();
    for _n in names {
      let nid = self.count as i32;
      let node = BDDNode{ nid:nid, var: nid, hi:!0, lo:0 };
      self.nodes.push(Box::new(node));
      result.push(Box::new(node));
      self.count += 1;
    }
    result
  }
}

impl Index<i32> for Base {
  type Output = BDDNode;
  fn index(&self, ix:i32) -> &BDDNode {
    if ix < 0 { if ix == !0 { &I } else { panic!("TODO: not()") }}
    else { &self.nodes[ix as usize] }
  }
}


#[test]
fn test_basics(){
  let base = Base::new();
  assert_eq!(1, base.count);
  assert_eq!(O, base[ 0]);
  assert_eq!(I, base[!0]);
}

#[test]
fn test_vars(){
  let mut base = Base::new();
  let mut ab = base.vars(&["a","b"]);
  let base = base;
  if let (Some(b), Some(a), None) = (ab.pop(), ab.pop(), ab.pop()) {
    assert_eq!(3, base.count);
    assert_eq!(*a, base[1]);   assert_eq!(*b, base[2]);
    assert_eq!(O.nid, a.lo, "a.lo->O"); assert_eq!(I.nid, a.hi, "a.hi->I");
    assert_eq!(O.nid, b.lo, "b.lo->O"); assert_eq!(I.nid, b.hi, "b.hi->I");
    assert_eq!(1, a.nid)
  } else { panic!("expected exactly two variables.") }
}

fn main() {
  // let mut base = Base::new();
  println!("hello. use rustc --test for now.");
}
