/// binary decision diagrams in rust
/// there are better bdd implementations in rust out there.
/// i'm just doing this as a learning exercise.. 
use std::ops::Index;
use std::clone::Clone;

#[derive(PartialEq,Debug,Clone,Copy)]
struct BDDNode { var:i32, hi:i32, lo:i32 }
static O:BDDNode = BDDNode { var: 0, hi:0, lo:0 };
static I:BDDNode = BDDNode { var: 0, hi:-1, lo:-1 };



struct Base {
  count: u32,
  nodes: Vec<Box<BDDNode>>
}

impl Base {
  fn new() -> Base {
    Base { count: 1, nodes: vec![Box::new(O.clone())] }
  }
  fn vars(&mut self, names:&[&str]) -> Vec<Box<BDDNode>> {
    let mut result = vec!();
    for n in names {
      self.count += 1;
      let node = BDDNode{ var: self.count as i32, hi:1, lo:0 };
      self.nodes.push(Box::new(node));
      result.push(Box::new(node))
    }
    result
  }
}

impl Index<i32> for Base {
  type Output = BDDNode;
  fn index(&self, ix:i32) -> &BDDNode {
    const ii:i32 = !0;
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
  if let (Some(b), Some(a), None) = (ab.pop(), ab.pop(), ab.pop()) {
//    assert_eq!(3, base.count.clone());
//    assert_eq!(*a, base[1]); 
//    assert_eq!(*b, base[2]); }
  } else { panic!("expected exactly two variables.") }
/*
        
        self.assertEquals(b, self.base[2])
        self.assertEquals(o, a.lo); self.assertEquals(o, b.lo)
        self.assertEquals(l, a.hi); self.assertEquals(l, b.hi)
        self.assertEquals(1, a.nid)
*/
}

fn main() {
  println!("hello?");
}
