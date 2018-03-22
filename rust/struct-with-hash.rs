struct B {
  a:Vec<usize>,
  b:HashMap<usize,usize>}

use std::collections::HashMap;
fn main(){
  let mut thing = B{a:vec![], b:HashMap::new()};
  for i in 123..128 {
    let num = thing.a.len();
    let b = &mut thing.b;
    thing.a.push(i);
    b.insert(i,num);
  }
}
