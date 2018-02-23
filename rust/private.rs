// example of how private members work

mod private {
  #[derive(Debug)]
  pub struct Data {hidden: u32}
  impl Data {
    pub fn new(x:u32) -> Data { Data{hidden:x} }}}

fn main() {
  use private::Data;

  // let data = Data{hidden:123}; // NOPE! 'field "hidden" is private.'
  let data = Data::new(123);

  println!("{:?}", data)}
