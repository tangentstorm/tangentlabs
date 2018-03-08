    // simple example of pattern matching on Rc<enum>

    use std::rc::Rc;
    use std::fmt;

    type Cell = Rc<RawCell>;

    #[derive(Debug, Clone)]
    enum RawCell { Nil, Item(i32), Cons(Cell, Cell) }
    use RawCell::*;

    fn cell(x:RawCell)->Cell { Cell::new(x) }
    fn item(x:i32)-> Cell { cell(Item(x)) }
    fn cons(a:Cell, b:Cell)-> Cell { cell(Cons(a,b)) }

    impl fmt::Display for RawCell {
      fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {

        // !! is there any way to get rid of these & in the
        match *self {

          Nil => write!(f, "()"),                              // should only happen if we directly display nil.

          Item(x) => write!(f, "{}", x),                       // single item. easy.

          Cons(ref x, ref y) => {                              // walk through and display the entire list:

            // always show '(x'
            write!(f, "({}", x).unwrap();                       // !! how to detect and propagate the errors correctly?

            // intermediate values are space-separated:
            let mut tail = y;
            while let &Cons(ref h, ref t) = tail.as_ref() {
              write!(f, " {}", h).unwrap();                     // !!same question.
              tail = t
            }

            // final value at end of list is either ')' (normal list) or '. y)' for "dotted pair"
            match *(tail.as_ref()) {
              Nil => write!(f, ")"),
              Item(n) => write!(f, ". {})", n),

                                                                // !! not sure how i'm supposed to handle errors here:
              ref xxx => { eprintln!("got to end of list and found something weird: {:?}", xxx); Err(fmt::Error) }
            }
          }
        }
      }
    }

    fn main() {
      let nil = cell(Nil);
      let ls1 = cons(item(1), cons(item(2), nil.clone()));
      let ls2 = cons(item(3), nil.clone());
      println!("refcount for nil (before): {}", Rc::strong_count(&nil));
      let pretty = format!("{}", cons(ls1.clone(), cons(ls1, ls2)));
      assert_eq!("((1 2) (1 2) 3)", pretty);
      println!("refcount for nil (after): {}", Rc::strong_count(&nil));
    }
