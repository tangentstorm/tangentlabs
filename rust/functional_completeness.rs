// demo of providing a partial implementation of a trait (FunctionallyComplete)
// given a few "axioms" in a smaller trait (AndXorNot)

trait FunctionallyComplete<T> {
  /* table */
  /* ----- */
  /*  0000 */ fn o(&mut self)-> T;                  // constant "false" (zero)
  /*  0001 */ fn and(&mut self, x:T, y:T)->T;   // x & y
  /*  0010 */ fn gt(&mut self, x:T, y:T)->T;    // x > y
  /*  0011 */ // this is just x, so we don't need a function
  /*  0100 */ fn lt(&mut self, x:T, y:T)->T;    // x < y
  /*  0101 */ // this is just y.
  /*  0110 */ fn xor(&mut self, x:T, y:T)->T;   // x ^ y
  /*  0111 */ fn or(&mut self, x:T, y:T)->T;    // x | y
  /*  1000 */ fn nor(&mut self, x:T, y:T)->T;   // ~(x|y)
  /*  1001 */ fn eq(&mut self, x:T, y:T)->T;    // x == y
  /*  1010 */ // not(y)
  /*  1011 */ fn gte(&mut self, x:T, y:T)->T;   // x >= y
  /*  1100 */ fn not(&mut self, x:T)->T;        // ~x
  /*  1101 */ fn lte(&mut self, x:T, y:T)->T;   // x <= y (x implies y)
  /*  1110 */ fn nand(&mut self, x:T, y:T)->T;  // ~(x&y)
  /*  1111 */ fn i(&mut self)->T;                   // constant "true" (one)
}

trait AndXorNot<T> {
  /*  0000 */ fn o(&self)-> T;                  // constant "false" (zero)
  /*  0001 */ fn and(&mut self, x:T, y:T)->T;   // x & y
  /*  0110 */ fn xor(&mut self, x:T, y:T)->T;   // x ^ y
  /*  1100 */ fn not(&mut self, x:T)->T;        // ~x
}

impl<T:Copy> FunctionallyComplete<T> for AndXorNot<T> {
  /*  0000 */ fn o(&mut self)->T { <Self as AndXorNot<T>>::o(self) }
  /*  0001 */ fn and(&mut self, x:T, y:T)->T { AndXorNot::and(self, x, y) }
  /*  0010 */ fn gt(&mut self, x:T, y:T)->T { let t = self.not(y); self.and(x, t) }
  /*  0011 x */
  /*  0100 */ fn lt(&mut self, x:T, y:T)->T { let t = self.not(x); self.and(t, y) }
  /*  0101 y */
  /*  0110 */ fn xor(&mut self, x:T, y:T)->T { AndXorNot::xor(self, x, y) }
  /*  0111 */ fn or(&mut self, x:T, y:T)->T {
    let t0 = self.and(x, y);
    let t1 = self.xor(x, y);
    self.xor(t1, t0) }
  /*  1000 */ fn nor(&mut self, x:T, y:T)->T { let t = self.or(x,y); self.not(t) }
  /*  1001 */ fn eq(&mut self, x:T, y:T)->T { let t = self.xor(x,y); self.not(t) }
  /*  1010 not(y) */
  /*  1011 */ fn gte(&mut self, x:T, y:T)->T { let t = self.lt(x,y); self.not(t) }
  /*  1100 */ fn not(&mut self, x:T)->T { AndXorNot::not(self, x) }
  /*  1101 */ fn lte(&mut self, x:T, y:T)->T { let t = self.gt(x,y); self.not(t) }
  /*  1110 */ fn nand(&mut self, x:T, y:T)->T{ let t = self.and(x,y); self.not(t) }
  /*  1111 */ fn i(&mut self)->T { let t = self.o(); self.not(t) } }


fn main() {}
