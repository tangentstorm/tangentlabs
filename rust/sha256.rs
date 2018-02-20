// sha256 implementation in rust

type Block = Vec<u32>;
type Hash  = Vec<u32>;

type Tup8 = (u32,u32,u32,u32, u32,u32,u32,u32);

fn tup8(v:&Vec<u32>) -> Tup8 {
  (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7])}

fn xor(x:u32, y:u32) -> u32 { x^y }
fn ror(x:u32, y:u32) -> u32 { x.rotate_right(y) }
fn add(x:u32, y:u32)->u32 { x.wrapping_add(y) }
fn reduce(f:(fn(u32,u32)->u32), xs:Vec<u32>, z:u32) -> u32 {
  let mut r = z; for x in xs { r = f(r, x) } r }

fn xr(rots:Vec<u32>, x:u32) -> u32 {
  reduce(xor, rots.into_iter().map(|r| ror(x,r)).collect(), 0) }

fn zum(xs:Vec<u32>) -> u32 { reduce(add, xs, 0) }
fn ch(x:u32, y:u32, z:u32)->u32 { (x&y) ^ (!x&z) }
fn mj(x:u32, y:u32, z:u32)->u32 { (x&y) ^ (x&z) ^ (y&z) }
fn sum0(x:u32)->u32 { xr(vec![ 2, 13, 22], x) }
fn sum1(x:u32)->u32 { xr(vec![ 6, 11, 25], x) }
fn sig0(x:u32)->u32 { xr(vec![ 7, 18], x) ^ (x>>3) }
fn sig1(x:u32)->u32 { xr(vec![17, 19], x) ^ (x>>10) }

const K:[u32;64] = [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2];

const H0:[u32;8] = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];


fn make_w(block:Block)->Vec<u32> {
  assert_eq!(16, block.len());
  let mut w = block.clone();
  for i in 16..64 {
    let w2=w[i-2]; let w7=w[i-7]; let w15=w[i-15]; let w16=w[i-16];
    w.push(zum(vec![sig1(w2), w7, sig0(w15), w16])) }
  w }

fn compress(block:Block, h0:&Hash)->Vec<u32> {
  let (mut a, mut b, mut c, mut d,
       mut e, mut f, mut g, mut h) = tup8(h0);
  let w = make_w(block);
  for i in 0..64 {
    let t1 = zum(vec![h, sum1(e), ch(e,f,g), K[i], w[i]]);
    let t2 = add(sum0(a), mj(a,b,c));
    h=g; g=f; f=e; e=add(d,t1); d=c; c=b; b=a; a=add(t1,t2) }
  vec![a,b,c,d,e,f,g,h] }

fn blocks(bits:&Vec<u32>) -> Vec<Vec<u32>> {
  // !! since bits is always a vector of u32
  //    we stray a bit from actual sha256 here.
  let mut all = bits.clone();
  let pad = 16-(all.len()+3) % 16; // 3=2 for size + 1 for end bit
  all.push(1_u32 << 31); // single bit marking end of text
  for _ in 0..pad { all.push(0) }
  all.push(0); all.push(bits.len() as u32 * 32); // size marker
  assert_eq!(0, all.len() % 16, "internal error: bit length is screwy...");
  let mut res = vec![]; let mut i = 0; // now break into 512-bit chunks:
  while i < all.len() { res.push(all[i..i+16].to_vec()); i+=16 }
  res }


fn zipwith(f:fn(u32,u32)->u32, xs:&Vec<u32>, ys:&Vec<u32>) -> Vec<u32> {
  let mut i = 0; let mut r = vec![];
  while (i<xs.len()) && (i<ys.len()) { r.push(f(xs[i],ys[i])); i+=1 }
  r }

fn sha256(bits:&Vec<u32>) -> Hash {
  let mut r = H0.to_vec();
  for block in blocks(bits) {
    r = zipwith(add, &r, &compress(block, &r)) }
  r }


// -------------------------------------------------------------

#[test] fn test_xr(){  assert_eq!(15, xr(vec![0,1,2,3], 8)) }

#[test] fn test_prims(){
  let a=0b00001111_u32; let b=0b00110011_u32; let c=0b01010101_u32;
             //0123456789abcdef0123456789abcdef
  assert_eq!(0b01111000000000000000000000000000, ror(a,5), "ror");
  assert_eq!(0b00001010, c>>3, ">>");
  assert_eq!(0b01010011, ch(a,b,c), "ch");
  assert_eq!(0b00010111, mj(a,b,c), "mj");
  assert_eq!(0b01000010, add(a,b), "add"); }

#[test] fn test_blocks(){
  let bs = blocks(&vec![0xaabbccdd]);
  assert_eq!(bs[0], vec![
    0xaabbccdd, 0x80000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000020]); }

#[test] fn test_w(){
  let block = blocks(&vec![0xaabbccdd]);
  assert_eq!(make_w(block[0].clone()), vec![
    0xaabbccdd, 0x80000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000020,
    0xbbbbecdd, 0x80140000, 0x8bdb8451, 0x80205508,
    0xb2800277, 0x20055801, 0x01598f30, 0xc2c4a231,
    0x769256e4, 0x5149ec63, 0xe1d36616, 0x7e29936d,
    0xfff7300b, 0xfd1e29e5, 0x81081ffe, 0x9fbac256,
    0x2a2933e7, 0xeea67e24, 0xddd17bde, 0x6aadb515,
    0x9282d719, 0x1125ae1b, 0x25b11add, 0xa33eedca,
    0xcb08a936, 0xc30ca4fe, 0x3ff2d8bb, 0x9b80dcf0,
    0xa68268ff, 0x836cb6cb, 0xabee1ef3, 0xc0489513,
    0x8543ec83, 0x7fab1bdf, 0x5008f323, 0x946f14e7,
    0xdd5188f3, 0x1e27f88f, 0x159d79fd, 0x8a8f762c,
    0x2b50514d, 0x30b68146, 0xbc630f3f, 0x7afcfa3e,
    0x55db427b, 0xf0e772ff, 0x1ab2bf3f, 0x2f37412c]);}

#[test] fn test_sha256(){
  assert_eq!(sha256(&vec![0;8]), vec![
    0x66687aad, 0xf862bd77, 0x6c8fc18b, 0x8e9f8e20,
    0x08971485, 0x6ee233b3, 0x902a591d, 0x0d5f2925]);}

// -------------------------------------------------------------

fn main() {
  for x in sha256(&vec![0;8]) { print!("{:x}", x) }
  println!(""); }
