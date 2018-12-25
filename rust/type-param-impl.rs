/// this is a prototype of how to arrange the types in bex::bdd.
///
/// the basic idea is that a Base has a Worker, and a Worker has a State,
/// State and Worker are both traits, and I want to be able to construct
/// a Base with a single call to Base::new(), possibly parameterized by
/// the State and Worker types.
///
/// This implementation is very close to what I want.
///
/// It is still a tiny bit unpleasant, though, because I have to say
/// 'Base<S, W<S>>' instead of just 'Base<S, W>' or 'Base<W<S>>'
///
use std::marker::PhantomData;

// the end goal: Base should have a Worker. (think database, not "base class")

struct Base<S:StateT, W:WorkerT<S>>{
  phantom: PhantomData<S>,
  worker:W }

impl<S:StateT,W:WorkerT<S>> Base<S,W> {
  fn new(x:u32)->Self { Base{ worker:W::new(x), phantom: PhantomData } }
  fn val(&self)->u32 { self.worker.val() }}


// WorkerT is just a trait

trait WorkerT<S:StateT> : Sized {
  fn new(x:u32)->Self;
  fn val(&self)->u32; }


// Any actual Worker implementation has a State, but we don't want Base to know about it.

struct Worker<S:StateT> { state:S }

impl<S:StateT> WorkerT<S> for Worker<S> {
  fn new(x:u32)->Self { Worker{ state: S::new(x) } }
  fn val(&self)->u32 { return self.state.val() }}


// StateT is just another trait.

trait StateT : Sized {
  fn new(val:u32)->Self;
  fn val(&self)->u32; }

// State is an implementation of StateT:

struct State { val: u32 }
impl StateT for State {
  fn new(val:u32)->Self { State { val }}
  fn val(&self)->u32 { return self.val } }


#[test]
fn test_main() {
  let a = Base::<State, Worker<State>>::new(123);
  let b = Base::<State, Worker<State>>::new(256);
  assert_eq!(123, a.val());
  assert_eq!(256, b.val()); }

// default base type
type DefaultBase = Base<State, Worker<State>>;

#[test]
fn test_default() {
  let a = DefaultBase::new(123);
  let b = DefaultBase::new(256);
  assert_eq!(123, a.val());
  assert_eq!(256, b.val()); }
