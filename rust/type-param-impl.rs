/// this is a prototype of how to arrange the types in bex::bdd.

// the end goal: Base should have a Worker. (think database, not "base class")

struct Base<W:WorkerT> { worker:W }

impl<W:WorkerT> Base<W> {
  fn new(worker:W)->Self { Base{ worker } }
  fn val(&self)->u32 { self.worker.val() }}


// WorkerT is just a trait

trait WorkerT {
  fn val(&self)->u32; }


// Any actual Worker implementation has a State, but we don't want Base to know about it.

struct Worker<S:StateT> { state:S }

impl<S:StateT> Worker<S> {
  fn new(state:S)->Self { Worker{ state } }}

impl<S:StateT> WorkerT for Worker<S> {
  fn val(&self)->u32 { return self.state.val() }}


// StateT is just another trait.

trait StateT { fn val(&self)->u32; }

// State is an implementation of StateT:

struct State { val: u32 }
impl State {
  fn new(val:u32)->Self { State { val }} }

impl StateT for State {
  fn val(&self)->u32 { return self.val } }


fn main() {
  let b = Base::new(Worker::new(State::new(123)));
  assert_eq!(123, b.val()); }
