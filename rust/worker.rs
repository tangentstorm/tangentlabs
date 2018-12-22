// ----------------------------------------------------------------------
// a working Worker implementation.
// ----------------------------------------------------------------------
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;
// ----------------------------------------------------------------------

/// Intents are what we're telling the workers to do.
#[derive(PartialEq,Debug)]
enum Intent { Add(u32, u32) }
struct IntentMsg { id:usize, msg:Intent }

/// Events are the messages coming back from the workers.
/// I want a better name for this. I wanted to call it Result,
/// but didn't want it confused with std::result::Result
#[derive(PartialEq,Debug)]
enum Event { Sum(u32) }
struct EventMsg { id:usize, msg:Event }

// ----------------------------------------------------------------------

fn work(tx:Sender<EventMsg>, rx:Receiver<IntentMsg>) {
  loop {
    match rx.recv().expect("aaaaah!") {
      IntentMsg{ id, msg } => {
        println!("Worker got msg {}: {:?}", id, msg);
        match msg {
          Intent::Add(x,y) => {
            tx.send(EventMsg{id, msg:Event::Sum(x+y)})
              .expect("I TOLD you you'd regret not writing a better error message someday.");
          }} }} }}

// ----------------------------------------------------------------------

/// A Master controls a bunch of workers. More importantly, you can ask
/// it to do something by calling intent, and it does the work of waiting
/// for the answer from you.
///
/// For context, this is intended for an application where every request
/// (or "Intent") involves a very large graph structure. There's only ever
/// intent at a time, but there may be many worker threads working on it.
struct Master {
  /// receives messages from the workers
  rx: Receiver<EventMsg>,
  /// send messages to myself (so we can put them back in the queue if they're
  /// not the ones we're looking for. (otherwise, we'd need to store them
  /// somewhere else)
  me: Sender<EventMsg>,
  id: usize,
  workers: Vec<Sender<IntentMsg>> }

impl Master {
  fn new()->Master {
    let (me, rx) = channel::<EventMsg>();
    let mut workers = vec![];
    for _ in 0..2 {
      let (tx, rx) = channel::<IntentMsg>();
      let me_clone = me.clone();
      thread::spawn(|| { work(me_clone, rx) });
      workers.push(tx); }
    Master{ me, rx, id:0, workers}}

  fn run(&mut self, x:Intent)->Event {
    let w:usize = self.id % self.workers.len();
    self.workers[w].send(IntentMsg{ id:self.id, msg:x }).expect("ugh");
    let mut result:Option<Event> = None;
    while result.is_none() {
      let EventMsg{id, msg} = self.rx.recv().expect("oh no!");
      println!("Master got msg {}: {:?}", id, msg);
      if id==self.id { result = Some(msg) }
      else { self.me.send(EventMsg{id, msg}).expect(":/"); }}
    self.id += 1;
    result.expect("got invalid result?") } }


// ----------------------------------------------------------------------

fn main() {
  let mut m = Master::new();
  assert_eq!(m.run(Intent::Add(2, 3)), Event::Sum(5));
  assert_eq!(m.run(Intent::Add(3, 5)), Event::Sum(8)); }
