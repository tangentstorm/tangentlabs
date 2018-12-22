//! This is a stripped-down prototype of a worker system that doesn't actually
//! (and can't possibly) work. I was thinking of workers as being a struct,
//! but realize now it makes no sense.
//!
//! I just had to unlearn a way of thinking, and so I wrote this out
//! to help me clarify my thoughts.
//!
//! reddit thread: https://www.reddit.com/r/learnrust/comments/a8isd9
//! ------------------------------------------------------------------------------------
//!
//! I've been programming for many years, but I can probably count on
//! one hand the number of times I've actually used threads
//! directly. Instead, I've always favored asynchronous event
//! loops. In that world, I often model workers as objects with a step
//! method. (And then run them in a container that could choose to do
//! threading if it wanted.)
//!
//! I like rust's promise of taming threads, so I decided to give it a
//! try, but I brought that "worker is an object" mentality with me.
//!
//! I sketched out a short little mockup of the scheme I had in mind:
//! a Master struct would own a Vec<&Worker>, and Worker would be
//! another struct that encapsulates all its state like a good little
//! OOP class.
//!
//! Then I wrote the following type signature and realized this scheme
//! simply makes no sense:
//!
//! impl Worker { fn work(&mut self) {
//!    /* infinite message-handling //! loop */ }
//! }
//!
//! It's the &mut self that breaks it:
//!
//! If work needs to modify any field in self, then self must be mut
//! or &mut... But then there can't be a reference to it in the
//! Vec<&Worker>, either because it would require moving while
//! borrowed (mut) or because you can't have both mutable and
//! non-mutable references to the same object (&mut).
//!
//! So: okay, no big deal, just replace the Vec<Worker> with a
//! Vec<Sender<WorkMsg>>. Then the Worker can own a Receiver<WorkMsg>
//! and it can own a Sender<T> for returning results to the Manager.
//!
//! That would be fine, but now who owns the Worker?
//!
//! Well, it should be owned by the thread.
//!
//! But then what's the point, other than forcing me to type self
//! everywhere?
//!
//! Long story short, the function running in the thread can just own
//! all that state as a local variable, and that's why workers are
//! functions (or closures) instead of structs.
//
// anyway, here's the code I did write, even though it's pointless now:
// ----------------------------------------------------------------------
use std::sync::mpsc::{channel, Sender, Receiver, SendError};
use std::result::Result;
use std::fmt::Debug;
use std::cmp::PartialEq;
// ----------------------------------------------------------------------

/// Intents are what we're telling the workers to do.
#[derive(PartialEq,Debug)]
enum Intent { Add(u32, u32) }
struct IntentMsg { id:u32, msg:Intent }

/// Events are the messages coming back from the workers.
/// I want a better name for this. I wanted to call it Result,
/// but didn't want it confused with std::result::Result
#[derive(PartialEq,Debug)]
enum Event { Sum(u32) }
struct EventMsg { id:u32, msg:Event }

type SendResult = std::result::Result<(), SendError<IntentMsg>>;

// ----------------------------------------------------------------------

/// A worker does work in its own separate thread.

struct Worker {
  /// so worker can talk to the master
  tx: Sender<EventMsg>,
  /// channel for talking to the worker's own thread
  me: Sender<IntentMsg>,
  /// the receiving end of the worker's channel
  rx: Receiver<IntentMsg> }

impl Worker {
  fn new(tx:Sender<EventMsg>)->Worker {
    let (me, rx) = channel::<IntentMsg>();
    Worker{ tx, me, rx } }

  fn send(&self, id:u32, msg:Intent)->SendResult {
    self.me.send(IntentMsg{ id, msg }) }

  fn work(mut self) { }

}

// ----------------------------------------------------------------------

/// A Master controls a bunch of workers. More importantly, you can ask
/// it to do something by calling intent, and it does the work of waiting
/// for the answer from you.
///
/// For context, this is intended for an application where every request
/// (or "Intent") involves a very large graph structure. There's only ever
/// intent at a time, but there may be many worker threads working on it.
struct Master<'a> {
  /// receives messages from the workers
  rx: Receiver<EventMsg>,
  /// send messages to myself (so we can put them back in the queue if they're
  /// not the ones we're looking for. (otherwise, we'd need to store them
  /// somewhere else)
  me: Sender<EventMsg>,
  id: u32,
  workers: Vec<&'a Worker> }

impl<'a> Master<'a> {
  fn new()->Master<'static> {
    let (me, rx) = channel::<EventMsg>();
    let workers = vec![&Worker::new(me.clone()),
                       &Worker::new(me.clone())];

    for &w in workers { w.work() }
    Master{ me, rx, id:0, workers}}

  fn run(&mut self, x:Intent)->Event {
    self.id += 1;
    match x { Intent::Add(x,y) => Event::Sum(x+y) }
  }
}


// ----------------------------------------------------------------------

fn main() {
  let mut m = Master::new();
  assert_eq!(m.run(Intent::Add(2, 3)), Event::Sum(5));
  assert_eq!(m.run(Intent::Add(3, 5)), Event::Sum(8));
}
