//! # thread-local-drop
//!
//! This library supports the **_extraction_** of thread-local values that have been dropped. Computations that use thread-local variables and need to be able to extract the thread-local values can benefit from this library.
//!
//! ## Core concepts
//!
//! The core concepts in this framework are the `Control` and `Holder` structs.
//!
//! [`Holder`] wraps a thread-local value, ensures each thread is registered with `Control` when the thread-local variable is used, and de-registers from `Control` when the thread terminates and the `Holder` instance is dropped.
//!
//! [`Control`] keeps track of the registered threads, and contains an accumulation operation `op` and an accumulated value `acc`. The accumulated value is updated by applying `op` to each thread-local data value and `acc` when the thread-local value is dropped.
//!
//! `Control` provides methods to read and update the thread-local variable and methods ([`with_acc`](Control::with_acc) and [`take_acc`](Control::take_acc)) to access the accumulated value.
//!
//! ## Usage pattern
//!
//! Here's an outline of how this little framework can be used:
//!
//! ```rust
//! use std::thread::{self, ThreadId};
//! use thread_local_drop::joined::{Control, Holder};
//!
//! // Define your data type, e.g.:
//! type Data = i32;
//!
//! // Define your accumulated value type. It can be `()` if you don't need an accumulator.
//! type AccValue = i32;
//!
//! // Define your thread-local:
//! thread_local! {
//!     static MY_TL: Holder<Data, AccValue> = Holder::new(|| 0);
//! }
//!
//! // Define your accumulation operation.
//! // You can use the closure `|_, _, _| ()` inline in the `Control` constructor if you don't need an accumulator.
//! fn op(data: Data, acc: &mut AccValue, _: &ThreadId) {
//!     *acc += data;
//! }
//!
//! // Create a function to update the thread-local value:
//! fn update_tl(value: Data, control: &Control<Data, AccValue>) {
//!     control.with_tl_mut(&MY_TL, |data| {
//!         *data = value;
//!     });
//! }
//!
//! fn main() {
//!     let control = Control::new(0, op);
//!
//!     thread::scope(|s| {
//!         let h = s.spawn(|| {
//!             update_tl(10, &control);
//!         });
//!         h.join().unwrap();
//!     });
//!
//!     {
//!         // Acquire `control`'s lock.
//!         let lock = control.lock();
//!
//!         control.with_acc(&lock, |acc| println!("accumulated={}", acc));
//!     }
//! }
//! ```
//!
//! ## Other examples
//!
//! See another example at [`examples/map_accumulator.rs`](https://github.com/pvillela/rust-thread-local-drop/blob/main/examples/map_accumulator.rs).

pub mod forced;
pub mod joined;
