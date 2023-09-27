# thread-local-drop

This library supports the controlled and deliberate dropping and **_extraction_** of thread-local values, even before the corresponding threads terminate. Computations that use thread-local variables and need to be able to extract the thread-local values can benefit from this library.

It is not literally possible to force thread-local variables themselves to be dropped before their threads terminate, but we can accomplish our goal by using thread-local variables of a holder type that encapsulates the values of interest. We can take the encapsulated values of holders that have not already been dropped and then drop those values. The values _extracted_ from the the thread-local variables are accumulated and made available to the library's caller.

## Core concepts

The core concepts in this framework are the `Control` and `Holder` structs.

[`Holder`] wraps a thread-local value, ensures each thread is registered with `Control` when the thread-local variable is used, and de-registers from `Control` when the thread terminates and the `Holder` instance is dropped.

[`Control`] keeps track of the registered threads, and contains an accumulation operation `op` and an accumulated value `acc`. The accumulated value is updated by applying `op` to each thread-local data value and `acc` when the thread-local value is dropped.

`Control` also provides methods to read and update the thread-local variable, a method [`ensure_tls_dropped`](Control::ensure_tls_dropped) (usually called from the main thread) to ensure all thread-local values have been deregistered/dropped, and methods ([`with_acc`](Control::with_acc) and [`take_acc`](Control::take_acc)) to access the accumulated value.

## Usage pattern

Here's an outline of how this little framework can be used:

```rust
//! Simple example usage of [`thread_local_drop`].

use std::thread::{self, ThreadId};
use thread_local_drop::{Control, Holder};

// Define your data type, e.g.:
type Data = i32;

// Define your accumulated value type. It can be `()` if you don't need an accumulator.
type AccValue = i32;

// Define your thread-local:
thread_local! {
    static MY_TL: Holder<Data, AccValue> = Holder::new(|| 0);
}

// Define your accumulation operation.
// You can use the closure `|_, _, _| ()` inline in the `Control` constructor if you don't need an accumulator.
fn op(data: Data, acc: &mut AccValue, _: &ThreadId) {
    *acc += data;
}

// Create a function to update the thread-local value:
fn update_tl(value: Data, control: &Control<Data, AccValue>) {
    control.with_tl_mut(&MY_TL, |data| {
        *data = value;
    });
}

fn main() {
    let control = Control::new(0, op);

    update_tl(1, &control);

    thread::scope(|s| {
        s.spawn(|| {
            update_tl(10, &control);
        });
    });

    // Call this after all other threads registered with `Control` have been joined.
    control.ensure_tls_dropped();

    control
        .with_acc(|acc| println!("accumulated={}", acc));
}
```

## Other examples

See another example at [`examples/map_accumulator.rs`](https://github.com/pvillela/rust-thread-local-drop/blob/main/examples/map_accumulator.rs).
