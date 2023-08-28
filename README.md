# thread-local-drop

Support for ensuring that destructors are run on thread-local variables after the threads terminate, as well as support for accumulating the thread-local values using an accumulation operation.

## Core concepts

The core concepts in this framework are the `Control` and `Holder` structs.

**`Holder`** wraps a thread-local value, ensures each thread is registered with `Control` when the thread-local variable is used, and de-registers from `Control` when the thread terminates and the `Holder` instance is dropped.

**`Control`** keeps track of the registered threads, and contains an accumulation operation `op` and an accumulated value `acc`. The accumulated value is updated by applying `op` to each thread-local data value and `acc` when the thread-local value is dropped.

`Control` also provides methods to read and update the thread-local variable, a method `ensure_tls_dropped` (called from the main thread) to ensure all thread-local values have been deregistered/dropped, and a method to retrieve the accumulated value (see above).

An important consideration and a key reason for this library is that, while thread-local variables are eventually dropped after the thread terminates, execution of the `drop` method on thread-locals is asynchronous to the main thread and the main thread may terminate before all the thread-local destructors are executed. So, the `Control` method `ensure_tls_dropped` would be used in the main thread, after the threads with the relevant thread-local variables have been joined (directly or indirectly), to force the execution of any thread-local value destructors that have not already been invoked at that point.

## Usage pattern

Here's an outline of how this little framework can be used:

```rust
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
fn op(data: &Data, acc: &mut AccValue, _: &ThreadId) {
    *acc += data;
}

// Create a function to update the thread-local value:
fn update_tl(value: Data, control: &Control<Data, AccValue>) {
    control.with_mut(&MY_TL, |data| {
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

    let acc = control.accumulator().unwrap();
    println!("accumulated={:?}", acc.acc);
}
```

## Worked-out examples

See a more elaborate example at [`examples/map_accumulator.rs`](https://github.com/pvillela/rust-thread-local-drop/blob/main/examples/map_accumulator.rs).
