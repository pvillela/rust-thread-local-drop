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
fn op(data: &Data, acc: &mut AccValue, _: &ThreadId) {
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
        .with_acc(|acc| println!("accumulated={:?}", acc))
        .unwrap();
}
