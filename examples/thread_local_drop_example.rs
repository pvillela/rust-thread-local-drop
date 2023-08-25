//! Example usage of [thread_local_drop].

use std::{
    collections::HashMap,
    fmt::Debug,
    thread::{self, ThreadId},
    time::Duration,
};
use thread_local_drop::{Control, Holder};

#[derive(Debug, Clone)]
struct Foo(String);

type Data = HashMap<u32, Foo>;

type AccumulatorMap = HashMap<ThreadId, HashMap<u32, Foo>>;

thread_local! {
    static MY_FOO_MAP: Holder<Data, AccumulatorMap> = Holder::new(HashMap::new);
}

fn insert_tl_entry(k: u32, v: Foo, control: &Control<Data, AccumulatorMap>) {
    control.with_mut(&MY_FOO_MAP, |data| {
        data.insert(k, v);
    });
}

fn print_tl(prefix: &str) {
    MY_FOO_MAP.with(|r| {
        println!(
            "{}: local map for thread id={:?}: {:?}",
            prefix,
            thread::current().id(),
            r
        );
    });
}

fn op(data: &HashMap<u32, Foo>, acc: &mut AccumulatorMap, tid: &ThreadId) {
    println!(
        "`op` called from {:?} with data {:?}",
        thread::current().id(),
        data
    );

    acc.entry(tid.clone()).or_insert_with(|| HashMap::new());
    for (k, v) in data {
        acc.get_mut(tid).unwrap().insert(*k, v.clone());
    }
}

fn main() {
    let control = Control::new(HashMap::new(), op);

    thread::scope(|s| {
        let h1 = s.spawn(|| {
            insert_tl_entry(1, Foo("a".to_owned()), &control);
            insert_tl_entry(2, Foo("b".to_owned()), &control);
            print_tl("Before h1 sleep");
            thread::sleep(Duration::from_millis(100));
            print_tl("After h1 sleep");
        });

        let h2 = s.spawn(|| {
            insert_tl_entry(1, Foo("aa".to_owned()), &control);
            print_tl("Before h2 sleep");
            thread::sleep(Duration::from_millis(200));
            insert_tl_entry(2, Foo("bb".to_owned()), &control);
            print_tl("After h2 sleep");
        });

        thread::sleep(Duration::from_millis(50));

        println!("Before h1 join: control={:?}", control);

        {
            _ = h1.join();
            println!("After h1 join: control={:?}", control);

            // Don't do this in production code. For demonstration purposes only.
            // Making this call before joining with `h2` is dangerous because there is a data race.
            // However, in this particular example, it's OK because of the choice of sleep times
            // and the fact that `Holder::borrow_mut` ensures `Holder` is properly initialized
            // before inserting a key-value pair.
            control.ensure_tls_dropped();

            println!(
                "After 1st call to `ensure_tls_dropped`: control={:?}",
                control
            );
        }

        {
            _ = h2.join();
            println!("After h2 join: control={:?}", control);
            control.ensure_tls_dropped();
            println!(
                "After 2nd call to `ensure_tls_dropped`: control={:?}",
                control
            );
        }
    });

    let acc = control.accumulator().unwrap();
    println!("accumulated={:?}", acc.acc);
}
