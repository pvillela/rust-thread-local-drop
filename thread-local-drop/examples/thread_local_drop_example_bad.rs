//! Example of inappropriate use of [`thread_local_drop`].

use std::{cell::RefCell, collections::HashMap, fmt::Debug, thread, time::Duration};
use thread_local_drop::{Control, Holder};

#[derive(Debug)]
struct Foo(String);

thread_local! {
    static MY_FOO_MAP: RefCell<Holder<HashMap<u32, Foo>>> = RefCell::new(Holder::new());
}

fn insert_tl_entry(k: u32, v: Foo, control: &Control<HashMap<u32, Foo>>) {
    control.ensure_tl_registered(&MY_FOO_MAP);
    MY_FOO_MAP.with(|r| {
        let x = &mut r.borrow_mut();
        if x.data.is_none() {
            (*x).data = Some(HashMap::new());
        }
        x.data.as_mut().unwrap().insert(k, v);
    });
}

fn dangerous_insert_tl_entry(k: u32, v: Foo) {
    MY_FOO_MAP.with(|r| {
        let x = &mut r.borrow_mut();
        x.data.as_mut().unwrap().insert(k, v);
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

pub fn main() {
    let control = Control::new(|_| ());

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
            dangerous_insert_tl_entry(2, Foo("bb".to_owned()));
            print_tl("After `dangerous_insert_tl_entry`");
        });

        thread::sleep(Duration::from_millis(50));

        println!("Before h1 join: control={:?}", control);

        {
            _ = h1.join();
            println!("After h1 join: control={:?}", control);
            control.ensure_tls_dropped(); // this call is unsafe because h2 hasn't been joined yet
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
}
