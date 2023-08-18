//! Generic version of `thread_local_drop_control.rs`.
//! Demonstrates how to ensure destructors are run on thread-local variables after the thread terminates.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    mem::replace,
    sync::{Arc, Mutex},
    thread::{self, LocalKey, ThreadId},
    time::Duration,
};

#[derive(Debug)]
struct Foo(String);

pub struct Control(Arc<Mutex<HashMap<ThreadId, usize>>>);

impl Clone for Control {
    fn clone(&self) -> Self {
        Control(self.0.clone())
    }
}

impl Control {
    pub fn new() -> Self {
        Control(Arc::new(Mutex::new(HashMap::new())))
    }

    pub fn ensure_tl_registered<T>(&self, tl: &'static LocalKey<RefCell<(bool, Holder<T>)>>) {
        tl.with(|r| {
            // Case already registered.
            if r.borrow().0 {
                return;
            }

            // Otherwise.

            // Update Holder.
            {
                (*r.borrow_mut()).0 = true;
                let holder = &mut r.borrow_mut().1;
                (*holder).control = Some(self.clone());
            }

            // Update self.
            {
                let data_ptr: *const Option<T> = &r.borrow().1.data;
                let addr = data_ptr as usize;
                let mut control = self.0.lock().unwrap();
                control.insert(thread::current().id(), addr);
                println!("thread id {:?} registered", thread::current().id());
            }
        });
    }

    pub fn ensure_tls_dropped<T>(&self) {
        println!("entered `ensure_tls_dropped`");
        let mut control = self.0.lock().unwrap();
        for (tid, addr) in control.iter() {
            println!("executing `ensure_tls_dropped` tid {:?}", tid);
            // Safety: provided that:
            // - This function is only called by a thread on which `ensure_tl_registered` has never been called
            // - All other threads have terminaged, which means the only possible remaining activity on those threads
            //   would be Holder drop method execution, but that method uses the above Mutex to prevent
            //   race conditions.
            let ptr = unsafe { &mut *(*addr as *mut Option<T>) };
            _ = replace(ptr, None);
        }
        *control = HashMap::new();
    }
}

pub struct Holder<T> {
    data: Option<T>,
    control: Option<Control>,
}

impl<T> Holder<T> {
    pub fn new() -> Self {
        Holder {
            data: None,
            control: None,
        }
    }
}

impl<T: Debug> Debug for Holder<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Holder{{data: {:?}}}", self.data))
    }
}

impl<T> Drop for Holder<T> {
    fn drop(&mut self) {
        println!(
            "entered `drop` for Holder on thread {:?}",
            thread::current().id()
        );
        if self.control.is_none() {
            println!(
                "exiting `drop` for Holder on thread {:?} because control is None",
                thread::current().id()
            );
            return;
        }
        println!(
            "`drop` acquiring control lock on thread {:?}",
            thread::current().id()
        );
        let mut control = self.control.as_ref().unwrap().0.lock().unwrap();
        println!(
            "`drop` acquired control lock on thread {:?}",
            thread::current().id()
        );
        let entry = control.remove_entry(&thread::current().id());
        println!(
            "`drop` removed entry {:?} for thread {:?}, control={:?}",
            entry,
            thread::current().id(),
            control
        );
    }
}

thread_local! {
    static MY_FOO_MAP: RefCell<(bool, Holder<HashMap<u32, Foo>>)> = RefCell::new((false, Holder::new()));
}

fn insert_tl_entry(k: u32, v: Foo, control: &Control) {
    control.ensure_tl_registered(&MY_FOO_MAP);
    MY_FOO_MAP.with(|r| {
        let x = &mut r.borrow_mut().1;
        if x.data.is_none() {
            (*x).data = Some(HashMap::new());
        }
        x.data.as_mut().unwrap().insert(k, v);
    });
}

fn print_tl() {
    MY_FOO_MAP.with(|r| {
        println!(
            "local map for thread id={:?}: {:?}",
            thread::current().id(),
            r
        );
    });
}

// fn main() {}

fn main() {
    let control = Control::new();

    thread::scope(|s| {
        let h1 = s.spawn(|| {
            insert_tl_entry(1, Foo("a".to_owned()), &control);
            insert_tl_entry(2, Foo("b".to_owned()), &control);
            print_tl();
            thread::sleep(Duration::from_millis(100));
            print_tl();
        });

        let h2 = s.spawn(|| {
            insert_tl_entry(1, Foo("aa".to_owned()), &control);
            insert_tl_entry(2, Foo("bb".to_owned()), &control);
            print_tl();
            thread::sleep(Duration::from_millis(200));
            print_tl();
        });

        thread::sleep(Duration::from_millis(50));

        {
            let control = control.0.lock().unwrap();
            println!("Before h1 join: control={:?}", control);
        }

        {
            _ = h1.join();
            {
                let control = control.0.lock().unwrap();
                println!("After h1 join: control={:?}", control);
            }
            control.ensure_tls_dropped::<HashMap<u32, Foo>>(); // this call can be unsafe because h2 hasn't been joined yet
            let control = control.0.lock().unwrap();
            println!(
                "After 1st call to `ensure_tls_dropped`: control={:?}",
                control
            );
        }

        {
            _ = h2.join();
            {
                let control = control.0.lock().unwrap();
                println!("After h2 join: control={:?}", control);
            }
            control.ensure_tls_dropped::<HashMap<u32, Foo>>();
            let control = control.0.lock().unwrap();
            println!(
                "After 2nd call to `ensure_tls_dropped`: control={:?}",
                control
            );
        }
    });
}
