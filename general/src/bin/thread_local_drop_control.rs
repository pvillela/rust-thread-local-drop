use std::{
    cell::RefCell,
    collections::HashMap,
    mem::replace,
    pin::Pin,
    sync::{Mutex, OnceLock},
    thread::{self, ThreadId},
    time::Duration,
};

#[derive(Debug)]
struct Foo(String);

static GLOBAL_DROP_CONTROL: OnceLock<Mutex<HashMap<ThreadId, usize>>> = OnceLock::new();

fn get_tl_drop_control() -> &'static Mutex<HashMap<ThreadId, usize>> {
    GLOBAL_DROP_CONTROL.get_or_init(|| Mutex::new(HashMap::new()))
}

#[derive(Debug)]
struct Holder(Pin<Box<HashMap<u32, Foo>>>);

impl Drop for Holder {
    fn drop(&mut self) {
        println!(
            "entered `drop` for Holder on thread {:?}",
            thread::current().id()
        );
        // Prevent recursion with `ensure_tls_dropped`.
        if self.0.is_empty() {
            return;
        }
        let mut control = get_tl_drop_control().lock().unwrap();
        control.remove_entry(&thread::current().id());
    }
}

thread_local! {
    static MY_MAP: RefCell<(bool, Holder)> = RefCell::new((false, Holder(Box::pin(HashMap::new()))));
}

fn ensure_tl_registered() {
    MY_MAP.with(|r| {
        if r.borrow().0 {
            return;
        }
        (*r.borrow_mut()).0 = true;
        let mut control = get_tl_drop_control().lock().unwrap();
        let x: *const Pin<Box<HashMap<u32, Foo>>> = &r.borrow().1 .0;
        let x = x as usize;
        control.insert(thread::current().id(), x);
        println!("thread id {:?} registered", thread::current().id());
    });
}

fn insert_tl_entry(k: u32, v: Foo) {
    ensure_tl_registered();
    MY_MAP.with(|r| {
        let x = &mut r.borrow_mut().1;
        x.0.insert(k, v)
    });
}

fn print_tl() {
    MY_MAP.with(|r| {
        println!(
            "local map for thread id={:?}: {:?}",
            thread::current().id(),
            r
        );
    });
}

fn ensure_tls_dropped() {
    println!("entered `ensure_tls_dropped`");
    let mut control = get_tl_drop_control().lock().unwrap();
    for (tid, addr) in control.iter() {
        println!("executing `ensure_tls_dropped` tid {:?}", tid);
        // Safety: provided that:
        // - This function is only called by a thread on which `ensure_tl_registered` has never been called
        // - All other threads have terminaged, which means the only possible remaining activity on those threads
        //   would be Holder drop method execution, but that method uses the above Mutex to prevent
        //   race conditions.
        let ptr = unsafe { &mut *(*addr as *mut Pin<Box<HashMap<u32, Foo>>>) };
        _ = replace(ptr, Box::pin(HashMap::new()));
    }
    *control = HashMap::new();
}

fn main() {
    let h1 = thread::spawn(|| {
        insert_tl_entry(1, Foo("a".to_owned()));
        insert_tl_entry(2, Foo("b".to_owned()));
        print_tl();
        thread::sleep(Duration::from_millis(100));
        print_tl();
    });

    let h2 = thread::spawn(|| {
        insert_tl_entry(1, Foo("aa".to_owned()));
        insert_tl_entry(2, Foo("bb".to_owned()));
        print_tl();
        thread::sleep(Duration::from_millis(200));
        print_tl();
    });

    thread::sleep(Duration::from_millis(50));

    {
        let control = get_tl_drop_control().lock().unwrap();
        println!("Before h1 join: control={:?}", control);
    }

    {
        _ = h1.join();
        {
            let control = get_tl_drop_control().lock().unwrap();
            println!("After h1 join: control={:?}", control);
        }
        ensure_tls_dropped(); // this call can be unsafe because h2 hasn't been joined yet
        let control = get_tl_drop_control().lock().unwrap();
        println!(
            "After 1st call to `ensure_tls_dropped`: control={:?}",
            control
        );
    }

    {
        _ = h2.join();
        {
            let control = get_tl_drop_control().lock().unwrap();
            println!("After h2 join: control={:?}", control);
        }
        ensure_tls_dropped();
        let control = get_tl_drop_control().lock().unwrap();
        println!(
            "After 2nd call to `ensure_tls_dropped`: control={:?}",
            control
        );
    }
}
