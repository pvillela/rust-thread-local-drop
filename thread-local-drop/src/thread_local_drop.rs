//! Support for ensuring that destructors are run on thread-local variables after the thread terminates.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    mem::replace,
    sync::{Arc, Mutex},
    thread::{self, LocalKey, ThreadId},
};

/// Controls the destruction of thread-local variables registered with it.
/// Such thread-locals must be of type `RefCell<Holder<T>>`.
pub struct Control<T>(
    Arc<Mutex<HashMap<ThreadId, usize>>>,
    Arc<dyn Fn(&Option<T>) + Send + Sync>,
);

impl<T: 'static> Debug for Control<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Control({:?})", self.0))
    }
}

impl<T> Clone for Control<T> {
    fn clone(&self) -> Self {
        Control(self.0.clone(), self.1.clone())
    }
}

impl<T> Control<T> {
    /// Instantiates a new [Control].
    pub fn new(accept: impl Fn(&Option<T>) + 'static + Send + Sync) -> Self {
        Control(Arc::new(Mutex::new(HashMap::new())), Arc::new(accept))
    }

    /// Registers a thread-local with `self` in case it is not already registered.
    pub fn ensure_tl_registered(&self, tl: &'static LocalKey<RefCell<Holder<T>>>) {
        tl.with(|r| {
            // Case already registered.
            if r.borrow().control.is_some() {
                return;
            }

            // Otherwise.

            // Update Holder.
            {
                let holder = &mut r.borrow_mut();
                (*holder).control = Some(self.clone());
            }

            // Update self.
            {
                let data_ptr: *const Option<T> = &r.borrow().data;
                let addr = data_ptr as usize;
                let mut control = self.0.lock().unwrap();
                control.insert(thread::current().id(), addr);
                println!("thread id {:?} registered", thread::current().id());
            }
        });
    }

    /// Forces all registered thread-locals that have not already been dropped to be effectively dropped
    /// by replacing the [`Holder`] data with [`None`].
    /// Should only be called after joining with all threads that have registered, to ensure proper
    /// "happened-before" condition between any thread-local data updates and this call.
    pub fn ensure_tls_dropped(&self) {
        println!("entered `ensure_tls_dropped`");
        let mut control = self.0.lock().unwrap();
        for (tid, addr) in control.iter() {
            println!("executing `ensure_tls_dropped` tid {:?}", tid);
            // Safety: provided that:
            // - This function is only called by a thread on which `ensure_tl_registered` has never been called
            // - All other threads have terminaged and been joined, which means that there is a proper
            //   "happened-before" relationship and the only possible remaining activity on those threads
            //   would be Holder drop method execution, but that method uses the above Mutex to prevent
            //   race conditions.
            let ptr = unsafe { &mut *(*addr as *mut Option<T>) };
            let data = replace(ptr, None);
            self.1(&data);
        }
        *control = HashMap::new();
    }
}

/// Holds thead-local data to enable registering with [`Control`].
pub struct Holder<T: 'static> {
    pub data: Option<T>,
    control: Option<Control<T>>,
}

impl<T> Holder<T> {
    /// Instantiates an empty [`Holder`].
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
        if self.data.is_none() {
            println!(
                "exiting `drop` for Holder on thread {:?} because data is None",
                thread::current().id()
            );
            return;
        }
        println!(
            "`drop` acquiring control lock on thread {:?}",
            thread::current().id()
        );
        let mut control = self.control.as_ref().unwrap();
        println!(
            "`drop` acquired control lock on thread {:?}",
            thread::current().id()
        );
        let mut map = control.0.lock().unwrap();
        let entry = map.remove_entry(&thread::current().id());
        println!(
            "`drop` removed entry {:?} for thread {:?}, control={:?}",
            entry,
            thread::current().id(),
            map
        );
        let accept = &control.1;
        accept(&self.data);
    }
}
