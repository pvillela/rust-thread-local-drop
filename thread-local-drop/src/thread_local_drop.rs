//! Support for ensuring that destructors are run on thread-local variables after the thread terminates.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    mem::replace,
    ops::DerefMut,
    sync::{Arc, Mutex},
    thread::{self, LocalKey, ThreadId},
};

#[derive(Debug)]
struct InnerControl<U> {
    map: HashMap<ThreadId, usize>,
    acc: U,
}

/// Controls the destruction of thread-local variables registered with it.
/// Such thread-locals must be of type `RefCell<Holder<T>>`.
pub struct Control<T, U> {
    inner: Arc<Mutex<InnerControl<U>>>,
    op: Arc<dyn Fn(&T, &U, &ThreadId) -> U + Send + Sync>,
}

impl<T, U> Clone for Control<T, U> {
    fn clone(&self) -> Self {
        Control {
            inner: self.inner.clone(),
            op: self.op.clone(),
        }
    }
}

impl<T, U: Debug> Debug for Control<T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Control({:?})", self.inner))
    }
}

impl<T, U> Control<T, U> {
    /// Instantiates a new [Control].
    pub fn new(acc_base: U, op: impl Fn(&T, &U, &ThreadId) -> U + 'static + Send + Sync) -> Self {
        Control {
            inner: Arc::new(Mutex::new(InnerControl {
                map: HashMap::new(),
                acc: acc_base,
            })),
            op: Arc::new(op),
        }
    }

    /// Registers a thread-local with `self` in case it is not already registered.
    pub fn ensure_tl_registered(&self, tl: &'static LocalKey<RefCell<Holder<T, U>>>) {
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
                let mut control = self.inner.lock().unwrap();
                control.map.insert(thread::current().id(), addr);
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
        let mut control = self.inner.lock().unwrap();
        let inner = control.deref_mut();
        let acc = &mut inner.acc;
        let map = &mut inner.map;
        for (tid, addr) in map.iter() {
            println!("executing `ensure_tls_dropped` tid {:?}", tid);
            // Safety: provided that:
            // - This function is only called by a thread on which `ensure_tl_registered` has never been called
            // - All other threads have terminaged and been joined, which means that there is a proper
            //   "happened-before" relationship and the only possible remaining activity on those threads
            //   would be Holder drop method execution, but that method uses the above Mutex to prevent
            //   race conditions.
            let ptr = unsafe { &mut *(*addr as *mut Option<T>) };
            let data = replace(ptr, None);
            if let Some(data) = data {
                *acc = (&self.op)(&data, acc, tid);
            }
        }
        *map = HashMap::new();
    }
}

/// Holds thead-local data to enable registering with [`Control`].
pub struct Holder<T, U> {
    pub data: Option<T>,
    control: Option<Control<T, U>>,
}

impl<T, U> Holder<T, U> {
    /// Instantiates an empty [`Holder`].
    pub fn new() -> Self {
        Holder {
            data: None,
            control: None,
        }
    }
}

impl<T: Debug, U> Debug for Holder<T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Holder{{data: {:?}}}", self.data))
    }
}

impl<T, U> Drop for Holder<T, U> {
    fn drop(&mut self) {
        let tid = thread::current().id();
        println!("entered `drop` for Holder on thread {:?}", tid);
        if self.data.is_none() {
            println!(
                "exiting `drop` for Holder on thread {:?} because data is None",
                tid
            );
            return;
        }
        println!("`drop` acquiring control lock on thread {:?}", tid);
        let control = self.control.as_ref().unwrap();
        println!("`drop` acquired control lock on thread {:?}", tid);
        let mut inner = control.inner.lock().unwrap();
        let map = &mut inner.map;
        let entry = map.remove_entry(&tid);
        println!(
            "`drop` removed entry {:?} for thread {:?}, control={:?}",
            entry,
            thread::current().id(),
            map
        );
        let op = &control.op;
        if let Some(data) = &self.data {
            (*inner).acc = op(data, &inner.acc, &tid);
        }
    }
}
