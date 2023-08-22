//! Support for ensuring that destructors are run on thread-local variables after the threads terminate,
//! as well as support for accumulating the thread-local values using a binary operation.

use log;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    mem::replace,
    ops::DerefMut,
    sync::{Arc, Mutex, MutexGuard, TryLockError},
    thread::{self, LocalKey, ThreadId},
};

#[derive(Debug)]
pub struct Accumulator<U> {
    /// Thread control map.
    tmap: HashMap<ThreadId, usize>,
    /// Accumulated value.
    pub acc: U,
}

type InnerControl<U> = Accumulator<U>;

/// Controls the destruction of thread-local variables registered with it.
/// Such thread-locals must be of type `RefCell<Holder<T>>`.
pub struct Control<T, U> {
    /// Keeps track of registered threads and accumulated value.
    inner: Arc<Mutex<InnerControl<U>>>,
    /// Binary operation that combines data from thread-locals with accumulated value.
    op: Arc<dyn Fn(&T, &mut U, &ThreadId) + Send + Sync>,
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
    ///
    /// # Arguments
    /// * `acc_base` - Initial value of accumulator that will be combined with thread-local values
    /// using `op`.
    /// * `op` - Binary operation used to combine thread-local values with accumulated value.
    pub fn new(acc_base: U, op: impl Fn(&T, &mut U, &ThreadId) + 'static + Send + Sync) -> Self {
        Control {
            inner: Arc::new(Mutex::new(InnerControl {
                tmap: HashMap::new(),
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
                control.tmap.insert(thread::current().id(), addr);
                log::trace!("thread id {:?} registered", thread::current().id());
            }
        });
    }

    /// Forces all registered thread-locals that have not already been dropped to be effectively dropped
    /// by replacing the [`Holder`] data with [`None`].
    /// Should only be called after joining with all threads that have registered, to ensure proper
    /// "happened-before" condition between any thread-local data updates and this call.
    pub fn ensure_tls_dropped(&self) {
        log::trace!("entered `ensure_tls_dropped`");
        let mut control = self.inner.lock().unwrap();
        let inner = control.deref_mut();
        let acc = &mut inner.acc;
        let map = &mut inner.tmap;
        for (tid, addr) in map.iter() {
            log::trace!("executing `ensure_tls_dropped` tid {:?}", tid);
            // Safety: provided that:
            // - This function is only called by a thread on which `ensure_tl_registered` has never been called
            // - All other threads have terminaged and been joined, which means that there is a proper
            //   "happened-before" relationship and the only possible remaining activity on those threads
            //   would be Holder drop method execution, but that method uses the above Mutex to prevent
            //   race conditions.
            let ptr = unsafe { &mut *(*addr as *mut Option<T>) };
            let data = replace(ptr, None);
            if let Some(data) = data {
                (&self.op)(&data, acc, tid);
            }
        }
        *map = HashMap::new();
    }

    /// Provides access to the value accumulated from thread-locals (see `new`).
    /// The result should always be [Ok] when this method is called after `ensure_tls_dropped`.
    /// However, calling this before all thread-locals have been dropped may result in lock
    /// contention with a [TryLockError] result.
    pub fn accumulator(
        &self,
    ) -> Result<MutexGuard<Accumulator<U>>, TryLockError<MutexGuard<Accumulator<U>>>> {
        match self.inner.try_lock() {
            Ok(guard) => Ok(guard),
            err @ _ => err,
        }
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
        log::trace!("entered `drop` for Holder on thread {:?}", tid);
        if self.data.is_none() {
            log::trace!(
                "exiting `drop` for Holder on thread {:?} because data is None",
                tid
            );
            return;
        }
        log::trace!("`drop` acquiring control lock on thread {:?}", tid);
        let control = self.control.as_ref().unwrap();
        log::trace!("`drop` acquired control lock on thread {:?}", tid);
        let mut inner = control.inner.lock().unwrap();
        let map = &mut inner.tmap;
        let entry = map.remove_entry(&tid);
        log::trace!(
            "`drop` removed entry {:?} for thread {:?}, control={:?}",
            entry,
            thread::current().id(),
            map
        );
        let op = &control.op;
        if let Some(data) = &self.data {
            op(data, &mut inner.acc, &tid);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::{
        cell::RefCell,
        collections::HashMap,
        fmt::Debug,
        sync::RwLock,
        thread::{self, ThreadId},
        time::Duration,
    };

    #[derive(Debug, Clone, PartialEq)]
    struct Foo(String);

    type Data = HashMap<u32, Foo>;

    type AccumulatorMap = HashMap<ThreadId, HashMap<u32, Foo>>;

    thread_local! {
        static MY_FOO_MAP: RefCell<Holder<Data, AccumulatorMap>> = RefCell::new(Holder::new());
    }

    fn insert_tl_entry(k: u32, v: Foo, control: &Control<Data, AccumulatorMap>) {
        control.ensure_tl_registered(&MY_FOO_MAP);
        MY_FOO_MAP.with(|r| {
            let x = &mut r.borrow_mut();
            if x.data.is_none() {
                (*x).data = Some(HashMap::new());
            }
            x.data.as_mut().unwrap().insert(k, v);
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

    fn assert_tl(other: &Data, msg: &str) {
        MY_FOO_MAP.with(|r| {
            let map = r.borrow();
            let map = map.data.as_ref().unwrap();
            assert!(map.eq(other), "{}", msg);
        });
    }

    fn assert_control_map(control: &Control<Data, AccumulatorMap>, keys: &[ThreadId], msg: &str) {
        let inner = control.inner.lock().unwrap();
        let map = &inner.tmap;
        assert_eq!(map.len(), keys.len(), "{}", msg);
        for k in keys {
            assert!(map.contains_key(k), "{}", msg);
        }
    }

    #[test]
    fn test_all() {
        let control = Control::new(HashMap::new(), op);

        let h1_tid = RwLock::new(thread::current().id());
        let h2_tid = RwLock::new(thread::current().id());

        thread::scope(|s| {
            let h1 = s.spawn(|| {
                let mut lock = h1_tid.try_write().unwrap();
                *lock = thread::current().id();
                drop(lock);

                insert_tl_entry(1, Foo("a".to_owned()), &control);
                insert_tl_entry(2, Foo("b".to_owned()), &control);

                let other = HashMap::from([(1, Foo("a".to_owned())), (2, Foo("b".to_owned()))]);
                assert_tl(&other, "Before h1 sleep");

                thread::sleep(Duration::from_millis(100));

                assert_tl(&other, "After h1 sleep");
            });

            let h2 = s.spawn(|| {
                let mut lock = h2_tid.try_write().unwrap();
                *lock = thread::current().id();
                drop(lock);

                insert_tl_entry(1, Foo("aa".to_owned()), &control);

                let other = HashMap::from([(1, Foo("aa".to_owned()))]);
                assert_tl(&other, "Before h2 sleep");

                thread::sleep(Duration::from_millis(200));

                insert_tl_entry(2, Foo("bb".to_owned()), &control);

                let other = HashMap::from([(2, Foo("bb".to_owned()))]);
                assert_tl(&other, "After h2 sleep");
            });

            {
                thread::sleep(Duration::from_millis(50));

                let h1_tid = h1_tid.try_read().unwrap();
                let h2_tid = h2_tid.try_read().unwrap();
                let keys = [h1_tid.clone(), h2_tid.clone()];
                assert_control_map(&control, &keys, "Before h1 join");
            }

            {
                _ = h1.join();
                let h2_tid = h2_tid.try_read().unwrap();
                let keys = [h2_tid.clone()];
                assert_control_map(&control, &keys, "After h1 join");

                // Don't do this in production code. For demonstration purposes only.
                // Making this call before joining with `h2` is dangerous because there is a data race.
                // However, in this particular example, it's OK because of the choice of sleep times
                // together with the fact that `insert_tl_entry` ensures `Holder` is properly initialized
                // before inserting a key-value pair.
                control.ensure_tls_dropped();

                let keys = [];
                assert_control_map(&control, &keys, "After 1st call to `ensure_tls_dropped`");
            }

            {
                _ = h2.join();
                let keys = [];
                assert_control_map(&control, &keys, "After h2 join");
                control.ensure_tls_dropped();
                let keys = [];
                assert_control_map(&control, &keys, "After 2nd call to `ensure_tls_dropped`");
            }
        });

        {
            let h1_tid = h1_tid.try_read().unwrap();
            let h2_tid = h2_tid.try_read().unwrap();

            let map1 = HashMap::from([(1, Foo("a".to_owned())), (2, Foo("b".to_owned()))]);
            let map2 = HashMap::from([(1, Foo("aa".to_owned())), (2, Foo("bb".to_owned()))]);
            let map = HashMap::from([(h1_tid.clone(), map1), (h2_tid.clone(), map2)]);

            let acc = &control.accumulator().unwrap().acc;

            assert!(acc.eq(&map), "Accumulator check");
        }
    }
}
