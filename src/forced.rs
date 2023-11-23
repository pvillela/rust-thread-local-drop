//! Support for ensuring that destructors are run on thread-local variables after the threads terminate,
//! as well as support for accumulating the thread-local values using a binary operation.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    mem::replace,
    ops::DerefMut,
    sync::{Arc, Mutex, MutexGuard},
    thread::{self, LocalKey, ThreadId},
};

#[derive(Debug)]
struct InnerControl<T, U> {
    /// Thread control map.
    tmap: HashMap<ThreadId, Arc<Mutex<Option<T>>>>,
    /// Accumulated value.
    acc: U,
}

/// Controls the destruction of thread-local values registered with it.
/// Such values of type `T` must be held in thread-locals of type [`Holder<T>`].
/// `U` is the type of the accumulated value resulting from an initial base value and
/// the application of an operation to each thread-local value and the current accumulated
/// value upon dropping of each thread-local value. (See [`new`](Control::new) method.)
pub struct Control<T, U> {
    /// Keeps track of registered threads and accumulated value.
    inner: Arc<Mutex<InnerControl<T, U>>>,
    /// Binary operation that combines data from thread-locals with accumulated value.
    #[allow(clippy::type_complexity)]
    op: Arc<dyn Fn(T, &mut U, &ThreadId) + Send + Sync>,
}

/// Encapsulates a [`MutexGuard`] for use by public methods that require [`Control`]'s lock to be acquired.
///
/// An acquired lock can be used with multiple method calls and droped after the last call.
/// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
pub struct ControlLock<'a, T, U: 'a>(MutexGuard<'a, InnerControl<T, U>>);

impl<T, U> Clone for Control<T, U> {
    fn clone(&self) -> Self {
        Control {
            inner: self.inner.clone(),
            op: self.op.clone(),
        }
    }
}

impl<T: Debug, U: Debug> Debug for Control<T, U> {
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
    pub fn new(acc_base: U, op: impl Fn(T, &mut U, &ThreadId) + 'static + Send + Sync) -> Self {
        Control {
            inner: Arc::new(Mutex::new(InnerControl {
                tmap: HashMap::new(),
                acc: acc_base,
            })),
            op: Arc::new(op),
        }
    }

    /// Registers a thread-local with `self` in case it is not already registered.
    fn ensure_tl_registered(&self, tl: &'static LocalKey<Holder<T, U>>) {
        tl.with(|r| {
            // Case already registered.
            {
                if r.control.borrow().is_some() {
                    log::trace!(
                        "r.control.borrow().is_some() on {:?}",
                        thread::current().id(),
                    );
                    return;
                }
            }

            // Otherwise.

            // Update Holder.
            {
                let mut control = r.control.borrow_mut();
                *control = Some(self.clone());
            }

            // Update self.
            {
                // let data_ptr: *const Option<T> = &*r.data.borrow();
                // let addr = data_ptr as usize;
                let data = r.data.clone();
                let mut control = self.inner.lock().unwrap();
                control.tmap.insert(thread::current().id(), data);
                log::trace!("thread id {:?} registered", thread::current().id());
            }
        });
    }

    /// Acquires a lock for use by public [`Control`] methods that require its internal Mutex to be locked.
    ///
    /// An cquired lock can be used with multiple method calls and droped after the last call.
    /// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
    pub fn lock(&self) -> ControlLock<'_, T, U> {
        let lock = self.inner.lock().unwrap();
        ControlLock(lock)
    }

    /// Forces all registered thread-local values that have not already been dropped to be effectively dropped
    /// by replacing the [`Holder`] data with [`None`], and accumulates the values contained in those thread-locals.
    ///
    /// Should only be called from a thread (typically the main thread) under the following conditions:
    /// - All other threads that use this [`Control`] instance must have been directly or indirectly spawned
    ///   from this thread; ***and***
    /// - Any prior updates to holder values must have had a *happened before* relationship to this call;
    ///   ***and***
    /// - Any further updates to holder values must have a *happened after* relationship to this call.
    ///   
    /// In particular, the last two conditions are satisfied if the call to this method takes place after
    /// this thread joins (directly or indirectly) with all threads that have registered with this [`Control`]
    /// instance.
    ///
    /// These conditions ensure the absence of data races with a proper "happens-before" condition between any
    /// thread-local data updates and this call.
    ///
    /// The [`lock`](Self::lock) method can be used to obtain the `lock` argument.
    /// An cquired lock can be used with multiple method calls and droped after the last call.
    /// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
    pub fn ensure_tls_dropped(&self, lock: &mut ControlLock<'_, T, U>) {
        log::trace!("entered `ensure_tls_dropped`");
        let inner = lock.0.deref_mut();
        let map = &inner.tmap;
        let acc = &mut inner.acc;
        if map.is_empty() {
            log::trace!("exited `ensure_tls_dropped` with no keys to drop");
            return;
        }
        for (tid, addr) in map.iter() {
            log::trace!("executing `ensure_tls_dropped` for key={:?}", tid);
            let mut guard = addr.lock().unwrap();
            let ptr = guard.deref_mut();
            let data = Option::take(ptr);
            log::trace!("executed `take` -- `ensure_tls_dropped` for key={:?}", tid);
            if let Some(data) = data {
                log::trace!("executing `op` -- `ensure_tls_dropped` for key={:?}", tid);
                (self.op)(data, acc, tid);
            }
        }
        // tmap's keys are left alone to enable users of this framework to resume processing after
        // the thread-local data is accumulated.
    }

    /// Provides access to the accumulated value in the [Control] struct.
    ///
    /// The [`lock`](Self::lock) method can be used to obtain the `lock` argument.
    /// An cquired lock can be used with multiple method calls and droped after the last call.
    /// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
    pub fn with_acc<V>(&self, lock: &ControlLock<'_, T, U>, f: impl FnOnce(&U) -> V) -> V {
        f(&lock.0.acc)
    }

    /// Returns the accumulated value in the [Control] struct, using a value of the same type to replace
    /// the existing accumulated value.
    ///
    /// The [`lock`](Self::lock) method can be used to obtain the `lock` argument.
    /// An cquired lock can be used with multiple method calls and droped after the last call.
    /// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
    pub fn take_acc(&self, lock: &mut ControlLock<'_, T, U>, replacement: U) -> U {
        let acc = &mut lock.0.deref_mut().acc;
        replace(acc, replacement)
    }

    /// Provides immutable access to the data in the `Holder` in argument `tl`;
    pub fn with_tl<V>(&self, tl: &'static LocalKey<Holder<T, U>>, f: impl FnOnce(&T) -> V) -> V {
        self.ensure_tl_registered(tl);
        tl.with(|h| {
            let lock = h.borrow_data();
            let data = lock.as_ref().unwrap();
            f(data)
        })
    }

    /// Provides mutable access to the data in the `Holder` in argument `tl`;
    pub fn with_tl_mut<V>(
        &self,
        tl: &'static LocalKey<Holder<T, U>>,
        f: impl FnOnce(&mut T) -> V,
    ) -> V {
        self.ensure_tl_registered(tl);
        tl.with(|h| {
            let mut lock = h.borrow_data_mut();
            let data = lock.as_mut().unwrap();
            f(data)
        })
    }
}

/// Holds thead-local data to enable registering it with [`Control`].
pub struct Holder<T, U> {
    data: Arc<Mutex<Option<T>>>,
    control: RefCell<Option<Control<T, U>>>,
    data_init: fn() -> T,
}

impl<T, U> Holder<T, U> {
    /// Instantiates an empty [`Holder`] with the given data initializer function `data_init`.
    /// `data_init` is invoked when the data in [`Holder`] is accessed for the first time.
    /// See `borrow_data` and `borrow_data_mut`.
    pub fn new(data_init: fn() -> T) -> Self {
        Holder {
            data: Mutex::new(None).into(),
            control: RefCell::new(None),
            data_init,
        }
    }

    /// Immutably borrows the held data.
    /// If the data is not yet initialized, the function `data_init` passed to `new` is called to initialize the data.
    fn borrow_data(&self) -> MutexGuard<'_, Option<T>> {
        let mut data = self.data.lock().unwrap();
        if data.is_none() {
            // let data = self.data.lock().unwrap();
            *data = Some((self.data_init)());
        }
        data
    }

    /// Mutably borrows the held data.
    /// If the data is not yet initialized, the function `data_init` passed to `new` is called to initialize the data.
    fn borrow_data_mut(&self) -> MutexGuard<'_, Option<T>> {
        self.borrow_data()
    }
}

impl<T: Debug, U> Debug for Holder<T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Holder{{data: {:?}}}", self.data))
    }
}

impl<T, U> Drop for Holder<T, U> {
    /// Ensures the held data, if any, is deregistered from the associated [`Control`] instance
    /// and the control instance's accumulation operation is invoked with the held data.
    fn drop(&mut self) {
        let tid = thread::current().id();
        log::trace!("entered `drop` for Holder on thread {:?}", tid);
        let control = self.control.borrow();
        if control.is_none() {
            log::trace!(
                "exiting `drop` for Holder on thread {:?} because control is None",
                tid
            );
            return;
        }
        let control = control.as_ref().unwrap();

        log::trace!("`drop` acquiring control lock on thread {:?}", tid);
        let mut inner = control.inner.lock().unwrap();
        log::trace!("`drop` acquired control lock on thread {:?}", tid);

        let mut data = self.data.lock().unwrap();
        if data.is_none() {
            log::trace!(
                "exiting `drop` for Holder on thread {:?} because data is None",
                tid
            );
            return;
        }

        let map = &mut inner.tmap;
        let _entry = map.remove_entry(&tid);
        log::trace!(
            "`drop` removed entry <:?> for thread {:?}, control=<:?>",
            // entry,
            thread::current().id(),
            // map
        );
        let op = &control.op;
        let data = data.take();
        if let Some(data) = data {
            op(data, &mut inner.acc, &tid);
        }
        log::trace!("`drop` exited on thread {:?}", tid);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::{
        collections::HashMap,
        fmt::Debug,
        ops::Deref,
        sync::RwLock,
        thread::{self, ThreadId},
        time::Duration,
    };

    #[derive(Debug, Clone, PartialEq)]
    struct Foo(String);

    type Data = HashMap<u32, Foo>;

    type AccumulatorMap = HashMap<ThreadId, HashMap<u32, Foo>>;

    thread_local! {
        static MY_FOO_MAP: Holder<Data, AccumulatorMap> = Holder::new(HashMap::new);
    }

    fn insert_tl_entry(k: u32, v: Foo, control: &Control<Data, AccumulatorMap>) {
        control.with_tl_mut(&MY_FOO_MAP, |data| {
            data.insert(k, v);
        });
    }

    fn op(data: HashMap<u32, Foo>, acc: &mut AccumulatorMap, tid: &ThreadId) {
        println!(
            "`op` called from {:?} with data {:?}",
            thread::current().id(),
            data
        );

        acc.entry(tid.clone()).or_insert_with(|| HashMap::new());
        for (k, v) in data {
            acc.get_mut(tid).unwrap().insert(k, v.clone());
        }
    }

    // fn assert_tl(other: &Data, msg: &str) {
    //     MY_FOO_MAP.with(|r| {
    //         let map_ref = r.borrow_data();
    //         let map = map_ref.deref();
    //         assert_eq!(map, other, "{msg}");
    //     });
    // }

    fn _typed_value<T>(addr: usize) -> &'static Option<T> {
        unsafe { &*(addr as *const Option<T>) }
    }

    // fn assert_control_map(control: &Control<Data, AccumulatorMap>, keys: &[ThreadId], msg: &str) {
    //     let inner = control.inner.lock().unwrap();
    //     let map = &inner.tmap;
    //     for (k, v) in map {
    //         let value = typed_value::<Data>(*v);
    //         assert!(
    //             keys.contains(k) || value.is_none(),
    //             "{msg} - map contains spurious key {:?} with value {:?}",
    //             k,
    //             value
    //         );
    //     }
    //     for k in keys {
    //         let v = map.get(k);
    //         let res = match v {
    //             None => false,
    //             Some(&addr) => typed_value::<Data>(addr).is_some(),
    //         };
    //         assert!(res, "{msg} - map is missing key {:?}", k);
    //     }
    // }

    #[test]
    fn test_all() {
        let control = Control::new(HashMap::new(), op);

        let main_tid = thread::current().id();
        println!("main_tid={:?}", main_tid);
        let spawned_tid = RwLock::new(thread::current().id());

        {
            insert_tl_entry(1, Foo("a".to_owned()), &control);
            insert_tl_entry(2, Foo("b".to_owned()), &control);
            println!("after main thread inserts: {:?}", control);

            let _other = HashMap::from([(1, Foo("a".to_owned())), (2, Foo("b".to_owned()))]);
            // assert_tl(&other, "After main thread inserts");
        }

        thread::sleep(Duration::from_millis(100));

        thread::scope(|s| {
            let h = s.spawn(|| {
                let mut lock = spawned_tid.try_write().unwrap();
                *lock = thread::current().id();
                drop(lock);

                insert_tl_entry(1, Foo("aa".to_owned()), &control);

                let _other = HashMap::from([(1, Foo("aa".to_owned()))]);
                // assert_tl(&other, "Before spawned thread sleep");

                thread::sleep(Duration::from_millis(200));

                insert_tl_entry(2, Foo("bb".to_owned()), &control);

                let _other = HashMap::from([(1, Foo("aa".to_owned())), (2, Foo("bb".to_owned()))]);
                // assert_tl(&other, "After spawned thread sleep");
            });

            thread::sleep(Duration::from_millis(50));

            let spawned_tid = spawned_tid.try_read().unwrap();
            println!("spawned_tid={:?}", spawned_tid);

            let _keys = [main_tid.clone(), spawned_tid.clone()];
            // assert_control_map(&control, &keys, "Before joining spawned thread");

            h.join().unwrap();

            println!("after h.join(): {:?}", control);

            control.ensure_tls_dropped(&mut control.lock());
            // let keys = [];
            // assert_control_map(&control, &keys, "After call to `ensure_tls_dropped`");
        });

        {
            let spawned_tid = spawned_tid.try_read().unwrap();
            let map1 = HashMap::from([(1, Foo("a".to_owned())), (2, Foo("b".to_owned()))]);
            let map2 = HashMap::from([(1, Foo("aa".to_owned())), (2, Foo("bb".to_owned()))]);
            let map = HashMap::from([(main_tid.clone(), map1), (spawned_tid.clone(), map2)]);

            {
                let lock = control.lock();
                let acc = &lock.0.deref().acc;
                assert_eq!(acc, &map, "Accumulator check");
            }
        }
    }
}
