//! Support for ensuring that destructors are run on thread-local variables after the threads terminate,
//! as well as support for accumulating the thread-local values using a binary operation.

use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::Debug,
    mem::replace,
    sync::{Arc, Mutex, MutexGuard},
    thread::{self, LocalKey, ThreadId},
};

/// Controls the destruction of thread-local values registered with it.
/// Such values of type `T` must be held in thread-locals of type [`Holder<T>`].
/// `U` is the type of the accumulated value resulting from an initial base value and
/// the application of an operation to each thread-local value and the current accumulated
/// value upon dropping of each thread-local value. (See [`new`](Control::new) method.)
pub struct Control<T, U> {
    /// Keeps track of registered threads and accumulated value.
    acc: Arc<Mutex<U>>,
    /// Binary operation that combines data from thread-locals with accumulated value.
    #[allow(clippy::type_complexity)]
    op: Arc<dyn Fn(T, &mut U, &ThreadId) + Send + Sync>,
}

/// Encapsulates a [`MutexGuard`] for use by public methods that require [`Control`]'s lock to be acquired.
///
/// An acquired lock can be used with multiple method calls and droped after the last call.
/// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
pub struct ControlLock<'a, U: 'a>(MutexGuard<'a, U>);

impl<T, U> Clone for Control<T, U> {
    fn clone(&self) -> Self {
        Control {
            acc: self.acc.clone(),
            op: self.op.clone(),
        }
    }
}

impl<T, U: Debug> Debug for Control<T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Control({:?})", self.acc))
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
            acc: Arc::new(Mutex::new(acc_base)),
            op: Arc::new(op),
        }
    }

    /// Registers a thread-local with `self` in case it is not already registered.
    fn ensure_tl_control(&self, tl: &'static LocalKey<Holder<T, U>>) {
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
        });
    }

    /// Acquires a lock for use by public [`Control`] methods that require its internal Mutex to be locked.
    ///
    /// An cquired lock can be used with multiple method calls and droped after the last call.
    /// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
    pub fn lock(&self) -> ControlLock<'_, U> {
        let lock = self.acc.lock().unwrap();
        ControlLock(lock)
    }

    /// Provides access to the accumulated value in the [Control] struct.
    ///
    /// The [`lock`](Self::lock) method can be used to obtain the `lock` argument.
    /// An cquired lock can be used with multiple method calls and droped after the last call.
    /// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
    pub fn with_acc<V>(&self, lock: &ControlLock<'_, U>, f: impl FnOnce(&U) -> V) -> V {
        f(&lock.0)
    }

    /// Returns the accumulated value in the [Control] struct, using a value of the same type to replace
    /// the existing accumulated value.
    ///
    /// The [`lock`](Self::lock) method can be used to obtain the `lock` argument.
    /// An cquired lock can be used with multiple method calls and droped after the last call.
    /// As with any lock, the caller should ensure the lock is dropped as soon as it is no longer needed.
    pub fn take_acc(&self, lock: &mut ControlLock<'_, U>, replacement: U) -> U {
        let acc = &mut lock.0;
        replace(acc, replacement)
    }

    /// Provides immutable access to the data in the `Holder` in argument `tl`;
    pub fn with_tl<V>(&self, tl: &'static LocalKey<Holder<T, U>>, f: impl FnOnce(&T) -> V) -> V {
        self.ensure_tl_control(tl);
        tl.with(|h| {
            let data = h.borrow_data();
            f(&data)
        })
    }

    /// Provides mutable access to the data in the `Holder` in argument `tl`;
    pub fn with_tl_mut<V>(
        &self,
        tl: &'static LocalKey<Holder<T, U>>,
        f: impl FnOnce(&mut T) -> V,
    ) -> V {
        self.ensure_tl_control(tl);
        tl.with(|h| {
            let mut data = h.borrow_data_mut();
            f(&mut data)
        })
    }
}

/// Holds thead-local data to enable registering it with [`Control`].
pub struct Holder<T, U> {
    data: RefCell<Option<T>>,
    control: RefCell<Option<Control<T, U>>>,
    data_init: fn() -> T,
}

impl<T, U> Holder<T, U> {
    /// Instantiates an empty [`Holder`] with the given data initializer function `data_init`.
    /// `data_init` is invoked when the data in [`Holder`] is accessed for the first time.
    /// See `borrow_data` and `borrow_data_mut`.
    pub fn new(data_init: fn() -> T) -> Self {
        Holder {
            data: RefCell::new(None),
            control: RefCell::new(None),
            data_init,
        }
    }

    /// Immutably borrows the held data.
    /// If the data is not yet initialized, the function `data_init` passed to `new` is called to initialize the data.
    fn borrow_data(&self) -> Ref<'_, T> {
        let data = self.data.borrow();
        if data.is_none() {
            let mut data = self.data.borrow_mut();
            *data = Some((self.data_init)())
        }
        Ref::map(data, |x: &Option<T>| x.as_ref().unwrap())
    }

    /// Mutably borrows the held data.
    /// If the data is not yet initialized, the function `data_init` passed to `new` is called to initialize the data.
    fn borrow_data_mut(&self) -> RefMut<'_, T> {
        let mut data = self.data.borrow_mut();
        if data.is_none() {
            *data = Some((self.data_init)())
        }

        fn decimal_address<T>(r: &T) -> usize {
            r as *const T as usize
        }
        log::trace!(
            "`borrow_data_mut` address={} on {:?}",
            decimal_address(&*data),
            thread::current().id()
        );

        RefMut::map(data, |x: &mut Option<T>| x.as_mut().unwrap())
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
        let mut acc = control.acc.lock().unwrap();
        log::trace!("`drop` acquired control lock on thread {:?}", tid);

        if self.data.borrow().is_none() {
            log::trace!(
                "exiting `drop` for Holder on thread {:?} because data is None",
                tid
            );
            return;
        }
        let op = &control.op;
        let data = self.data.take();
        if let Some(data) = data {
            op(data, &mut acc, &tid);
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

    fn assert_tl(other: &Data, msg: &str) {
        MY_FOO_MAP.with(|r| {
            let map_ref = r.borrow_data();
            let map = map_ref.deref();
            assert_eq!(map, other, "{msg}");
        });
    }

    #[test]
    fn test_all() {
        let control = Control::new(HashMap::new(), op);
        let spawned_tids = RwLock::new(vec![thread::current().id(), thread::current().id()]);

        thread::scope(|s| {
            let hs = (0..2)
                .map(|i| {
                    s.spawn({
                        // These are to prevent the move closure from moving `control` and `spawned_tids`.
                        // The closure has to be `move` because it needs to own `i`.
                        let control = &control;
                        let spawned_tids = &spawned_tids;

                        move || {
                            let si = i.to_string();

                            let mut lock = spawned_tids.try_write().unwrap();
                            lock[i] = thread::current().id();
                            drop(lock);

                            insert_tl_entry(1, Foo("a".to_owned() + &si), control);

                            let other = HashMap::from([(1, Foo("a".to_owned() + &si))]);
                            assert_tl(&other, "After 1st insert");

                            insert_tl_entry(2, Foo("b".to_owned() + &si), control);

                            let other = HashMap::from([
                                (1, Foo("a".to_owned() + &si)),
                                (2, Foo("b".to_owned() + &si)),
                            ]);
                            assert_tl(&other, "After 2nd insert");
                        }
                    })
                })
                .collect::<Vec<_>>();

            thread::sleep(Duration::from_millis(50));

            let spawned_tids = spawned_tids.try_read().unwrap();
            println!("spawned_tid={:?}", spawned_tids);

            hs.into_iter().for_each(|h| h.join().unwrap());

            println!("after h.join(): {:?}", control);
        });

        {
            let spawned_tids = spawned_tids.try_read().unwrap();
            let map_0 = HashMap::from([(1, Foo("a0".to_owned())), (2, Foo("b0".to_owned()))]);
            let map_1 = HashMap::from([(1, Foo("a1".to_owned())), (2, Foo("b1".to_owned()))]);
            let map = HashMap::from([
                (spawned_tids[0].clone(), map_0),
                (spawned_tids[1].clone(), map_1),
            ]);

            {
                let lock = control.lock();
                let acc = &lock.0;
                assert!(acc.eq(&map), "Accumulator check: acc={acc:?}, map={map:?}");
            }
        }
    }
}
