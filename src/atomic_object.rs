use crate::{AtomicShared, Shared, Guard, Tag};
use crate::Arc;

use portable_atomic::Ordering;

/// A wrapper for `AtomicShared::from(Shared::new_unchecked(T))`.
/// but that does not allow to creating nullptr, and does not requires "static lifetime".
///
/// it internally uses 2-Arc to preventing clone multi un-associated object in memory.
/// that is global uniquely unless "the original value has been cloned out-side".
#[derive(Debug, Clone)]
pub struct AtomicObject<T> {
    inner: Arc<AtomicShared<Arc<T>>>,
}

impl<T> AtomicObject<T> {
    /// creates [AtomicObject] with provided value.
    pub fn new(obj: T) -> Self {
        Self {
            inner: Arc::new(
                       AtomicShared::new_forced(
                           Arc::new(obj)
                       )
                   ),
        }
    }
    /// # Panic
    /// call to this will always panic.
    ///
    /// any NULL value or "un-initializd state" is strict disallowed.
    pub fn null() -> Self {
        unimplemented!("any NULL value or 'un-initializd state' is strict disallowed.");
    }

    pub fn get_shared(&self, guard: &Guard) -> Shared<Arc<T>> {
        self.inner.get_shared(Ordering::Relaxed, &guard)
                    .expect("Bug: `.inner` should never be NULL!")
    }

    /// get current value.
    pub fn get(&self) -> Arc<T> {
        let guard = Guard::new();
        let shared = self.get_shared(&guard);
        shared.get_guarded_ref(&guard) // &Arc<T>
            .clone() // Arc<T>
    }

    /// set "currently value" to specified one. this actual "replace" the older to the newer one.
    ///
    /// so you cannot really modify it (unless it implements "inner-mutabliy" such as [core::cell::Cell]).
    /// instead, we doing replace inner by newer one, then marking the older one as a junk.
    ///
    /// if the EBR collector does not working properly, this may causes memory-leak (but it is not a critical error).
    ///
    /// __**NOTE: it should never causes "double-free" (if you found this please report it).**__
    pub fn set(&self, obj: T) -> bool {
        let arc_obj = Arc::new(obj);

        let guard = Guard::new();
        let old_ptr = {
            let old_shared = self.get_shared(&guard);
            old_shared.get_guarded_ptr(&guard)
        };

        #[cfg(test)]
            eprintln!("old_ptr: .tag={:?} | .as_ptr={:?} | as_underlying_ptr={:?}",
                      old_ptr.tag(),
                      old_ptr.as_ptr(),
                      old_ptr.as_underlying_ptr()
            );

        let new_shared = unsafe { Shared::new_unchecked(arc_obj) };

        self.inner.compare_exchange(
            old_ptr,
            (Some(new_shared), Tag::None),
            Ordering::Relaxed,
            Ordering::Relaxed,
            &guard
        ).is_ok()
    }
}

unsafe impl<T: Send> Send for AtomicObject<T> {}
unsafe impl<T: Sync> Sync for AtomicObject<T> {}

use core::panic::UnwindSafe;
impl<T: UnwindSafe> UnwindSafe for AtomicObject<T> {}

#[cfg(test)]
mod test {
    use super::*;
    use core::time::Duration;

    #[test]
    fn atom_obj() {
        let a = AtomicObject::new("first");
        assert!(a.get().as_ref() == &"first");

        let t1 = {
            let a = a.clone();
            std::thread::spawn(move ||{
                while a.get().as_ref() != &"success" {
                    let r = a.set("intermediate");
                    eprintln!("set im = {r}");

                    std::thread::sleep(Duration::from_millis(20));
                }
            })
        };
        let t2 = {
            let a = a.clone();
            std::thread::spawn(move ||{
                std::thread::sleep(Duration::from_millis(50));
                let r = a.set("success");
                eprintln!("set succ = {r}");
            })
        };

        std::thread::sleep(Duration::from_millis(25));
        let x = a.get();
        let x = x.as_ref();
        assert!(x != &"first");
        assert!(x == &"intermediate" || x == &"success");

        if x == &"success" {
            std::thread::sleep(Duration::from_millis(50));

            assert!(a.get().as_ref() == &"intermediate");
        } else if x == &"intermediate" {
            std::thread::sleep(Duration::from_millis(50));
            assert!(a.get().as_ref() == &"success");
        } else {
            panic!("unexpected other str");
        }

        a.set("final");
        let y = a.get();
        let y = y.as_ref();

        assert!(x != y);
        assert!(y == &"final");
    }
}
