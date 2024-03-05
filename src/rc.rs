use crate::Collectible;
use crate::Arc;

use core::fmt::Debug;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ptr::NonNull;
use portable_atomic::AtomicUsize;
use portable_atomic::Ordering::{self, Relaxed};

/// [`RefCounted`] stores an instance of type `T`, and a union of a link to the next
/// [`Collectible`] or the reference counter.
pub struct _RefCounted<T> {
    instance: T,
    next_or_refcnt: LinkOrRefCnt,
}

/// replace by Arc
pub struct RefCounted<T> {
    instance:       Arc<T>,
    next_or_refcnt: Result<Arc<Self>, Arc<AtomicUsize>>,
}
impl<T: Debug> Debug for RefCounted<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter)
        -> Result<(), core::fmt::Error>
    {
        f.debug_struct("RefCounted")
        .field("instance", &self.instance)
        .field("refcnt", &self.ref_cnt())
        .finish()
    }
}
impl<T> Deref for RefCounted<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.instance.as_ref()
    }
}

impl<T> Clone for RefCounted<T> {
    fn clone(&self) -> Self {
        let instance       = self.instance.clone();
        let next_or_refcnt = self.next_or_refcnt.clone();

        let cloned = Self { instance, next_or_refcnt };
        cloned.add_ref(); // FIXME is this should exists?

        cloned
    }
}

impl<T: Collectible> RefCounted<T> {
    /// Creates a new [`RefCounted`] that allows ownership sharing.
    #[inline]
    pub const fn new_shared(t: T) -> Self {
        Self {
            instance:       Arc::new(t),
            next_or_refcnt: Err(Arc::new(AtomicUsize::new(1))),
        }
    }

    /// Creates a new [`RefCounted`] that disallows reference counting.
    ///
    /// The reference counter field is never used until the instance is retired.
    #[inline]
    pub const fn new_unique(t: T) -> Self {
        Self {
            instance:       Arc::new(t),
            next_or_refcnt: Err(Arc::new(AtomicUsize::new(0))),
        }
    }

    /// Tries to add a strong reference to the underlying instance.
    ///
    /// `order` must be as strong as `Acquire` for the caller to correctly validate the newest
    /// state of the pointer.
    #[inline]
    pub fn try_add_ref(&self, order: Ordering) -> bool {
        self.ref_cnt()
            .fetch_update(
                order,
                order,
                |r| {
                    if r % 2 == 1 {
                        Some(r + 2)
                    } else {
                        None
                    }
                },
            )
            .is_ok()
    }

    /// Returns a mutable reference to the instance if the number of owners is `1`.
    #[inline]
    pub fn get_mut_shared(&mut self) -> Option<&mut T> {
        if self.ref_cnt().load(Relaxed) == 1 {
            Some(&mut self.instance)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the instance if it is uniquely owned.
    #[inline]
    pub fn get_mut_unique(&mut self) -> &mut T {
        assert_eq!(self.ref_cnt().load(Relaxed), 0);
        &mut self.instance
    }

    /// Adds a strong reference to the underlying instance.
    #[inline]
    pub fn add_ref(&self) {
        let mut current = self.ref_cnt().load(Relaxed);
        loop {
            debug_assert_eq!(current % 2, 1);
            debug_assert!(current <= usize::MAX - 2, "reference count overflow");
            match self
                .ref_cnt()
                .compare_exchange(current, current + 2, Relaxed, Relaxed)
            {
                Ok(_) => break,
                Err(actual) => {
                    current = actual;
                }
            }
        }
    }

    /// Drops a strong reference to the underlying instance.
    ///
    /// Returns `true` if it the last reference was dropped.
    #[inline]
    pub fn drop_ref(&self) -> bool {
        // It does not have to be a load-acquire as everything's synchronized via the global
        // epoch.
        let mut current = self.ref_cnt().load(Relaxed);
        loop {
            debug_assert_ne!(current, 0);
            let new = if current <= 1 { 0 } else { current - 2 };
            match self
                .ref_cnt()
                .compare_exchange(current, new, Relaxed, Relaxed)
            {
                Ok(_) => break,
                Err(actual) => {
                    current = actual;
                }
            }
        }
        current == 1
    }

    /// Returns a reference to its reference count.
    #[inline]
    pub fn ref_cnt(&self) -> Arc<AtomicUsize> {
        let mut cur: &Self = &self;
        while let Ok(ref next) = cur.next_or_refcnt {
            cur = next.as_ref();
        }
        if let Err(ref cnt) = cur.next_or_refcnt {
            cnt.clone()
        } else {
            panic!("unexpected Ok val in linked list `RefCounted`");
        }
    }

    /// Returns a `dyn Collectible` reference to `self`.
    #[inline]
    pub fn as_collectible(&self) -> &dyn Collectible {
        self
    }
}
impl<T: Collectible> Collectible for RefCounted<T> {
    #[inline]
    fn next_ptr_mut(&mut self) -> &mut Option<NonNull<dyn Collectible>> {
        let inst = Arc::get_mut(&mut self.instance)?;
        &mut NonNull::new(inst as *mut _)
    }
}

/// [`LinkOrRefCnt`] is a union of a dynamic pointer to [`Collectible`] and a reference count.
pub(crate) union LinkOrRefCnt {
    next: Option<NonNull<dyn Collectible>>,
    refcnt: ManuallyDrop<(AtomicUsize, usize)>,
}

impl LinkOrRefCnt {
    #[inline]
    const fn new_shared() -> Self {
        LinkOrRefCnt {
            refcnt: ManuallyDrop::new((AtomicUsize::new(1), 0)),
        }
    }

    #[inline]
    const fn new_unique() -> Self {
        LinkOrRefCnt {
            refcnt: ManuallyDrop::new((AtomicUsize::new(0), 0)),
        }
    }
}

