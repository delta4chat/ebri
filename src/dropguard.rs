//! This module implements a simplified, yet safe version of
//! [`scopeguard`](https://crates.io/crates/scopeguard).

use core::ops::{Deref, DerefMut};
use core::fmt::{Debug, Formatter};
use portable_atomic::{AtomicBool, Ordering::Relaxed};

use crate::{AtomicOwned, Guard};


/// [`DropGuard`] captures the environment and invokes the defined closure at the end of the scope.
pub struct DropGuard<T, D: FnOnce(&mut T)> {
    val_dropcb: Option<(T, D)>, // inner-value & dropping-callback.
    should_run: AtomicOwned<ShouldRun>,
}

//pub use DropGuard as ScopeGuard;
pub use DropGuard as ExitGuard;
pub use DropGuard as DeferGuard;
pub use DropGuard as Defer;
pub use DropGuard as DestructGuard;

impl<T, D> Clone for DropGuard<T, D>
where
    T: Clone,
    D: Clone + FnOnce(&mut T),
{
    fn clone(&self) -> Self {
        let val_dropcb = Option::clone(&self.val_dropcb);
        let should_run = self.should_run.clone();
        Self {
            val_dropcb,
            should_run,
        }
    }
}

impl<T, D> Debug for DropGuard<T, D>
where
    T: Debug,
    D: Debug + FnOnce(&mut T),
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
        f.debug_struct("DropGuard")
        .field("val", &self.val())
        .field("should_run", &self.should_run)
        .finish()
    }
}

impl<T, D> DropGuard<T, D>
where
    D: FnOnce(&mut T),
{
    fn val(&self) -> Option<&T> {
        if let Some(ref vd) = self.val_dropcb {
            Some(&vd.0)
        } else {
            None
        }
    }

    /// Creates a new [`DropGuard`] with the specified variables captured.
    #[inline]
    pub fn new(captured: T, cb: D) -> Self {
        Self {
            val_dropcb: Some((captured, cb)),
            should_run: AtomicOwned::new(RunAlways),
        }
    }

    pub fn should_run(&self, case: u16) -> bool {
        let guard = Guard::new();
        self.should_run.load(Relaxed, &guard) // <- AtomicOwned
            .as_ref().unwrap() // <- Ptr
            .should_run(case)  // <- ShouldRun
    }

    fn set_should_run(&self, sr: ShouldRun) {
        self.should_run.store(sr, Relaxed);
    }

    pub fn always(&self) {
        self.set_should_run(RunAlways)
    }
    pub fn on_success(&self) {
        self.set_should_run(RunIfSuccess)
    }
    pub fn on_failed(&self) {
        self.set_should_run(RunIfFailed)
    }
    pub fn on_unwind(&self) {
        self.set_should_run(RunIfUnwind)
    }

    /// drop then return inner.
    fn drop_return(&mut self, case: u16) -> Option<T>{
        if let Some((mut val, destructor)) = Option::take(&mut self.val_dropcb) {
            if self.should_run(case) {
                (destructor)(&mut val)
            }
            Some(val)
        } else {
            None
        }
    }

    /// destruct and return the inner value, then set this [DropGuard] "used".
    /// this is seems likes to `Arc::into_inner` or `Vec::drain`.
    pub fn destruct(&mut self) -> Option<T> {
        self.drop_return(ShouldRun::BY_MANUALLY)
    }
}

impl<T, D> Drop for DropGuard<T, D>
where
    D: FnOnce(&mut T),
{
    #[inline]
    fn drop(&mut self) {
        self.drop_return(ShouldRun::BY_RUSTDROP);
    }
}

#[macro_export]
macro_rules! defer {
    ($($t:tt)*) => {
        let _guard = $crate::guard((), |()| { $($t)* });
    };
}

pub const RunAlways:    ShouldRun = ShouldRun::Always;
pub const RunIfSuccess: ShouldRun = ShouldRun::OnSuccess;
pub const RunIfFailed:  ShouldRun = ShouldRun::OnFailed;
pub const RunIfUnwind:  ShouldRun = ShouldRun::OnUnwind;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ShouldRun {
    /// Always run on scope exit, it does not care whatever thread panicking.
    ///
    /// "Always" run: on regular exit from a scope or on unwinding from a panic.
    /// Can not run on abort, process exit, and other catastrophic events where
    /// destructors do not run.
    Always,

    /// only Run on manually calls [DropGuard::destruct]
    Manually,

    /// Run on regular scope exit (when not unwinding) or manually destruct.
    ///
    /// Requires crate feature `std`.
    OnSuccess,

    /// only Run on unexpected scope exit (only through unwinding).
    ///
    /// Requires crate feature `std`.
    OnUnwind,

    /// Alias for [ShouldRun::OnUnwind].
    OnFailed,
}

impl ShouldRun {
    const BY_MANUALLY: u16 = 0xff01;
    const BY_RUSTDROP: u16 = 0xa0de;

    fn hint_manually(set: Option<bool>) -> bool {
        #[cfg(feature = "dropguard-manually")]
        return false;

        static HINT: AtomicBool = AtomicBool::new(true);
        if let Some(v) = set {
            HINT.store(v, Relaxed);
        }
        HINT.load(Relaxed)
    }
    pub fn slient_manually() {
        Self::hint_manually(Some(false));
    }

    /// return True if this [DropGuard] should run it's destructor, unless return False.
    ///
    /// in the case of `#[no_std]`, this just return True by default (unless `ShouldRun::Manually`).
    ///
    /// or, if `std` available, this will checking if panic by call [`std::thread::panicking`](https://doc.rust-lang.org/1.76.0/std/thread/fn.panicking.html) function.
    pub fn should_run(self, case: u16) -> bool {
        if self == Self::Always {
            return true;
        }
        if self == Self::Manually {
            if Self::hint_manually(None) {
                log::error!("be carefully to using [ShouldRun::Manually] because it often causes mistake or bugs. if you are make sure to use this, call ShouldRun::slient_manually() before destructing, or enable feature 'dropguard_manually'.");
            }
            if case == Self::BY_MANUALLY {
                return true;
            } else {
                return false;
            }
        }

        #[cfg(feature = "std")]
        {
            let panicking = std::thread::panicking();

            if self == Self::OnSuccess {
                return !panicking;
            }
            if self == Self::OnUnwind || self == Self::OnFailed {
                return panicking;
            }

            // this should never execute.
            unreachable!();
        }

        // no std library.
        true
    }
}

impl<T, D> Deref for DropGuard<T, D>
where
    D: FnOnce(&mut T),
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &self.val_dropcb.as_ref().unwrap_unchecked().0 }
    }
}

impl<T, D> DerefMut for DropGuard<T, D>
where
    D: FnOnce(&mut T),
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut self.val_dropcb.as_mut().unwrap_unchecked().0 }
    }
}

