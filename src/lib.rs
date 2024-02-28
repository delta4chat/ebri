//! **NOTE: un-tested. use at your own risk.**
//!
//! # ebri (ebr-integrated)
//! a `no-std` EBR (Epoch-Based Reclamation) implementation.
//! thanks to the idea from [`scc::ebr`](https://docs.rs/scc/2.0.16/scc/ebr/).
//!
//! The epoch consensus algorithm and the use of memory barriers and RMW semantics are similar to
//! that of [`crossbeam_epoch`](https://docs.rs/crossbeam-epoch/), however the API set is vastly
//! different, for instance, `unsafe` blocks are not required to read an instance subject to EBR.

// #![no_std] by default (unless feature "std" enabled)
#![cfg_attr(not(feature = "std"), no_std)]

mod atomic_owned;
pub use atomic_owned::AtomicOwned;

mod atomic_shared;
pub use atomic_shared::AtomicShared;

mod guard;
pub use guard::Guard;

mod collectible;
pub use collectible::Collectible;

mod owned;
pub use owned::Owned;

mod ptr;
pub use ptr::Ptr;

mod shared;
pub use shared::Shared;

mod tag;
pub use tag::Tag;

pub mod collector;
pub mod ref_counted;
pub mod exit_guard;

/// Suspends the garbage collector of the current thread.
///
/// If returns `false` if there is an active [`Guard`] in the thread. Otherwise, it passes all its
/// retired instances to a free flowing garbage container that can be cleaned up by other threads.
///
/// # Examples
///
/// ```
/// use ebri::{suspend, Guard, Shared};
///
/// assert!(suspend());
///
/// {
///     let shared: Shared<usize> = Shared::new(47);
///     let guard = Guard::new();
///     shared.release(&guard);
///     assert!(!suspend());
/// }
///
/// assert!(suspend());
///
/// let new_shared: Shared<usize> = Shared::new(17);
/// let guard = Guard::new();
/// new_shared.release(&guard);
/// ```
#[inline]
#[must_use]
pub fn suspend() -> bool {
    collector::Collector::pass_garbage()
}

