//! ### **NOTE: un-tested. use at your own risk.**
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

pub mod atomic_owned;
pub use atomic_owned::*;

pub mod atomic_shared;
pub use atomic_shared::*;

pub mod guard;
pub use guard::*;

pub mod collectible;
pub use collectible::*;

pub mod owned;
pub use owned::*;

pub mod ptr;
pub use ptr::*;

pub mod shared;
pub use shared::*;

pub mod tag;
pub use tag::*;

pub mod collector;

pub mod ref_counted;
pub use ref_counted::*;

pub mod dropguard;
pub use dropguard::*;
pub use dropguard as drop_guard;
pub use dropguard as exit_guard;
pub use dropguard as defer;
pub use dropguard as defer_guard;
pub use dropguard as destruct_guard;

// importing some alloc types now
extern crate alloc;
pub(crate) use alloc::{
    sync::Arc,
    boxed::Box,
};

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

