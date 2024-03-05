// warn instead of deny
#![warn(clippy::not_unsafe_ptr_arg_deref)]

// https://github.com/rust-lang/rust-clippy/issues/12402
#![allow(clippy::transmutes_expressible_as_ptr_casts)]

use core::mem::transmute;

/// [`Tag`] is a four-state `Enum` that can be **embedded in a pointer** as the two least
/// significant bits of the pointer value.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Tag {
    /// Not tagged.
    None   = 0,
    /// The first bit is tagged.
    First  = 1,
    /// The second bit is tagged.
    Second = 2,
    /// Both bits are tagged.
    Both   = 3,
}

impl Tag {
    /// Interprets the [`Tag`] as an integer.
    #[inline]
    pub const fn value(&self) -> u8 {
        match self {
            Self::None   => 0,
            Self::First  => 1,
            Self::Second => 2,
            Self::Both   => 3,
        }
    }

    /// Interprets from an integer as the [`Tag`].
    #[inline]
    pub const fn from_value(v: u8) -> Result<Self, u8> {
        match v {
            0 => Ok(Self::None),
            1 => Ok(Self::First),
            2 => Ok(Self::Second),
            3 => Ok(Self::Both),
            _ => Err(v),
        }
    }

    /// Returns the tag embedded in the pointer.
    #[inline]
    pub const fn into_tag<P>(ptr: *const P) -> Self {
        let addr = unsafe { transmute::<_, usize>(ptr) };
        let x = addr & 1;
        let y = addr & 2;
        match (x == 1, y == 2) {
            (false, false) => Tag::None,
            (true,  false) => Tag::First,
            (false, true)  => Tag::Second,
            (true,  true)  => Tag::Both,
        }
    }

    /// Sets a tag, overwriting any existing tag in the pointer.
    #[inline]
    pub const fn update_tag<P>(ptr: *const P, tag: Tag) -> *const P {
        let addr = unsafe { transmute::<_, usize>(ptr) };
        let val  = tag.value() as usize; // u8 as usize
        let p = addr & (!3);
        let p = p | val;
        p as *const P
    }

    /// Returns the pointer with the tag bits erased.
    #[inline]
    pub const fn unset_tag<P>(ptr: *const P) -> *const P {
        let addr = unsafe { transmute::<_, usize>(ptr) };
        let p = addr & (!3);
        p as *const P
    }
}

macro_rules! _tag_tryfrom_impl {
    ($t:ty) => {
        impl TryFrom<$t> for Tag {
            type Error = $t;

            #[inline]
            fn try_from(val: $t) -> Result<Tag, Self::Error> {
                if val > 3 { return Err(val); }
                match Tag::from_value(val as u8) {
                    Ok(v)  => { Ok(v)  }
                    Err(e) => { Err(e as $t) }
                }
            }
        }
    }
}
_tag_tryfrom_impl!(u8);
_tag_tryfrom_impl!(usize);

macro_rules! _tag_into_impl {
    ($t:ty) => {
        impl From<Tag> for $t {
            #[inline]
            fn from(t: Tag) -> $t {
                t.value()   as $t
            }
        }
    }
}
_tag_into_impl!(u8); _tag_into_impl!(u16); _tag_into_impl!(u32); _tag_into_impl!(u64); _tag_into_impl!(u128);
_tag_into_impl!(i8); _tag_into_impl!(i16); _tag_into_impl!(i32); _tag_into_impl!(i64); _tag_into_impl!(i128);
_tag_into_impl!(usize);
_tag_into_impl!(isize);

