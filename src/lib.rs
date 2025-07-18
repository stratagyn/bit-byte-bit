//! An `n`-bit string represented as &lceil; `n/8` &rceil; bytes.
//!
//! ## Instantiation
//!
//! Constructors defined in the [Bits] implementation generate bit strings
//! with a length that is either input-defined, or in the case of [Bits::new],
//! `8` times the length of the iterator.
//!
//! Constructors defined by the [From](Bits::from) or
//! [FromIterator](Bits::from_iter) traits generate bit strings with a length
//! based on the input. If a collection of `bool`, the length will be equal to
//! that of the input. If the input is a collection of `u8`, the length counts
//! all bits up to and including the most significant one bit.
//!
//! ```
//! # use bit_byte_bit::Bits;
//!
//! let bits = Bits::new([0x0A, 0x0B, 0x0C]);
//!
//! assert_eq!(bits.len(), 24);
//!
//! let bits_no_lz = Bits::from([0x0A, 0x0B, 0x0C]);
//!
//! assert_eq!(bits_no_lz.len(), 20);
//!
//! let aligned_bits = Bits::aligned(16, [0x0A, 0x0B, 0x0C]);
//!
//! assert_eq!(aligned_bits.len(), 32);
//!
//! let packed_bits = Bits::packed([0x0A, 0x0B, 0x0C]);
//!
//! assert_eq!(packed_bits, Bits::from([0xBA, 0x0C]));
//!
//! let bools = Bits::from([true, false, true, false, false, true]);
//!
//! assert_eq!(bools, Bits::slice(&[0x25], 6));
//!
//! let slice = Bits::take(&[0x0A, 0x0B, 0x0C], 3, 9);
//!
//! assert_eq!(slice, Bits::from([0x61, 0x01]));
//!```
//!
//! The [bits!] macro is also provided for convenience, wrapping the constructors:
//! * [Bits::new]
//! * [Bits::aligned]
//! * [Bits::ones]
//! * [Bits::packed]
//! * [Bits::zeros]
//!
//! ```
//! # use bit_byte_bit::{Bits, bits};
//! let bits = bits![0x0A, 0x0B, 0x0C];
//!
//! assert_eq!(bits, Bits::new([0x0A, 0x0B, 0x0C]));
//!
//! let repeated = bits![8; 0x0F; 20];
//!
//! assert_eq!(repeated, Bits::new([0x0F; 20]));
//!
//! let aligned_bits = bits![0x0A, 0x0B, 0x0C; => 16];
//!
//! assert_eq!(aligned_bits.len(), 32);
//!
//! let ones = bits![1; 20];
//!
//! assert_eq!(ones, Bits::ones(20));
//!
//! let packed_bits = bits![0x0A, 0x0B, 0x0C; %];
//!
//! assert_eq!(packed_bits, Bits::from([0xBA, 0x0C]));
//!
//! let zeros = bits![0; 20];
//!
//! assert_eq!(zeros, Bits::zeros(20));
//!
//! ```
//!
//! ## Indexing
//!
//! [Bits::i] can be used to access an individual bit. Bits can be [set](Bits::set) to one,
//! [reset](Bits::reset) to zero, or [toggled](Bits::toggle).
//!
//! ```
//! # use bit_byte_bit::{Bits};
//! let mut bits = Bits::new([0x0A, 0x0B, 0x0C]);
//!
//! assert_eq!(bits.i(0), 0);
//! assert_eq!(bits.i(1), 1);
//!
//! bits.set(0);
//! bits.reset(1);
//!
//! assert_eq!(bits.i(0), 1);
//! assert_eq!(bits.i(1), 0);
//!
//! bits.toggle(0);
//! bits.toggle(1);
//!
//! assert_eq!(bits.i(0), 0);
//! assert_eq!(bits.i(1), 1);
//! ```
//!
//! ## Bitwise Operations
//!
//! Bit strings support [and](Bits::and), [or](Bits::or), [not](Bits::complement),
//! [xor](Bits::xor), [left](Bits::shifted_left) and [right](Bits::shifted_right)
//! shifting, as well as, [left](Bits::rotated_left), and [right](Bits::rotated_right)
//! rotation.
//!
//! ```
//! # use bit_byte_bit::{Bits};
//! let x = Bits::new([0x20, 0x30, 0x40]);
//! let y = Bits::new([0xA0, 0xB0, 0xC0]);
//!
//! assert_eq!(x.and(&y), Bits::new([0x20, 0x30, 0x40]));
//! assert_eq!(x.complement(), Bits::new([0xDF, 0xCF, 0xBF]));
//! assert_eq!(x.or(&y), Bits::new([0xA0, 0xB0, 0xC0]));
//! assert_eq!(x.xor(&y), Bits::new([0x80, 0x80, 0x80]));
//!
//! let bits = Bits::from([0x0A, 0x0B, 0x0C]);
//!
//! assert_eq!(bits.len(), 20);
//! assert_eq!(bits.shifted_left(17), Bits::slice(&[0x00, 0x00, 0x04], 20));
//! assert_eq!(bits.shifted_right(17), Bits::slice(&[0x06, 0x00, 0x00], 20));
//! assert_eq!(bits.rotated_left(4), Bits::slice(&[0xAC, 0xB0, 0x00], 20));
//! assert_eq!(bits.rotated_right(4), Bits::slice(&[0xB0, 0xC0, 0x0A], 20));
//! ```
//!
//! ## Iteration
//!
//! Iteration can be done bit-by-bit, or byte-by-byte using:
//! * [Bits::iter]
//! * [Bits::iter_from]
//! * [Bits::into_iter]
//! * [Bits::bytes] (via `&[u8]::iter`)
//! * [Bits::into_bytes]
//!
//!```
//! # use bit_byte_bit::{Bits};
//! let x = Bits::new([0xAB, 0xCD, 0xEF]);
//!
//! let mut ones = 0;
//!
//! for bit in x.iter() { if bit == 1 { ones += 1; } }
//!
//! assert_eq!(ones, 17);
//!
//! ones = 0;
//!
//! for bit in x.iter_from(13) { if bit == 1 { ones += 1; } }
//!
//! assert_eq!(ones, 9);
//!
//! let mut y = x.bytes().iter();
//!
//! assert_eq!(y.next(), Some(&0xAB));
//! ```
//!
//! ## Note about endianness
//!
//! While the library does not implement any notion of endianness, indexing and methods ending
//! in either `_left` or `_right` assume bit<sub>0</sub> of an n-bit string is the most right bit,
//! while bit<sub>n-1</sub> is most left.

use std::ptr::NonNull;
use std::{alloc, ptr, slice};
use std::alloc::Layout;
use std::cmp::Ordering;
use std::fmt::{Binary, Debug, Display, Formatter};
use std::iter::FusedIterator;
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign,
    Div, Not, Shl, ShlAssign, Shr, ShrAssign
};


macro_rules! bitop {
    ($self:expr, $op:tt, $rhs:expr) => {
        unsafe {
            let (mut min, mut nbytes, mut nbits) = ($self.size(), $rhs.size(), $rhs.nbits);
            let (mut padding, mut mask) = ($rhs.padding, $rhs.mask);
            let aptr = $self.words.as_ptr_const();
            let bptr = $rhs.words.as_ptr_const();

            if $rhs.nbits < $self.nbits {
                (min, nbytes, nbits) = ($rhs.size(), $self.size(), $self.nbits);
                (padding, mask) = ($self.padding, $self.mask);
            }

            let layout = Layout::array::<u8>(nbytes).unwrap();
            let result = alloc::alloc(layout);

            for i in 0..min { ptr::write(result.add(i), *aptr.add(i) $op *bptr.add(i)); }

            match $self.size().cmp(&$rhs.size()) {
                Ordering::Greater => for i in $rhs.size()..$self.size() {
                    ptr::write(result.add(i), *aptr.add(i))
                },
                Ordering::Less => for i in $self.size()..$rhs.size() {
                    ptr::write(result.add(i), *bptr.add(i));
                },
                _ => ()
            }

            *result.add(nbytes - 1) &= mask;

            let bytes = RawBytes { bytes: NonNull::new(result).unwrap(), cap: nbytes, nbytes };

            Bits { words:bytes, mask, nbits, padding }
        }
    };
    (assign; $self:expr, $op:tt, $rhs:expr) => {
        unsafe {
            let aptr = $self.words.as_ptr_mut();
            let bptr = $rhs.words.as_ptr_const();
            let (lsize, rsize) = ($self.size(), $rhs.size());
            let min = if rsize < lsize { rsize } else { lsize };

            for i in 0..min { *aptr.add(i) $op *bptr.add(i); }

            if $self.nbits < $rhs.nbits {
                let aptr = $self.words.as_ptr_mut();

                $self.words.expand_to(rsize);

                for i in lsize..rsize { ptr::write(aptr.add(i), *bptr.add(i)); }

                $self.mask = $rhs.mask;
                $self.nbits = $rhs.nbits;
                $self.words.nbytes = rsize;
                $self.padding = $rhs.padding;

                if lsize > 0 { *aptr.add(lsize - 1) &= $self.mask; }
            }
        }
    };
}

macro_rules! divrem8 {
    ($n:expr) => { ($n >> 3, $n & 7) };
    (ceil; $n:expr) => { (1 + (($n - 1) >> 3), $n & 7) };
}

macro_rules! mask {
    ($shift:expr) => {
        if $shift == 0 { 0xFF } else { ((1 << $shift) - 1) as u8 }
    };
}

macro_rules! pointer {
    ($size:expr) => {{
        let layout = Layout::array::<u8>($size).unwrap();

        assert!(layout.size() <= isize::MAX as usize, "Allocation too large");

        let pointer = alloc::alloc(layout);

        pointer
    }};
    ($fill:expr; $size:expr) => {{
        let layout = Layout::array::<u8>($size).unwrap();

        assert!(layout.size() <= isize::MAX as usize, "Allocation too large");

        let pointer = alloc::alloc(layout);

        for i in 0..$size { ptr::write(pointer.add(i), $fill); }

        pointer
    }};
}


fn trim(mut bytes: Vec<u8>) -> Vec<u8> {
    let (mut upper_bound, mut i) = (bytes.len().saturating_sub(1), 0);

    while i < upper_bound {
        if bytes[i] == 0 {
            bytes.remove(i);
            upper_bound -= 1;
        } else {
            let clz = bytes[i].leading_zeros() as usize;

            if clz > 0 {
                let (mask, low) = ((1 << clz) - 1, 8 - clz);

                bytes[i] |= (bytes[i + 1] & mask) << low;
                bytes[i + 1] >>= clz;

                if bytes[i + 1] == 0 {
                    bytes.remove(i + 1);
                    upper_bound -= 1;

                    if bytes[i].leading_zeros() == 0 { i += 1; }
                } else {
                    i += 1;
                }
            } else {
                i += 1;
            }
        }
    }

    bytes
}


struct RawBytes {
    cap: usize,
    bytes: NonNull<u8>,
    nbytes: usize
}

impl RawBytes {
    fn as_ptr_const(&self) -> *const u8 { self.bytes.as_ptr().cast_const() }

    fn as_ptr_mut(&self) -> *mut u8 { self.bytes.as_ptr() }

    fn expand_to(&mut self, nbytes: usize) {
        let new_layout = Layout::array::<u8>(nbytes).unwrap();

        assert!(new_layout.size() <= isize::MAX as usize, "Allocation too large");

        let pointer = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<u8>(self.cap).unwrap();
            let old_pointer = self.bytes.as_ptr();

            unsafe { alloc::realloc(old_pointer, old_layout, new_layout.size()) }
        };

        self.bytes = match NonNull::new(pointer) {
            Some(p) => p,
            None => alloc::handle_alloc_error(new_layout)
        };

        self.cap = nbytes;
    }

    fn shift_right(&mut self, end: usize, mask: u8, up: usize, down: usize) {
        unsafe {
            let pointer = self.bytes.as_ptr();

            for i in 0..(end - 1) {
                *pointer.add(i) >>= down;
                *pointer.add(i) |= (*pointer.add(i + 1) & mask) << up;
            }

            *pointer.add(end - 1) >>= down;
        }
    }

    fn shift_right_from(&mut self, start: usize, end: usize, mask: u8, up: usize, down: usize) {
        unsafe {
            let pointer = self.bytes.as_ptr();

            for i in start..end {
                *pointer.add(i - 1) |= (*pointer.add(i) & mask) << up;
                *pointer.add(i) >>= down;
            }
        }
    }

    fn shrink_to(&mut self, nbytes: usize) {
        if self.cap <= nbytes { return; }

        let old_layout = Layout::array::<u8>(self.cap).unwrap();
        let old_pointer = self.bytes.as_ptr();

        unsafe {
            for i in nbytes..self.nbytes { ptr::read(old_pointer.add(i)); }

            if nbytes == 0 {
                alloc::dealloc(old_pointer, old_layout);
                self.bytes = NonNull::dangling();
            } else {
                let new_layout = Layout::array::<u8>(nbytes).unwrap();
                let pointer = alloc::realloc(old_pointer, old_layout, new_layout.size());

                self.bytes = match NonNull::new(pointer) {
                    Some(p) => p,
                    None => alloc::handle_alloc_error(new_layout)
                };
            }
        }

        self.cap = nbytes;
        self.nbytes = nbytes;
    }
}

impl Drop for RawBytes {
    fn drop(&mut self) {

        if self.cap != 0 {
            unsafe {
                alloc::dealloc(self.bytes.as_ptr(), Layout::array::<u8>(self.cap).unwrap());
            }
        }
    }
}

unsafe impl Send for RawBytes {}

unsafe impl Sync for RawBytes {}



pub struct Bits {
    words: RawBytes,
    mask: u8,
    nbits: usize,
    padding: usize,
}

impl Bits {
    /// Creates a bit string from a sequence of bytes.
    ///
    /// To ignore leading zeros use [Bits::from] or [Bits::from_iter].
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::new([0x0A, 0x0B, 0x0C, 0x00]);
    ///
    /// assert_eq!(x.len(), 32);
    /// ```
    pub fn new<I: IntoIterator<Item = u8>>(bits: I) -> Self {
        let mut bytes = bits.into_iter().collect::<Vec<u8>>();

        match bytes.len() {
            0 => Bits::empty(),
            nbytes => {
                bytes.shrink_to(nbytes);

                let cap = bytes.capacity();
                let pointer = bytes.as_mut_ptr();

                std::mem::forget(bytes);

                let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap, nbytes };

                Bits { words: bytes, mask: 0xFF, nbits: nbytes << 3, padding: 0 }
            }
        }
    }

    /// Creates a bit string with an aligned length.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::aligned(17, [0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x.len(), 34);
    /// assert_eq!(x, Bits::slice(&[0x0A, 0x0B, 0x0C, 0x00, 0x00], 34));
    /// ```
    pub fn aligned<I: IntoIterator<Item = u8>>(units: usize, bits: I) -> Self {
        match units {
            0 => Bits::empty(),
            1 => Bits::from_iter(bits),
            8 => Bits::new(bits),
            units => {
                let mut bytes = bits.into_iter().collect::<Vec<u8>>();
                let mut nbits = bytes.len() << 3;
                let overflow = nbits % units;

                if overflow > 0 {
                    nbits += units - overflow;

                    for _ in 0..(1 + ((units - 1) >> 3)) { bytes.push(0); }
                }

                let nbytes = bytes.len();

                if nbytes == 0 {
                    Bits::empty()
                } else {
                    bytes.shrink_to(nbytes);

                    let cap = bytes.capacity();
                    let pointer = bytes.as_mut_ptr();

                    std::mem::forget(bytes);

                    let overflow = nbits & 7;

                    let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap, nbytes };

                    Bits { words: bytes, mask: mask!(overflow), nbits, padding: (8 - overflow) & 7 }
                }
            }
        }
    }

    /// Creates an empty bit string.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::empty();
    ///
    /// assert_eq!(x.len(), 0);
    /// ```
    pub fn empty() -> Self {
        let bytes = RawBytes { bytes: NonNull::dangling(), cap: 0, nbytes: 0 };

        Bits { words: bytes, mask: 0xFF, nbits: 0, padding: 0 }
    }

    /// Creates a bit string of ones.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::ones(4);
    ///
    /// assert_eq!(x.len(), 4);
    /// assert_eq!(x, Bits::from([0x0F]));
    /// ```
    pub fn ones(length: usize) -> Self {
        match length {
            0 => Bits::empty(),
            length => unsafe {
                let nbytes = 1 + ((length - 1) >> 3);
                let overflow = length & 7;
                let padding = (8 - overflow) & 7;
                let mask = mask!(overflow);
                let pointer = pointer![0xFFu8; nbytes];

                *pointer.add(nbytes - 1) &= mask;

                let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap: nbytes, nbytes };

                Bits { words: bytes, mask, nbits: length, padding }
            }
        }
    }

    /// Creates a bit string by concatenating a slice of bytes removing leading zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::packed([0x00, 0x00, 0x00]);
    ///
    /// assert_eq!(x1, Bits::empty());
    ///
    /// let x2 = Bits::packed([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x2, Bits::from([0xBA, 0x0C]));
    /// assert_eq!(x2.len(), 12);
    /// ```
    pub fn packed<I: IntoIterator<Item = u8>>(bytes: I) -> Self {
        Bits::from(trim(bytes.into_iter().collect::<Vec<u8>>()))
    }

    /// Creates a bit string by copying a given number of bits from a slice of bytes.
    ///
    /// When the length is greater than the available number of bits in the source,
    /// the result is padded with zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::slice(&[], 17);
    ///
    /// assert_eq!(x1, Bits::zeros(17));
    ///
    /// let x2 = Bits::slice(&[0x0A, 0x0B, 0x0C], 0);
    ///
    /// assert_eq!(x2, Bits::empty());
    ///
    /// let x3 = Bits::slice(&[0x0A, 0x0B, 0x0C], 19);
    ///
    /// assert_eq!(x3, Bits::from([0x0A, 0x0B, 0x04]));
    ///
    /// let x4 = Bits::slice(&[0x00, 0x00, 0x00], 19);
    ///
    /// assert_eq!(x4, Bits::zeros(19));
    /// ```
    pub fn slice(src: &[u8], length: usize) -> Self { Bits::take(src, 0, length) }

    /// Creates a bit string by copying a given range of bits from a slice of bytes.
    ///
    /// When the length is greater than the available number of bits in the source,
    /// the result is padded with zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::take(&[], 1, 17);
    ///
    /// assert_eq!(x1, Bits::zeros(17));
    ///
    /// let x2 = Bits::take(&[0x0A, 0x0B, 0x0C], 1, 0);
    ///
    /// assert_eq!(x2, Bits::empty());
    ///
    /// let x3 = Bits::take(&[0x0A, 0x0B, 0x0C], 25, 17);
    ///
    /// assert_eq!(x3, Bits::zeros(17));
    ///
    /// let x4 = Bits::take(&[0x0A, 0x0B, 0x0C], 1, 17);
    ///
    /// assert_eq!(x4, Bits::slice(&[0x85, 0x05, 0x00], 17));
    ///
    /// let x5 = Bits::take(&[0x0A, 0x0B, 0x0C], 1, 16);
    ///
    /// assert_eq!(x5, Bits::new([0x85, 0x05]));
    ///
    /// let x6 = Bits::take(&[0x00, 0x00, 0x00], 1, 17);
    ///
    /// assert_eq!(x6, Bits::zeros(17));
    /// ```
    pub fn take(src: &[u8], start: usize, length: usize) -> Self {
        if length == 0 { return Bits::empty(); }

        let nbytes_src = src.len();

        if nbytes_src == 0 || start >= (nbytes_src << 3) { return Bits::zeros(length); }

        let (start_byte, start_idx) = divrem8!(start);
        let (nbytes, overflow) = divrem8!(ceil; length);
        let mask = mask!(overflow);
        let mut bytes = vec![0; nbytes];
        let take_all = nbytes >= (nbytes_src - start_byte);

        if start_idx > 0 {
            let shift_mask = (1 << start_idx) - 1;
            let upper_length = 8 - start_idx;
            let end_byte = if take_all { nbytes_src - 1 } else { nbytes };

            for i in start_byte..end_byte {
                bytes[i - start_byte] = src[i] >> start_idx;
                bytes[i - start_byte] |= (src[i + 1] & shift_mask) << upper_length;
            }

            if take_all { bytes[nbytes_src - start_byte - 1] = src[nbytes_src - 1] >> start_idx; }
        } else {
            let end_byte = if take_all { nbytes_src } else { nbytes };

            for i in start_byte..end_byte { bytes[i - start_byte] = src[i] }
        }

        bytes[nbytes - 1] &= mask;

        let pointer = bytes.as_mut_ptr();

        std::mem::forget(bytes);

        let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap: nbytes, nbytes };

        Bits { words: bytes, mask, nbits: length, padding: (8 - overflow) & 7 }
    }

    /// Creates a bit string of zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::zeros(4);
    ///
    /// assert_eq!(x.len(), 4);
    /// assert_eq!(x, Bits::from([false, false, false, false]));
    /// ```
    pub fn zeros(length: usize) -> Self {
        match length {
            0 => Bits::empty(),
            length => unsafe {
                let nbytes = 1 + ((length - 1) >> 3);
                let overflow = length & 7;
                let padding = (8 - overflow) & 7;
                let mask = mask!(overflow);
                let pointer = pointer![0u8; nbytes];
                let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap: nbytes, nbytes };

                Bits { words: bytes, mask, nbits: length, padding }
            }
        }
    }

    /// Pads a bit string until the length is a multiple of the given unit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.align(16);
    ///
    /// assert_eq!(x, Bits::new([0x0A, 0x0B, 0x0C, 0x00]));
    /// assert_eq!(x.len(), 32);
    /// ```
    pub fn align(&mut self, unit: usize) {
        match unit {
            0 | 1 => (),
            8 => {
                self.nbits = self.size() << 3;
                self.padding = 0;
            },
            unit if (self.nbits % unit) == 0 => (),
            unit => self.push_zeros(unit - (self.nbits % unit))
        }
    }

    /// Whether all bits are one.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::empty();
    ///
    /// assert!(x1.all());
    ///
    /// let x2 = Bits::from([0x0F]);
    ///
    /// assert!(x2.all());
    ///
    /// let x3 = Bits::new([0x0F]);
    ///
    /// assert!(!x3.all());
    pub fn all(&self) -> bool {
        match self.size() {
            0 => true,
            n => unsafe {
                let pointer = self.words.as_ptr_const();

                for i in 0..(n - 1) {
                    if *pointer.add(i) != 0xFF { return false; }
                }

                (*pointer.add(n - 1) & self.mask) == self.mask
            }
        }
    }

    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1.and(&y1), Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2.and(&y2);
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    pub fn and(&self, rhs: &Bits) -> Bits {
        unsafe {
            let (mut min, mut nbytes) = (self.size(), rhs.size());
            let mut nbits = rhs.nbits;
            let (mut padding, mut mask) = (rhs.padding, rhs.mask);
            let aptr = self.words.as_ptr_const();
            let bptr = rhs.words.as_ptr_const();

            if rhs.nbits < self.nbits {
                (min, nbytes, nbits) = (rhs.size(), self.size(), self.nbits);
                (padding, mask) = (self.padding, self.mask);
            }

            let layout = Layout::array::<u8>(nbytes).unwrap();
            let result = alloc::alloc(layout);

            for i in 0..min {
                ptr::write(result.add(i), *aptr.add(i) & *bptr.add(i));
            }

            for i in min..nbytes { ptr::write(result.add(i), 0); }

            *result.add(nbytes - 1) &= mask;

            let bytes = RawBytes { bytes: NonNull::new(result).unwrap(), cap: nbytes, nbytes };

            Bits { words: bytes, mask, nbits, padding }
        }
    }

    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1.and_mut(&y1);
    ///
    /// assert_eq!(x1, Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2.and_mut(&y2);
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn and_mut(&mut self, rhs: &Bits) {
        match self.size().cmp(&rhs.size()) {
            Ordering::Equal => unsafe {
                let aptr = self.words.as_ptr_mut();
                let bptr = self.words.as_ptr_const();
                let last_a = *aptr.add(self.size() - 1) & self.mask;
                let last_b = *bptr.add(rhs.size() - 1) & rhs.mask;

                for i in 0..(self.size() - 1) { *aptr.add(i) &= *bptr.add(i); }

                *aptr.add(self.size() - 1) = last_a & last_b;
            },
            Ordering::Less => unsafe {
                self.words.expand_to(rhs.size());

                let aptr = self.words.as_ptr_mut();
                let bptr = self.words.as_ptr_const();
                let last_a = *aptr.add(self.size() - 1) & self.mask;

                for i in 0..(self.size() - 1) { *aptr.add(i) &= *bptr.add(i); }

                *aptr.add(self.size() - 1) = last_a & *bptr.add(self.size() - 1);

                for i in self.size()..rhs.size() { ptr::write(aptr.add(i), 0); }
            },
            Ordering::Greater => unsafe {
                let aptr = self.words.as_ptr_mut();
                let bptr = self.words.as_ptr_const();

                for i in 0..(rhs.size() - 1) { *aptr.add(i) &= *bptr.add(i); }

                *aptr.add(rhs.size() - 1) &= *bptr.add(rhs.size() - 1) & rhs.mask;

                for i in rhs.size()..self.size() { *aptr.add(i) = 0; }
            }
        }

        if self.nbits < rhs.nbits {
            self.nbits = rhs.nbits;
            self.words.nbytes = rhs.size();
            self.padding = rhs.padding;
            self.mask = rhs.mask;
        }
    }

    /// Whether at least one bit is one.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::empty();
    ///
    /// assert!(!x1.any());
    ///
    /// let x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert!(x2.any());
    ///
    /// let x3 = Bits::zeros(20);
    ///
    /// assert!(!x3.any());
    pub fn any(&self) -> bool { self.nbits > 0 && self.bytes().iter().any(|&b| b > 0u8) }

    /// State of a byte.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B]);
    ///
    /// assert_eq!(x.byte(0), 0x0A);
    /// assert_eq!(x.byte(1), 0x0B);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B]);
    ///
    /// assert_eq!(x.byte(2), 0x0C);
    pub fn byte(&self, i: usize) -> u8 {
        assert!(i < self.size(), "Index out of bounds");

        unsafe { *self.words.as_ptr_mut().add(i) }
    }

    /// Underlying bytes
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x = Bits::new([0xAB, 0xCD, 0xEF]);
    /// let y = x.bytes().iter().cloned().collect::<Vec<u8>>();
    ///
    /// assert_eq!(y, vec![0xAB, 0xCD, 0xEF]);
    /// ```
    pub fn bytes(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.words.as_ptr_const(), self.size()) }
    }

    /// Flips every bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x.complement(), Bits::slice(&[0xF5, 0xF4, 0x03], 20));
    /// ```
    pub fn complement(&self) -> Bits {
        match self.size() {
            0 => Bits::empty(),
            nbytes => unsafe {
                let pointer = self.words.as_ptr_mut();
                let layout = Layout::array::<u8>(nbytes).unwrap();
                let clone = alloc::alloc(layout);

                for i in 0..nbytes { ptr::write(clone.add(i), !*pointer.add(i)); }

                *clone.add(nbytes - 1) &= self.mask;

                let bytes = RawBytes { bytes: NonNull::new(clone).unwrap(), cap: nbytes, nbytes };

                Bits { words: bytes, mask: self.mask, nbits: self.nbits, padding: self.padding }
            }
        }
    }

    /// Flips every bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.complement_mut();
    ///
    /// assert_eq!(x1, Bits::slice(&[0xF5, 0xF4, 0x03], 20));
    /// ```
    pub fn complement_mut(&mut self) {
        unsafe {
            let aptr = self.words.as_ptr_mut();

            for i in 0..self.size() { *aptr.add(i) = !*aptr.add(i); }

            *aptr.add(self.size() - 1) &= self.mask;
        }
    }

    /// Shifts out upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.consume_left(4);
    /// assert_eq!(x1.len(), 16);
    /// assert_eq!(x1, Bits::new([0x0A, 0x0B]));
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.consume_left(4);
    /// assert_eq!(x2.len(), 20);
    /// assert_eq!(x2, Bits::from([0x0A, 0x0B, 0x0C]));
    /// ```
    pub fn consume_left(&mut self, count: usize) {
        match (self.size(), count) {
            (0, _) | (_, 0) => (),
            (n, count) if count >= self.nbits => unsafe {
                let pointer = self.words.as_ptr_mut();

                for i in 0..n { *pointer.add(i) = 0; }
            },
            (n, count) => {
                let (extra, byte_len) = (count & 7, count >> 3);

                if byte_len > 0 {
                    unsafe {
                        let pointer = self.words.as_ptr_mut();

                        for i in (n - byte_len)..n { ptr::read(pointer.add(i)); }

                        self.words.nbytes -= byte_len;

                        *pointer.add(self.size() - 1) &= self.mask;
                    }
                }

                if extra > 0 {
                    unsafe {
                        let overflow = 8 - self.padding;
                        let pointer = self.words.as_ptr_mut();

                        let mask = match extra.cmp(&overflow) {
                            Ordering::Less => (1 << (overflow - extra)) - 1,
                            Ordering::Greater => (1 << (8 + overflow - extra)) - 1,
                            Ordering::Equal => 0,
                        };

                        *pointer.add(self.size() - 1) &= mask;
                    }
                }

                self.nbits -= count;
                let overflow = self.nbits & 7;
                self.padding = (8 - overflow) & 7;
                self.mask = mask!(overflow);

                self.shrink_to_fit();

                unsafe { *self.words.as_ptr_mut().add(self.size() - 1) &= self.mask; }
            }
        }
    }

    /// Shifts out lower bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.consume_right(4);
    ///
    /// assert_eq!(x1, Bits::from([0xB0, 0xC0]));
    /// assert_eq!(x1.len(), 16);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.consume_right(4);
    ///
    /// assert_eq!(x2, Bits::slice(&[0xB0, 0xC0, 0x00], 20));
    /// assert_eq!(x2.len(), 20);
    /// ```
    pub fn consume_right(&mut self, count: usize) {
        match (self.size(), count) {
            (0, _) | (_, 0) => (),
            (_, count) if count >= self.nbits => {
                self.words.shrink_to(0);
                self.nbits = 0;
                self.padding = 0;
            },
            (_, count) => {
                unsafe {
                    let shift_bytes = count >> 3;
                    let pointer = self.words.as_ptr_mut();

                    ptr::copy(pointer.add(shift_bytes), pointer, self.size() - shift_bytes);

                    self.words.shrink_to(self.size() - shift_bytes);

                    self.words.nbytes -= shift_bytes;
                    self.nbits -= count;
                    let new_overflow = self.nbits & 7;
                    self.padding = 8 - new_overflow;
                    self.mask = mask!(new_overflow);

                    let count_overflow = count & 7;

                    if count_overflow > 0 {
                        self.words.shift_right(
                            self.size(),
                            (1 << count_overflow) - 1,
                            8 - count_overflow,
                            count_overflow
                        );

                        self.shrink_to_fit();
                    }
                }
            }
        }
    }

    /// The number of zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([15, 15, 15]);
    ///
    /// assert_eq!(x.count_zeros(), 8);
    ///
    /// x = Bits::new([15, 15, 15]);
    ///
    /// assert_eq!(x.count_zeros(), 12);
    /// ```
    pub fn count_zeros(&self) -> usize {
        match self.size() {
            0 => 0,
            n => unsafe {
                let pointer = self.words.as_ptr_const();
                let mut sum = (*pointer.add(n - 1) & self.mask).count_zeros();

                for i in 0..(n - 1) { sum += (*pointer.add(i)).count_zeros(); }

                (sum as usize) - self.padding
            }
        }
    }

    /// Adds upper bit padding to a bit string.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.extend_left(&[0x0D, 0x0E, 0x0F]);
    ///
    /// assert_eq!(x1.len(), 44);
    /// assert_eq!(x1, Bits::slice(&[0x0A, 0x0B, 0xDC, 0xE0, 0xF0, 0x00], 44));
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.extend_left(&[0x0D, 0x0E, 0x0F]);
    ///
    /// assert_eq!(x2.len(), 48);
    /// assert_eq!(x2, Bits::new([0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F]));
    /// ```
    pub fn extend_left(&mut self, bytes: &[u8]) {
        let mut nbytes = bytes.len();

        while nbytes > 0 && bytes[nbytes - 1] == 0 { nbytes -= 1; }

        if nbytes == 0 { return; }

        unsafe {
            self.words.expand_to(self.size() + nbytes);

            let pointer = self.words.as_ptr_mut().add(self.size());

            for i in 0..nbytes { ptr::write(pointer.add(i), bytes[i]); }

            if self.padding > 0 {
                let overflow = (8 - self.padding) & 7;
                let mask = mask!(self.padding);
                let end = self.size() + nbytes;

                self.words.shift_right_from(self.size(), end, mask, overflow, self.padding);
            }

            self.words.nbytes += nbytes;
            self.nbits += nbytes << 3;
            *pointer.add(self.size() - 1) &= self.mask;
        }
    }

    /// Adds lower bit padding to a bit string.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::empty();
    ///
    /// x1.extend_right(&[0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x1.len(), 24);
    /// assert_eq!(x1, Bits::new([0x0A, 0x0B, 0x0C]));
    ///
    /// let mut x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.extend_right(&[0x0D, 0x0E, 0x0F]);
    ///
    /// assert_eq!(x2.len(), 44);
    /// assert_eq!(x2, Bits::from([0x0D, 0x0E, 0x0F, 0x0A, 0x0B, 0x0C]));
    /// ```
    pub fn extend_right(&mut self, bytes: &[u8]) {
        unsafe {
            let nbytes_padding = bytes.len();
            let nbytes = self.size() + nbytes_padding;

            self.words.expand_to(nbytes);

            let pointer = self.words.as_ptr_mut();

            ptr::copy(pointer, pointer.add(nbytes_padding), self.size());

            for i in 0..nbytes_padding { ptr::write(pointer.add(i), bytes[i]); }

            self.words.nbytes = nbytes;
            self.nbits += nbytes_padding << 3;
            *pointer.add(self.size() - 1) &= self.mask;
        }
    }

    /// The number of ones.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([15, 15, 15]);
    ///
    /// assert_eq!(x.hamming_weight(), 12);
    /// ```
    pub fn hamming_weight(&self) -> usize {
        match self.size() {
            0 => 0,
            n => unsafe {
                let pointer = self.words.as_ptr_const();
                let mut sum = (*pointer.add(n - 1) & self.mask).count_ones();

                for i in 0..(n - 1) { sum += (*pointer.add(i)).count_ones(); }

                sum as usize
            }
        }
    }

    /// State of a bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0F]);
    ///
    /// assert_eq!(x.i(3), 1u8);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0F]);
    ///
    /// assert_eq!(x.i(4), 0);
    /// ```
    pub fn i(&self, i: usize) -> u8 {
        assert!(i < self.nbits, "Index out of bounds");

        unsafe { (*self.words.as_ptr_mut().add(i >> 3) >> (i & 7)) & 1 }
    }

    /// An iterator over the individual bits
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x = Bits::new([0xAB, 0xCD, 0xEF]);
    /// let y = x.into_bytes().collect::<Vec<u8>>();
    ///
    /// assert_eq!(y, vec![0xAB, 0xCD, 0xEF]);
    /// ```
    pub fn into_bytes(self) -> IntoBytes {
        let (iter, bytes) = unsafe {
            (Bytes::new(self.bytes()), ptr::read(&self.words))
        };

        std::mem::forget(self);

        IntoBytes { iter, _bytes: bytes}
    }

    /// An iterator over the individual bits
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits, Iter};
    /// let x = Bits::new([0xAB, 0xCD, 0xEF]);
    /// let mut ones = 0;
    ///
    /// for bit in x.iter() { if bit == 1 { ones += 1; } }
    ///
    /// assert_eq!(ones, 17);
    /// ```
    pub fn iter(&self) -> Iter { Iter::new(self, 0) }

    /// An iterator over the individual bits
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits, Iter};
    /// let x = Bits::new([0xAB, 0xCD, 0xEF]);
    /// let mut ones = 0;
    ///
    /// for bit in x.iter_from(0) { if bit == 1 { ones += 1; } }
    ///
    /// assert_eq!(ones, 17);
    ///
    /// ones = 0;
    ///
    /// for bit in x.iter_from(13) { if bit == 1 { ones += 1; } }
    ///
    /// assert_eq!(ones, 9);
    /// ```
    pub fn iter_from(&self, index: usize) -> Iter {
        assert!(index <= self.nbits, "Index out of bounds");

        Iter::new(self, index)
    }

    /// The number of leading ones.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0xFF, 0x03]);
    ///
    /// assert_eq!(x1.leading_ones(), 10);
    ///
    /// let x2 = Bits::new([0x0A, 0xFF, 0x0B]);
    ///
    /// assert_eq!(x2.leading_ones(), 0);
    /// ```
    pub fn leading_ones(&self) -> usize {
        match self.size() {
            0 => 0,
            n => unsafe {
                let pointer = self.words.as_ptr_const();
                let last_byte = *pointer.add(n - 1) & self.mask;
                let ones = (last_byte << self.padding).leading_ones() as usize;

                if ones < (8 - self.padding) { return ones; }

                let mut i = n - 2;

                while i > 0 && *pointer.add(i) == 0xFF { i -= 1; }

                ones + ((self.size() - i - 2) << 3) + ((*pointer.add(i)).leading_ones() as usize)
            }
        }
    }

    /// The number of leading zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x00, 0x00]);
    ///
    /// assert_eq!(x1.leading_zeros(), 0);
    ///
    /// let x2 = Bits::zeros(20);
    ///
    /// assert_eq!(x2.leading_zeros(), 20);
    /// ```
    pub fn leading_zeros(&self) -> usize {
        match self.size() {
            0 => 0,
            1 => unsafe {
                let byte = *self.words.as_ptr_const() & self.mask;
                (byte.leading_zeros() as usize) - self.padding
            },
            n => unsafe {
                let pointer = self.words.as_ptr_const();
                let last_byte = *pointer.add(n - 1) & self.mask;
                let zeros = (last_byte.leading_zeros() as usize) - self.padding;

                if (zeros + self.padding) < 8 { return zeros; }

                let mut i = n - 2;

                while i > 0 && *pointer.add(i) == 0 { i -= 1; }

                zeros + ((n - i - 2) << 3) + ((*pointer.add(i)).leading_zeros() as usize)
            }
        }
    }

    /// The number of bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::empty();
    ///
    /// assert_eq!(x1.len(), 0);
    ///
    /// let x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x2.len(), 20);
    ///
    /// let x3 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x3.len(), 24);
    ///
    /// let x4 = Bits::slice(&[0x0A, 0x0B, 0x0C], 17);
    ///
    /// assert_eq!(x4.len(), 17);
    /// ```
    pub fn len(&self) -> usize { self.nbits }

    /// Whether all bits are zero.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::empty();
    ///
    /// assert!(!x1.any());
    ///
    /// let x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert!(x2.any());
    ///
    /// let x3 = Bits::zeros(20);
    ///
    /// assert!(!x3.any());
    pub fn none(&self) -> bool {
        unsafe {
            let pointer = self.words.as_ptr_const();

            for i in 0..(self.size() - 1) {
                if *pointer.add(i) != 0 { return false; }
            }

            (*pointer.add(self.size() - 1) & self.mask) == 0
        }
    }

    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1.or(&y1), Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2.or(&y2);
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    pub fn or(&self, rhs: &Bits) -> Bits { bitop!(self, |, rhs) }

    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1.or_mut(&y1);
    ///
    /// assert_eq!(x1, Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2.or_mut(&y2);
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn or_mut(&mut self, rhs: &Bits) { bitop!(assign; self, |=, rhs) }

    /// Shifts out the most significant bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::empty();
    ///
    /// assert_eq!(x1.pop_left(), 0u8);
    ///
    /// let mut x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x2.pop_left(), 1u8);
    /// assert_eq!(x2.len(), 19);
    ///
    /// let mut x3 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x3.pop_left(), 0u8);
    /// assert_eq!(x3.len(), 23);
    /// ```
    pub fn pop_left(&mut self) -> u8 {
        match self.size() {
            0 => 0,
            n => unsafe {
                let pointer = self.words.as_ptr_mut();
                self.nbits -= 1;

                match self.padding {
                    0 => {
                        let bit = *pointer.add(n - 1) >> 7;

                        *pointer.add(n - 1) &= 0x7F;

                        bit
                    },
                    7 => {
                        let bit = ptr::read(pointer.add(n - 1)) & 1;

                        self.words.nbytes -= 1;
                        self.padding = 0;

                        bit
                    },
                    alignment => {
                        let shift = 8 - alignment - 1;
                        let bit = *pointer.add(n- 1) >> shift;
                        *pointer.add(n - 1) &= mask!(shift);
                        self.padding += 1;

                        bit
                    }
                }
            }
        }
    }

    /// Shifts out the least significant bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::empty();
    ///
    /// assert_eq!(x1.pop_right(), 0u8);
    ///
    /// let mut x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x2.pop_right(), 0u8);
    /// assert_eq!(x2.len(), 19);
    /// assert_eq!(x2.pop_right(), 1u8);
    /// ```
    pub fn pop_right(&mut self) -> u8 {
        match self.size() {
            0 => 0,
            _ => {
                self.nbits -= 1;
                self.padding = (self.padding + 1) & 7;

                unsafe {
                    let pointer = self.words.as_ptr_mut();
                    let bit = *pointer & 1;

                    self.words.shift_right(self.size(), 1, 7, 1);

                    if self.nbits == 0 {
                        ptr::read(pointer);
                        self.words.nbytes = 0;
                    }

                    bit
                }
            }
        }
    }

    /// Adds upper bit padding to a bit string.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.push_left(true, 17);
    ///
    /// assert_eq!(x1.len(), 37);
    /// assert_eq!(x1, Bits::from([0x0A, 0x0B, 0xFC, 0xFF, 0x1F]));
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.push_left(false, 17);
    ///
    /// assert_eq!(x2.len(), 41);
    /// assert_eq!(x2, Bits::slice(&[0x0A, 0x0B, 0x0C, 0x00, 0x00, 0x00], 41));
    /// ```
    pub fn push_left(&mut self, bit: bool, count: usize) {
        if bit { self.push_ones(count); } else { self.push_zeros(count); }
    }

    /// Adds upper bit padding to a bit string.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([15, 15, 15]);
    ///
    /// x.push_byte_left(15, 2);
    ///
    /// assert_eq!(x.len(), 36);
    /// assert_eq!(x, Bits::slice(&[15, 15, 255, 240, 0], 36));
    ///
    /// x = Bits::new([15, 15, 15]);
    ///
    /// x.push_byte_left(31, 2);
    ///
    /// assert_eq!(x.len(), 40);
    /// assert_eq!(x, Bits::new([15, 15, 15, 31, 31]));
    /// ```
    pub fn push_byte_left(&mut self, word: u8, count: usize) {
        if count == 0 { return; }

        match word {
            0 => self.push_zeros(count << 3),
            0xFF => self.push_ones(count << 3),
            word => unsafe {
                self.words.expand_to(self.size() + count);

                let pointer = self.words.as_ptr_mut().add(self.size());

                for i in 0..count { ptr::write(pointer.add(i), word); }

                *pointer.add(self.size() - 1) &= self.mask;

                if self.padding > 0 && word != 0 {
                    self.words.shift_right_from(
                        self.size(),
                        self.size() + count,
                        mask!(self.padding),
                        (8 - self.padding) & 7,
                        self.padding
                    );
                }

                self.words.nbytes += count;
                self.nbits += count << 3;

                self.shrink_to_fit()
            }
        }
    }

    /// Adds lower bit padding to a bit string.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.push_right(true, 4);
    ///
    /// assert_eq!(x.len(), 24);
    /// assert_eq!(x, Bits::from([0xAF, 0xB0, 0xC0]));
    /// ```
    pub fn push_right(&mut self, bit: bool, count: usize)  {
        match count {
            0 => (),
            n => if bit { self.cons_bit(n, 0xFF); } else { self.cons_bit(n, 0) }
        }
    }

    /// Adds lower bit padding to a bit string.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([15, 15, 15]);
    ///
    /// x.push_byte_right(31, 2);
    ///
    /// assert_eq!(x.len(), 36);
    /// assert_eq!(x, Bits::from([31, 31, 15, 15, 15]));
    /// ```
    pub fn push_byte_right(&mut self, word: u8, count: usize) {
        let nbytes = self.size() + count;
        self.words.expand_to(nbytes);

        unsafe {
            let pointer = self.words.as_ptr_mut();

            ptr::copy(pointer, pointer.add(count), self.size());

            for i in 0..count { ptr::write(pointer.add(i), word); }
        }

        self.words.nbytes = nbytes;
        self.nbits += count << 3;
    }

    /// Creates a bit string by copying a range of bits.
    ///
    /// When the length is greater than the available number of bits in the source,
    /// the result is padded with zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::empty();
    /// let y1 = x1.range(1, 18);
    ///
    /// assert_eq!(y1, Bits::zeros(17));
    ///
    /// let x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let y2 = x2.range(1, 0);
    ///
    /// assert_eq!(y2, Bits::empty());
    ///
    /// let x3 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let y3 = x3.range(1, 18);
    ///
    /// assert_eq!(y3, Bits::slice(&[0x85, 0x05, 0x00], 17));
    ///
    /// let x4 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let y4 = x4.range(1, 17);
    ///
    /// assert_eq!(y4, Bits::new([0x85, 0x05]));
    ///
    /// let x5 = Bits::zeros(24);
    /// let y5 = x5.range(8, 24);
    ///
    /// assert_eq!(y5, Bits::zeros(16));
    /// ```
    pub fn range(&self, start: usize, end: usize) -> Self {
        if end <= start { Bits::empty() } else {
            Bits::take(self.bytes(), start, end - start)
        }
    }

    /// Sets a bit to zero.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::new([15]);
    ///
    /// assert_eq!(x.i(3), 1u8);
    ///
    /// x.reset(3);
    ///
    /// assert_eq!(x.i(3), 0u8);
    /// ```
    pub fn reset(&mut self, i: usize) {
        if i < self.nbits {
            unsafe { *self.words.as_ptr_mut().add(i >> 3) &= !(1 << (i & 7)); }
        }
    }

    /// Sets the state of a range of bits to zero.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// x1.reset_bits(7, 10);
    ///
    /// assert_eq!(x1, Bits::from([0x0A, 0x00, 0x0C]));
    ///
    /// let mut x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// x2.reset_bits(8, 12);
    ///
    /// assert_eq!(x2, Bits::slice(&[0x0A, 0x00, 0x00], 20));
    /// ```
    ///
    /// ``` should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.reset_bits(21, 14);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.reset_bits(7, 14);
    /// ```
    pub fn reset_bits(&mut self, start: usize, count: usize) {
        assert!(count <= self.nbits && start <= self.nbits - count, "Invalid range");

        let end = if count > (self.nbits - start) { self.nbits } else { start + count };
        let mut start = start;
        let low_overflow = 8 - (start & 7);

        unsafe {
            let pointer = self.words.as_ptr_mut();

            if low_overflow < 8 {
                *pointer.add(start >> 3) &= !(((1 << low_overflow) - 1) << (start & 7));
                start = start + low_overflow;
            }

            let bytes = (end - start) >> 3;
            let start_byte = start >> 3;

            for i in start_byte..(start_byte + bytes) { *pointer.add(i) = 0 }

            let overflow = (end - start) & 7;

            if overflow > 0 { *pointer.add(start_byte + bytes) &= !((1 << overflow) - 1); }

            if self.size() > 0 { *pointer.add(self.words.nbytes - 1) &= self.mask; }
        }
    }

    /// Sets the state of a byte to zero.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.reset_byte(1);
    ///
    /// assert_eq!(x, Bits::from([0x0A, 0x00, 0x0C]));
    ///
    /// x.reset_byte(2);
    ///
    /// assert_eq!(x, Bits::slice(&[0x0A, 0x00, 0x00], 20));
    ///```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.reset_byte(3);
    /// ```
    pub fn reset_byte(&mut self, i: usize) {
        assert!(i < self.size(), "Index out of range");

        unsafe {
            let pointer = self.words.as_ptr_mut();
            *pointer.add(i) = 0;

            if self.size() > 0 { *pointer.add(self.words.nbytes - 1) &= self.mask; }
        }
    }

    /// Sets the state of a range of bytes to zero.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.reset_bytes(1, 2);
    ///
    /// assert_eq!(x, Bits::slice(&[0x0A, 0x00, 0x00], 20));
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.reset_bytes(3, 2);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.reset_bytes(0, 4);
    /// ```
    pub fn reset_bytes(&mut self, start: usize, count: usize) {
        assert!(count <= self.size() && start <= self.size() - count, "Invalid range");

        unsafe {
            let pointer = self.words.as_ptr_mut();

            let end = if count > (self.size() - start) { self.size() } else { start + count };

            for i in start..end { *pointer.add(i) = 0; }

            if end == self.size() && self.padding > 0 { *pointer.add(end - 1) &= self.mask; }
        }
    }

    /// Reverses the order of the bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.reverse();
    ///
    /// assert_eq!(x1, Bits::slice(&[0x03, 0x0D, 0x05], 20));
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.reverse();
    ///
    /// assert_eq!(x2, Bits::new([0x30, 0xD0, 0x50]));
    /// ```
    pub fn reverse(&mut self) {
        match self.size() {
            0 => (),
            n => unsafe {
                let aptr = self.words.as_ptr_mut();
                *aptr.add(n - 1) &= self.mask;

                let mid = n >> 1;
                let upper_bound = n - 1;

                for i in 0..mid {
                    let a = (*aptr.add(i)).reverse_bits();

                    *aptr.add(i) = (*aptr.add(upper_bound - i)).reverse_bits();
                    *aptr.add(upper_bound - i) = a;
                }

                if (n & 1) == 1 { *aptr.add(mid) = (*aptr.add(mid)).reverse_bits() }

                if self.padding > 0 {
                    let overflow = 8 - self.padding;
                    let mask = (1 << overflow) - 1;

                    self.words.shift_right(self.size(), mask, self.padding, overflow);
                }
            }
        }
    }

    /// Rotates bits to the left.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.rotate_left(4);
    ///
    /// assert_eq!(x1, Bits::slice(&[0xAC, 0xB0, 0x00], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.rotate_left(4);
    ///
    /// assert_eq!(x2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn rotate_left(&mut self, count: usize) {
        match (self.size(), count) {
            (0, _) | (_, 0) => (),
            (n, count) => {
                unsafe { *self.words.as_ptr_mut().add(n - 1) &= self.mask; }

                let reduced_count = count % self.nbits;
                let other = self.shifted_right(self.nbits - reduced_count);

                self.shift_left(reduced_count);
                self.or_mut(&other);
            }
        }
    }

    /// Rotates bits to the left.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x1.rotated_left(4), Bits::slice(&[0xAC, 0xB0, 0x00], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x2.rotated_left(4), Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn rotated_left(&self, count: usize) -> Self {
        match (self.size(), count) {
            (0, _) | (_, 0) => self.clone(),
            (n, count) => {
                unsafe { *self.words.as_ptr_mut().add(n - 1) &= self.mask; }

                let reduced_count = count % self.nbits;
                let mut other = self.shifted_left(reduced_count);

                other |= self.shifted_right(self.nbits - reduced_count);

                other
            }
        }
    }

    /// Rotates bits to the right.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.rotate_right(4);
    ///
    /// assert_eq!(x1, Bits::slice(&[0xB0, 0xC0, 0x0A], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.rotate_right(4);
    ///
    /// assert_eq!(x2, Bits::new([0xB0, 0xC0, 0xA0]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn rotate_right(&mut self, count: usize) {
        match (self.size(), count) {
            (0, _) | (_, 0) => (),
            (n, count) => {
                unsafe { *self.words.as_ptr_mut().add(n - 1) &= self.mask; }

                let reduced_count = count % self.nbits;
                let other = self.shifted_left(self.nbits - reduced_count);

                self.shift_right(reduced_count);
                self.or_mut(&other);
            }
        }
    }

    /// Rotates bits to the right.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x1.rotated_right(4), Bits::slice(&[0xB0, 0xC0, 0x0A], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x2.rotated_right(4), Bits::new([0xB0, 0xC0, 0xA0]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn rotated_right(&self, count: usize) -> Self {
        match (self.size(), count) {
            (0, _) | (_, 0) => self.clone(),
            (n, count) => {
                unsafe { *self.words.as_ptr_mut().add(n - 1) &= self.mask; }

                let reduced_count = count % self.nbits;
                let mut other = self.shifted_right(reduced_count);

                other |= self.shifted_left(self.nbits - reduced_count);

                other
            }
        }
    }

    /// Sets a bit to one.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::new([15]);
    ///
    /// assert_eq!(x.i(4), 0u8);
    ///
    /// x.set(4);
    ///
    /// assert_eq!(x.i(4), 1u8);
    /// ```
    pub fn set(&mut self, i: usize) {
        assert!(i < self.nbits, "Index out of range");

        unsafe { *self.words.as_ptr_mut().add(i >> 3) |= 1 << (i & 7); }
    }

    /// Sets the state of a range of bits to one.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// x1.set_bits(7, 10);
    ///
    /// assert_eq!(x1, Bits::from([0x8A, 0xFF, 0x0D]));
    ///
    /// let mut x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// x2.set_bits(8, 12);
    ///
    /// assert_eq!(x2, Bits::slice(&[0x0A, 0xFF, 0x0F], 20));
    /// ```
    ///
    /// ``` should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.set_bits(21, 14);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.set_bits(7, 14);
    /// ```
    pub fn set_bits(&mut self, start: usize, count: usize) {
        assert!(count <= self.nbits && start <= self.nbits - count, "Invalid range");

        let end = if count > (self.nbits - start) { self.nbits } else { start + count };
        let mut start = start;
        let low_overflow = 8 - (start & 7);

        unsafe {
            let pointer = self.words.as_ptr_mut();

            if low_overflow < 8 {
                *pointer.add(start >> 3) |= ((1 << low_overflow) - 1) << (start & 7);
                start = start + low_overflow;
            }

            let bytes = (end - start) >> 3;
            let start_byte = start >> 3;

            for i in start_byte..(start_byte + bytes) { *pointer.add(i) = 0xFF }

            let overflow = (end - start) & 7;

            if overflow > 0 { *pointer.add(start_byte + bytes) |= (1 << overflow) - 1; }
        }
    }

    /// Sets the state of a byte to all ones.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.set_byte(1);
    ///
    /// assert_eq!(x, Bits::from([0x0A, 0xFF, 0x0C]));
    ///
    /// x.set_byte(2);
    ///
    /// assert_eq!(x, Bits::slice(&[0x0A, 0xFF, 0x0F], 20));
    ///```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_byte(3);
    /// ```
    pub fn set_byte(&mut self, i: usize) {
        assert!(i < self.size(), "Index out of range");

        unsafe {
            let pointer = self.words.as_ptr_mut();
            *pointer.add(i) = 0xFF;
            *pointer.add(self.size() - 1) &= self.mask;
        }
    }

    /// Sets the state of a range of bytes to all ones.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.set_bytes(1, 2);
    ///
    /// assert_eq!(x, Bits::slice(&[0x0A, 0xFF, 0x0F], 20));
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.set_bytes(3, 2);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.set_bytes(0, 4);
    /// ```
    pub fn set_bytes(&mut self, start: usize, count: usize) {
        assert!(count <= self.size() && start <= self.size() - count, "Invalid range");

        unsafe {
            let pointer = self.words.as_ptr_mut();

            let end = if count > (self.size() - start) { self.size() } else { start + count };

            for i in start..end { *pointer.add(i) = 0xFF; }

            if end == self.size() && self.padding > 0 { *pointer.add(end - 1) &= self.mask; }
        }
    }

    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.shift_left(17);
    ///
    /// assert_eq!(x1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.shift_left(4);
    ///
    /// assert_eq!(x2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn shift_left(&mut self, count: usize) {
        match (self.size(), count) {
            (0, _) | (_, 0) => (),
            (_, count) if count >= self.nbits => unsafe {
                let pointer = self.words.as_ptr_mut();

                for i in 0..self.size() { *pointer.add(i) = 0 }
            },
            (n, count) => unsafe {
                let pointer = self.words.as_ptr_mut();
                let shift_overflow = count & 7;
                let shift_bytes = count >> 3;

                if shift_bytes > 0 {
                    ptr::copy(pointer, pointer.add(shift_bytes), self.size() - shift_bytes);

                    for i in 0..shift_bytes { *pointer.add(i) = 0; }

                    *pointer.add(n - 1) &= self.mask;
                }

                if shift_overflow > 0 {
                    let low = 8 - shift_overflow;

                    for i in 1..n {
                        *pointer.add(n - i) <<= shift_overflow;
                        *pointer.add(i) |= *pointer.add(n - i - 1) >> low;
                    }

                    *pointer <<= shift_overflow;
                }

                *pointer.add(n - 1) &= self.mask;
            }
        }
    }

    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = x1.shifted_left(17);
    ///
    /// assert_eq!(s1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(s1.len(), 20);
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = x2.shifted_left(4);
    ///
    /// assert_eq!(s2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(s2.len(), 24);
    /// ```
    pub fn shifted_left(&self, count: usize) -> Self {
        let mut clone = self.clone();

        clone.shift_left(count);

        clone
    }

    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.shift_right(17);
    ///
    /// assert_eq!(x1.len(), 20);
    /// assert_eq!(x1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.shift_right(4);
    ///
    /// assert_eq!(x2.len(), 24);
    /// assert_eq!(x2, Bits::new([0xB0, 0xC0, 0x00]));
    /// ```
    pub fn shift_right(&mut self, count: usize) {
        match (self.size(), count) {
            (0, _) | (_, 0) => (),
            (_, count) if count >= self.nbits => unsafe {
                let pointer = self.words.as_ptr_mut();

                for i in 0..self.size() { *pointer.add(i) = 0 }
            },
            (n, count) => unsafe {
                let pointer = self.words.as_ptr_mut();
                *pointer.add(n - 1) &= self.mask;
                let nbytes_shift = count >> 3;

                ptr::copy(pointer.add(nbytes_shift), pointer, self.size() - nbytes_shift);

                for i in (self.size() - nbytes_shift)..self.size() { *pointer.add(i) = 0; }

                let overflow = count & 7;

                if overflow > 0 {
                    let mask = (1 << overflow) - 1;
                    let low = 8 - overflow;

                    self.words.shift_right(self.size() - nbytes_shift, mask, low, overflow);
                }
            }
        }
    }

    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = x1.shifted_right(17);
    ///
    /// assert_eq!(s1.len(), 20);
    /// assert_eq!(s1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = x2.shifted_right(4);
    ///
    /// assert_eq!(s2.len(), 24);
    /// assert_eq!(s2, Bits::new([0xB0, 0xC0, 0x00]));
    /// ```
    pub fn shifted_right(&self, count: usize) -> Self {
        let mut clone = self.clone();

        clone.shift_right(count);

        clone
    }

    /// The number of bytes.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::empty();
    ///
    /// assert_eq!(x1.size(), 0);
    ///
    /// let x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x2.size(), 3);
    ///
    /// let x3 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x3.size(), 3);
    ///
    /// let x4 = Bits::slice(&[0x0A, 0x0B, 0x0C], 13);
    ///
    /// assert_eq!(x4.size(), 2);
    /// ```
    pub fn size(&self) -> usize { self.words.nbytes }

    /// Splits the bit string.
    ///
    /// When the index is greater than or equal to the length
    /// of the bit string, the second element of the returned
    /// pair will be empty. When the index is `0`, the first
    /// element will be empty.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::empty();
    /// let (l1, r1) = x1.split(11);
    ///
    /// assert_eq!(l1.len(), 0);
    /// assert_eq!(r1.len(), 0);
    ///
    /// let x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let (l2, r2) = x2.split(20);
    ///
    /// assert_eq!(l2, x2);
    /// assert_eq!(r2.len(), 0);
    ///
    /// let (l3, r3) = x2.split(0);
    ///
    /// assert_eq!(l3.len(), 0);
    /// assert_eq!(r3, x2);
    ///
    /// let (l4, r4) = x2.split(11);
    /// assert_eq!(l4, Bits::slice(&[0x0A, 0x03], 11));
    /// assert_eq!(r4, Bits::slice(&[0x81, 0x01], 9));
    /// ```
    pub fn split(&self, i: usize) -> (Bits, Bits) {
        if i >= self.nbits { return (self.clone(), Bits::empty()) }

        if i == 0 { return (Bits::empty(), self.clone()) }

        let rlen = self.nbits - i;
        let (lsize, loverflow) = divrem8!(ceil; i);
        let idiv8 = i >> 3;
        let (rsize, roverflow) = (self.size() - idiv8, rlen & 7);
        let (lmask, rmask) = (mask!(loverflow), mask!(roverflow));

        unsafe {
            let pointer = self.words.as_ptr_mut();
            let l = pointer![lsize];
            let r = pointer![rsize];

            for i in 0..lsize { *l.add(i) = *pointer.add(i); }
            for i in 0..rsize { *r.add(i) = *pointer.add(idiv8 + i); }

            let rbytes = RawBytes { bytes: NonNull::new(r).unwrap(), cap: rsize, nbytes: rsize };

            let mut rbits = Bits {
                words: rbytes,
                mask: rmask,
                nbits: self.nbits - i,
                padding: (8 - roverflow) & 7
            };

            if loverflow > 0 {
                *l.add(lsize - 1) &= lmask;

                rbits.words.shift_right(rsize, lmask, 8 - loverflow, loverflow);
            }

            let lbytes = RawBytes { bytes: NonNull::new(l).unwrap(), cap: lsize, nbytes: lsize };

            let lbits = Bits {
                words: lbytes,
                mask: lmask,
                nbits: i,
                padding: (8 - loverflow) & 7
            };

            (lbits, rbits)
        }
    }

    /// Whether a bit is one.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0F]);
    ///
    /// assert!(x.test(3));
    /// assert!(!x.test(4));
    /// assert!(!x.test(8));
    /// ```
    pub fn test(&self, i: usize) -> bool {
        unsafe {
            i < self.nbits && (*self.words.as_ptr_mut().add(i >> 3) & (1 << (i & 7))) > 0
        }
    }

    /// Flips the state of a bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(x.i(0), 0u8);
    /// assert_eq!(x.i(1), 1u8);
    ///
    /// x.toggle(0);
    /// x.toggle(1);
    ///
    /// assert_eq!(x.i(0), 1u8);
    /// assert_eq!(x.i(1), 0u8);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle(21);
    /// ```
    pub fn toggle(&mut self, i: usize) {
        assert!(i < self.nbits, "Index out of range");

        unsafe { *self.words.as_ptr_mut().add(i >> 3) ^= 1 << (i & 7); }
    }

    /// Flips the state of a range of bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// x1.toggle_bits(7, 10);
    ///
    /// assert_eq!(x1, Bits::from([0x8A, 0xF4, 0x0D]));
    ///
    /// let mut x2 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// x2.toggle_bits(8, 12);
    ///
    /// assert_eq!(x2, Bits::slice(&[0x0A, 0xF4, 0x03], 20));
    /// ```
    ///
    /// ``` should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_bits(21, 14);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_bits(7, 14);
    /// ```
    pub fn toggle_bits(&mut self, start: usize, count: usize) {
        assert!(count <= self.nbits && start <= self.nbits - count, "Invalid range");

        let end = if count > (self.nbits - start) { self.nbits } else { start + count };
        let mut start = start;
        let low_overflow = 8 - (start & 7);

        unsafe {
            let pointer = self.words.as_ptr_mut();

            if low_overflow < 8 {
                *pointer.add(start >> 3) ^= ((1 << low_overflow) - 1) << (start & 7);
                start = start + low_overflow;
            }

            let bytes = (end - start) >> 3;
            let start_byte = start >> 3;

            for i in start_byte..(start_byte + bytes) { *pointer.add(i) = !*pointer.add(i); }

            let overflow = (end - start) & 7;

            if overflow > 0 { *pointer.add(start_byte + bytes) ^= (1 << overflow) - 1; }
        }
    }

    /// Flips the state of a byte.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_byte(1);
    ///
    /// assert_eq!(x, Bits::from([0x0A, 0xF4, 0x0C]));
    ///
    /// x.toggle_byte(2);
    ///
    /// assert_eq!(x, Bits::slice(&[0x0A, 0xF4, 0x03], 20));
    ///```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_byte(3);
    /// ```
    pub fn toggle_byte(&mut self, i: usize) {
        assert!(i < self.size(), "Index out of range");

        unsafe {
            let pointer = self.words.as_ptr_mut();
            *pointer.add(i) = !*pointer.add(i);
            *pointer.add(self.size() - 1) &= self.mask;
        }
    }

    /// Flips the state of a range of bytes.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_bytes(1, 2);
    ///
    /// assert_eq!(x, Bits::slice(&[0x0A, 0xF4, 0x03], 20));
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_bytes(3, 2);
    /// ```
    ///
    /// ```should_panic
    /// # use bit_byte_bit::{Bits};
    /// let mut x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x.toggle_bytes(0, 4);
    /// ```
    pub fn toggle_bytes(&mut self, start: usize, count: usize) {
        assert!(count <= self.size() && start <= self.size() - count, "Invalid range");

        unsafe {
            let pointer = self.words.as_ptr_mut();

            let end = if count > (self.size() - start) { self.size() } else { start + count };

            for i in start..end { *pointer.add(i) = !*pointer.add(i); }

            if end == self.size() && self.padding > 0 { *pointer.add(end - 1) &= self.mask; }
        }
    }

    /// The number of trailing ones.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x = Bits::from([0xFF, 0x0B, 0x0A]);
    ///
    /// assert_eq!(x.trailing_ones(), 10);
    /// ```
    pub fn trailing_ones(&self) -> usize {
        match self.size() {
            0 => 0,
            n => unsafe {
                let pointer = self.words.as_ptr_const();
                let mut i = 1;

                while i < (n - 1) && *pointer.add(i - 1) == 0xFF { i += 1; }

                ((i - 1) << 3) + ((*pointer.add(i - 1) & self.mask).trailing_ones() as usize)
            }
        }
    }

    /// The number of trailing zeros.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x00, 0x0A, 0x0B]);
    ///
    /// assert_eq!(x1.trailing_zeros(), 9);
    ///
    /// let x2 = Bits::zeros(20);
    ///
    /// assert_eq!(x2.trailing_zeros(), 20);
    /// ```
    pub fn trailing_zeros(&self) -> usize {
        match self.size() {
            0 => 0,
            n => unsafe {
                let pointer = self.words.as_ptr_const();
                let mut i = 0;

                while i < (n - 1) && *pointer.add(i) == 0 { i += 1; }

                let zeros = if i == (n - 1) {
                    let mut trailing = (*pointer.add(i) & self.mask).trailing_zeros() as usize;

                    if *pointer.add(i) == 0 { trailing -= self.padding; }

                    trailing
                } else {
                    (*pointer.add(i)).trailing_zeros() as usize
                };

                zeros + (i << 3)
            }
        }
    }

    /// Trims leading bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.trim_end(false);
    ///
    /// assert_eq!(x1.len(), 20);
    /// assert_eq!(x1, Bits::from([0x0A, 0x0B, 0x0C]));
    ///
    /// x1.trim_end(true);
    ///
    /// assert_eq!(x1.len(), 18);
    /// assert_eq!(x1, Bits::slice(&[0x0A, 0x0B, 0x00], 18));
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2.trim_end(true);
    ///
    /// assert_eq!(x2.len(), 24);
    /// assert_eq!(x2, Bits::new([0x0A, 0x0B, 0x0C]));
    ///
    /// x2.trim_end(false);
    ///
    /// assert_eq!(x2.len(), 20);
    /// assert_eq!(x2, Bits::from([0x0A, 0x0B, 0x0C]));
    ///
    /// let mut x3 = Bits::slice(&[0x0A, 0x0B, 0x00], 18);
    ///
    /// x3.trim_end(false);
    ///
    /// assert_eq!(x3.len(), 12);
    /// assert_eq!(x3, Bits::from([0x0A, 0x0B]));
    ///
    /// let mut x4 = Bits::slice(&[0x0A, 0xFB, 0x03], 18);
    ///
    /// x4.trim_end(true);
    ///
    /// assert_eq!(x4.len(), 11);
    /// assert_eq!(x4, Bits::slice(&[0x0A, 0x0B], 11));
    /// ```
    pub fn trim_end(&mut self, bit: bool) {
        unsafe {
            let pointer = self.words.as_ptr_mut();
            *pointer.add(self.size() - 1) &= self.mask;
            let mut i = self.size();

            if self.padding > 0 {
                let last_byte = pointer.add(self.size() - 1);

                if bit && *last_byte != self.mask {
                    *last_byte <<= self.padding;
                    let clo = (*last_byte).leading_ones() as usize;
                    *last_byte <<= clo;
                    *last_byte >>= self.padding + clo;
                    self.nbits-= clo;
                    let overflow = self.nbits & 7;
                    self.padding = (8 - overflow) & 7;
                    self.mask = mask!(overflow);

                    return;
                } else if !bit && *last_byte != 0 {
                    let clz = (*last_byte).leading_zeros() as usize;

                    self.nbits = self.nbits + self.padding - clz;
                    let overflow = self.nbits & 7;
                    self.padding = (8 - overflow) & 7;
                    self.mask = mask!(overflow);

                    return;
                }

                i -= 1;
            }

            let match_byte = if bit { 0xFF } else { 0 };

            while i > 0 && *pointer.add(i - 1) == match_byte { i -= 1; }

            if i == 0 {
                for i in 0..self.size() { *pointer.add(i) = 0; }

                self.words.nbytes = 0;
                self.nbits = 0;
                self.padding = 0;
                self.mask = 0xFF;
                self.words.shrink_to(0);

                return;
            }

            self.words.shrink_to(i);

            let trailing = if bit {
                (*pointer.add(i - 1)).leading_ones() as usize
            } else {
                (*pointer.add(i - 1)).leading_zeros() as usize
            };

            self.words.nbytes = i;
            self.nbits = (i << 3) - trailing;
            let overflow = self.nbits & 7;
            self.padding = (8 - overflow) & 7;
            self.mask = mask!(overflow);
            *pointer.add(i - 1) &= self.mask;
        }
    }

    /// Trims trailing bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1.trim_start(true);
    ///
    /// assert_eq!(x1.len(), 20);
    /// assert_eq!(x1, Bits::from([0x0A, 0x0B, 0x0C]));
    ///
    /// x1.trim_start(false);
    ///
    /// assert_eq!(x1.len(), 19);
    /// assert_eq!(x1, Bits::from([0x85, 0x05, 0x06]));
    ///
    /// let mut x2 = Bits::new([0x00, 0x0A, 0x0B]);
    ///
    /// x2.trim_start(false);
    ///
    /// assert_eq!(x2.len(), 15);
    /// assert_eq!(x2, Bits::slice(&[0x85, 0x05], 15));
    ///
    /// let mut x3 = Bits::new([0xFF, 0x0B, 0x0C]);
    ///
    /// x3.trim_start(true);
    ///
    /// assert_eq!(x3.len(), 14);
    /// assert_eq!(x3, Bits::slice(&[0x02, 0x03], 14));
    /// ```
    pub fn trim_start(&mut self, bit: bool) {
        unsafe {
            let pointer = self.words.as_ptr_mut();
            let last = pointer.add(self.size() - 1);
            *last &= self.mask;
            let mut i = 0;
            let match_byte = if bit { 0xFF } else { 0 };

            while i < (self.size() - 1) && *pointer.add(i) == match_byte { i += 1; }


            if i == (self.size() - 1) {
                if (bit && *last == self.mask) || (!bit && *last == 0)
                {
                    for i in 0..self.size() { *pointer.add(i) = 0; }

                    self.words.nbytes = 0;
                    self.nbits = 0;
                    self.padding = 0;
                    self.mask = 0xFF;

                    self.words.shrink_to(0);

                    return;
                }

                let trailing = if bit {
                    (*last).trailing_ones()
                } else {
                    (*last).trailing_zeros()
                } as usize;

                *pointer = *last >> trailing;

                self.padding += trailing;
                self.words.nbytes = 1;
                self.nbits = 8 - self.padding - trailing;
                self.mask = mask!(self.nbits & 7);

                self.words.shrink_to(1);

                return;
            }

            ptr::copy(pointer.add(i), pointer, self.size() - i);

            self.words.nbytes -= i;
            self.nbits -= i << 3;

            let trailing = if bit {
                (*pointer).trailing_ones()
            } else {
                (*pointer).trailing_zeros()
            } as usize;

            if trailing > 0 {
                let mask = (1 << trailing) - 1;
                let low = 8 - trailing;

                self.words.shift_right(self.size(), mask, low, trailing);

                self.nbits -= trailing;
                let overflow = self.nbits & 7;
                self.padding = (8 - overflow) & 7;
                self.mask = mask!(overflow);
            }

            self.shrink_to_fit()
        }
    }

    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1.xor(&y1), Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2.xor(&y2);
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    pub fn xor(&self, rhs: &Bits) -> Bits { bitop!(self, ^, rhs) }

    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1.xor_mut(&y1);
    ///
    /// assert_eq!(x1, Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2.xor_mut(&y2);
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    pub fn xor_mut(&mut self, rhs: &Bits) { bitop!(assign; self, ^=, rhs) }

    fn cons_bit(&mut self, nbits: usize, fill: u8) {
        unsafe {
            let (nbytes_padding, overflow) = divrem8!(ceil; nbits);
            let nbytes = self.size() + nbytes_padding;

            self.words.expand_to(nbytes);

            let pointer = self.words.as_ptr_mut();

            if self.size() > 0 { *pointer.add(self.size() - 1) &= self.mask; }

            ptr::copy(pointer, pointer.add(nbytes_padding), self.size());

            for i in 0..nbytes_padding { ptr::write(pointer.add(i), fill); }

            *pointer.add(nbytes_padding - 1) &= mask!(overflow);

            if overflow > 0 {
                let clz = 8 - overflow;
                let mask = (1 << clz) - 1;

                self.words.shift_right_from(nbytes_padding, nbytes, mask, overflow, clz);
            }

            self.words.nbytes = nbytes;
            self.nbits += nbits;
            let new_overflow = self.nbits & 7;
            self.padding = (8 - new_overflow) & 7;
            self.mask = mask!(new_overflow);
            self.shrink_to_fit();
        }
    }

    fn push_ones(&mut self, count: usize) {
        unsafe {
            let pointer = self.words.as_ptr_mut();
            *pointer.add(self.size() - 1) &= self.mask;
            let overflow = self.nbits & 7;

            if self.padding > 0 && count <= self.padding {
                *pointer.add(self.size() - 1) |= ((1 << count) - 1) << overflow;
            } else {
                *pointer.add(self.size() - 1) |= ((1 << self.padding) - 1) << overflow;

                let (byte_len, overflow) = divrem8!(ceil; count - self.padding);

                self.words.expand_to(self.size() + byte_len);

                let pointer = self.words.as_ptr_mut().add(self.size());

                for i in 0..(byte_len - 1) { ptr::write(pointer.add(i), 0xFF); }

                ptr::write(pointer.add(byte_len - 1), mask!(overflow));

                self.words.nbytes += byte_len;
            }

            self.nbits += count;
            let overflow = self.nbits & 7;
            self.padding = (8 - overflow) & 7;
            self.mask = mask!(overflow);
        }
    }

    fn push_zeros(&mut self, count: usize) {
        unsafe {
            let pointer = self.words.as_ptr_mut();
            *pointer.add(self.size() - 1) &= self.mask;

            if self.padding == 0 || count > self.padding {
                let byte_len = 1 + ((count - self.padding - 1) >> 3);

                self.words.expand_to(self.size() + byte_len);

                let pointer = self.words.as_ptr_mut().add(self.size());

                for i in 0..byte_len { ptr::write(pointer.add(i), 0); }

                self.words.nbytes += byte_len;
            }

            self.nbits += count;
            let overflow = self.nbits & 7;
            self.padding = (8 - overflow) & 7;
            self.mask = mask!(overflow);
        }
    }

    fn shrink_to_fit(&mut self) { self.words.shrink_to(1 + ((self.nbits - 1) >> 3)); }
}

impl Clone for Bits {
    fn clone(&self) -> Self {
        match self.size() {
            0 => Bits::empty(),
            nbytes => unsafe {
                let pointer = self.words.as_ptr_mut();
                let layout = Layout::array::<u8>(nbytes).unwrap();
                let clone = alloc::alloc(layout);

                for i in 0..nbytes { ptr::write(clone.add(i), *pointer.add(i)); }

                *clone.add(nbytes - 1) &= self.mask;

                let bytes = RawBytes { bytes: NonNull::new(clone).unwrap(), cap: nbytes, nbytes };

                Bits { words: bytes, mask: self.mask, nbits: self.nbits, padding: self.padding }
            }
        }
    }
}

impl Drop for Bits {
    fn drop(&mut self) {

        if self.words.nbytes > 0 {
            unsafe {
                let pointer = self.words.as_ptr_mut();

                for i in 0..self.words.nbytes { ptr::read(pointer.add(i)); }
            }
        }
    }
}

unsafe impl Send for Bits {}

unsafe impl Sync for Bits {}

/* Section::Display */

impl Binary for Bits {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        unsafe {
            let aptr = self.words.as_ptr_const();

            if self.padding == 0 {
                for i in (0..self.size()).rev() { write!(f, "{:08b}", *aptr.add(i))?; }
            } else {
                write!(
                    f,
                    "{:01$b}",
                    *aptr.add(self.size() - 1) & self.mask,
                    8 - self.padding
                )?;

                for i in (0..(self.size() - 1)).rev() {
                    write!(f, "{:08b}", *aptr.add(i))?;
                }
            }

            Ok(())
        }
    }
}

impl Debug for Bits {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bits<")?;
        Binary::fmt(&self, f)?;
        write!(f, ": {}>", self.nbits)
    }
}

impl Display for Bits {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Binary::fmt(&self, f) }
}

/* Section::Constructors */

impl From<&[u8]> for Bits {
    fn from(data: &[u8]) -> Self { Self::from(data.to_vec()) }
}

impl<const N: usize> From<[u8; N]> for Bits {
    fn from(bytes: [u8; N]) -> Self {
        let mut nbytes = N;

        while nbytes > 0 && bytes[nbytes - 1] == 0 { nbytes -= 1; }

        if nbytes == 0 {
            Bits::empty()
        } else {
            let nbits = (nbytes << 3) - (bytes[nbytes - 1].leading_zeros() as usize);
            let mut truncated_bytes = bytes[..nbytes].to_vec();
            let pointer = truncated_bytes.as_mut_ptr();

            std::mem::forget(truncated_bytes);

            let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap: nbytes, nbytes };
            let overflow = nbits & 7;

            Bits { words: bytes, mask: mask!(overflow), nbits, padding: (8 - overflow) & 7 }
        }
    }
}

impl From<Vec<u8>> for Bits  {
    fn from(mut bytes: Vec<u8>) -> Self {
        let mut nbytes = bytes.len();

        while nbytes > 0 && bytes[nbytes - 1] == 0 { nbytes -= 1; }

        match nbytes {
            0 => Bits::empty(),
            nbytes => {
                let nbits = (nbytes << 3) - (bytes[nbytes - 1].leading_zeros() as usize);

                bytes.truncate(nbytes);

                let cap = bytes.capacity();
                let pointer = bytes.as_mut_ptr();
                let overflow = nbits & 7;

                std::mem::forget(bytes);

                let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap, nbytes };

                Bits { words: bytes, mask: mask!(overflow), nbits, padding: (8 - overflow) & 7 }
            }
        }
    }
}

impl From<&[bool]> for Bits {
    /// Creates a bit string from booleans.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let bits1 = vec![true, false, true, true, false, true, true];
    /// let x1 = Bits::from(bits1.as_slice());
    ///
    /// assert_eq!(x1.len(), 7);
    /// assert_eq!(x1, Bits::from([0x6D]));
    ///
    /// let bits2 = vec![true, false, true, false, false, false, false, false, false];
    /// let x2 = Bits::from(bits2.as_slice());
    ///
    /// assert_eq!(x2.len(), 9);
    /// assert_eq!(x2, Bits::slice(&[0x05, 0x00], 9));
    /// ```
    fn from(bits: &[bool]) -> Self {
        match bits.len() {
            0 => Bits::empty(),
            nbits => unsafe {
                let (nbytes, overflow) = divrem8!(ceil; nbits);
                let padding = (8 - overflow) & 7;
                let mask = mask!(overflow);
                let layout = Layout::array::<u8>(nbytes).unwrap();
                let pointer = alloc::alloc(layout);

                for i in 0..(nbytes - 1) {
                    let mut b = 0;
                    let j = i << 3;

                    if bits[j + 0] { b |= 1; }
                    if bits[j + 1] { b |= 2; }
                    if bits[j + 2] { b |= 4; }
                    if bits[j + 3] { b |= 8; }
                    if bits[j + 4] { b |= 16; }
                    if bits[j + 5] { b |= 32; }
                    if bits[j + 6] { b |= 64; }
                    if bits[j + 7] { b |= 128; }

                    ptr::write(pointer.add(i), b);
                }

                let mut b = 0;

                for i in 0..(8 - padding) {
                    if bits[nbits - overflow + i] { b |= 1 << i; }
                }

                ptr::write(pointer.add(nbytes - 1), b);

                let bytes = RawBytes { bytes: NonNull::new(pointer).unwrap(), cap: nbytes, nbytes };

                Bits { words: bytes, mask, nbits, padding }
            }
        }
    }
}

impl<const N: usize> From<[bool; N]> for Bits {
    /// Creates a bit string from booleans.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([true, false, true, true, false, true, true]);
    ///
    /// assert_eq!(x1.len(), 7);
    /// assert_eq!(x1, Bits::from([0x6D]));
    ///
    /// let x2 = Bits::from([true, false, true, false, false, false, false, false, false]);
    ///
    /// assert_eq!(x2.len(), 9);
    /// assert_eq!(x2, Bits::slice(&[0x05, 0x00], 9));
    /// ```
    fn from(bits: [bool; N]) -> Self { Bits::from(bits.as_slice()) }
}

impl From<Vec<bool>> for Bits {
    /// Creates a bit string from booleans.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let bits1 = vec![true, false, true, true, false, true, true];
    /// let x1 = Bits::from(bits1);
    ///
    /// assert_eq!(x1.len(), 7);
    /// assert_eq!(x1, Bits::from([0x6D]));
    ///
    /// let bits2 = vec![true, false, true, false, false, false, false, false, false];
    /// let x2 = Bits::from(bits2);
    ///
    /// assert_eq!(x2.len(), 9);
    /// assert_eq!(x2, Bits::slice(&[0x05, 0x00], 9));
    /// ```
    fn from(bits: Vec<bool>) -> Self { Bits::from(bits.as_slice()) }
}

impl FromIterator<u8> for Bits {
    fn from_iter<I: IntoIterator<Item=u8>>(iter: I) -> Self {
        Bits::from(iter.into_iter().collect::<Vec<u8>>())
    }
}

impl FromIterator<bool> for Bits {
    fn from_iter<I: IntoIterator<Item=bool>>(iter: I) -> Self {
        Bits::from(iter.into_iter().collect::<Vec<bool>>())
    }
}

/* Section::Order */

impl Eq for Bits {}

impl Ord for Bits {
    /// Compares a bit string with another
    ///
    /// # Examples
    /// ```
    /// # use std::cmp::Ordering;
    /// # use bit_byte_bit::Bits;
    ///
    /// let x = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let y = Bits::from([0x09, 0x0B, 0x0C]);
    /// let z = Bits::from([0x0A, 0x09, 0x0D]);
    ///
    /// assert_eq!(x.cmp(&y), Ordering::Greater);
    /// assert_eq!(x.cmp(&z), Ordering::Less);
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        match other.leading_zeros().cmp(&self.leading_zeros()) {
            Ordering::Equal => unsafe {
                let aptr= self.words.as_ptr_const();
                let bptr = other.words.as_ptr_const();

                for i in (0..self.size()).rev() {
                    match (*aptr.add(i)).cmp(&*bptr.add(i)) {
                        Ordering::Equal => (),
                        ord => return ord,
                    }
                }

                Ordering::Equal
            },
            ord => ord,
        }
    }
}

impl PartialEq for Bits {
    /// Whether two bit strings are equal.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x = Bits::from([0x20, 0x30, 0x40]);
    ///
    /// assert!(Bits::eq(&x, &x));
    ///
    /// let y = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert!(Bits::ne(&x, &y));
    ///
    /// let z1 = Bits::from([0x20, 0x30, 0x40, 0x00]);
    ///
    /// assert!(Bits::eq(&x, &z1));
    ///
    /// let z2 = Bits::new([0x20, 0x30, 0x40, 0x00]);
    ///
    /// assert!(Bits::ne(&x, &z2));
    /// ```
    fn eq(&self, other: &Self) -> bool {
        match (self.nbits, other.nbits) {
            (0, 0) => true,
            (a, b) if a != b => false,
            _ => unsafe {
                let aptr = self.words.as_ptr_const();
                let bptr = other.words.as_ptr_const();

                for i in 0..(self.size() - 1) {
                    if *aptr.add(i) != *bptr.add(i) { return false; }
                }

                let last_a = *aptr.add(self.size() - 1) & self.mask;
                let last_b = *bptr.add(other.size() - 1) & other.mask;

                last_a == last_b
            }
        }
    }
}

impl PartialOrd for Bits {
    /// Compares a bit string with another
    ///
    /// # Examples
    /// ```
    /// # use std::cmp::Ordering;
    /// # use bit_byte_bit::Bits;
    ///
    /// let x = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let y = Bits::from([0x09, 0x0B, 0x0C]);
    /// let z = Bits::from([0x0A, 0x09, 0x0D]);
    ///
    /// assert_eq!(x.partial_cmp(&y), Some(Ordering::Greater));
    /// assert_eq!(x.partial_cmp(&z), Some(Ordering::Less));
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

/* Section::Iteration */

impl IntoIterator for Bits {
    type Item = u8;
    type IntoIter = IntoBits;

    fn into_iter(self) -> Self::IntoIter { IntoBits::new(self, 0) }
}


struct Bytes {
    start: *const u8,
    end: *const u8
}

impl Bytes {
    unsafe fn new(slice: &[u8]) -> Self {
        Bytes {
            start: slice.as_ptr(),
            end: if slice.len() == 0 {
                slice.as_ptr()
            } else {
                unsafe{ slice.as_ptr().add(slice.len()) }
            }
        }
    }
}

impl DoubleEndedIterator for Bytes {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                self.end = self.end.offset(-1);
                Some(ptr::read(self.end))
            }
        }
    }
}

impl ExactSizeIterator for Bytes {
    fn len(&self) -> usize { self.end as usize - self.start as usize }
}

impl FusedIterator for Bytes { }

impl Iterator for Bytes {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        match self.start == self.end {
            true => None,
            false => unsafe {
                let old_ptr = self.start;
                self.start = self.start.add(1);

                Some(ptr::read(old_ptr))
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end as usize - self.start as usize;

        (len, Some(len))
    }
}


pub struct Iter<'a> {
    bits: &'a Bits,
    index: usize,
    exhausted: bool
}

impl<'a> Iter<'a> {
    fn new(bits: &'a Bits, index: usize) -> Self {
        Iter { bits, index, exhausted: bits.nbits == index }
    }

    /// Moves the iterator ahead until the predicate returns true.
    ///
    /// This method behaves like [Iterator::skip_while], but doesn't
    /// rely on repeated calls to [Iterator::next].
    pub fn skip_bits_while<P: FnMut(u8) -> bool>(&mut self, mut f: P) -> usize {
        if self.exhausted { return 0; }

        match (f(0), f(1)) {
            (true, true) => {
                let rem = self.bits.len() - self.index;

                self.index = self.bits.len();
                self.exhausted = true;

                rem
            },
            (false, false) => 0,
            (z, _) => {
                let ct =
                    if z { self.bits.trailing_zeros() } else { self.bits.trailing_ones() };

                if ct > self.index {
                    let skipped = ct - self.index;

                    self.index = ct;
                    self.exhausted = self.index == self.bits.len();

                    skipped
                } else {
                    0
                }
            }
        }
    }

    /// Moves the iterator ahead.
    ///
    /// This method behaves like [Iterator::skip], but doesn't rely on
    /// repeated calls to [Iterator::next].
    pub fn skip_bits(&mut self, n: usize) {
        if self.exhausted {
            return;
        } else if (self.index + n) >= self.bits.len() {
            self.index = self.bits.len();
            self.exhausted = true;
        } else {
            self.index += n;
        }
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index == 0 {
            None
        } else {
            self.index -= 1;
            self.exhausted = false;

            Some(self.bits.i(self.index))
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.index < n {
            None
        } else {
            self.index -= n;
            self.exhausted = false;

            Some(self.bits.i(self.index))
        }
    }
}

impl<'a> ExactSizeIterator for Iter<'a> {
    fn len(&self) -> usize { self.bits.len() - self.index }
}

impl<'a> FusedIterator for Iter<'a> { }

impl<'a> Iterator for Iter<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        match self.exhausted {
            true => None,
            false => {
                let bit = self.bits.i(self.index);
                self.index += 1;
                self.exhausted = self.bits.len() == self.index;

                Some(bit)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.bits.len() - self.index;

        (rem, Some(rem))
    }

    fn count(mut self) -> usize {
        let rem = self.bits.len() - self.index;

        self.index = self.bits.len();
        self.exhausted = true;

        rem
    }

    fn last(mut self) -> Option<u8> {
        if self.exhausted {
            None
        } else {
            let bit = self.bits.i(self.bits.len() - 1);

            self.index = self.bits.len();
            self.exhausted = true;

            Some(bit)
        }
    }

    fn nth(&mut self, n: usize) -> Option<u8> {
        if self.exhausted {
            None
        } else if self.index + n >= self.bits.len() {
            self.index = self.bits.len();
            self.exhausted = true;

            None
        } else {
            let bit = self.bits.i(self.index + n);
            self.index += n + 1;
            self.exhausted = self.index == self.bits.len();

            Some(bit)
        }
    }
}


pub struct IntoBits {
    bits: Bits,
    index: usize,
    exhausted: bool
}

impl IntoBits {
    fn new(bits: Bits, index: usize) -> Self {
        let exhausted = bits.nbits == index;

        IntoBits { bits, index, exhausted }
    }

    /// Moves the iterator ahead until the predicate returns true.
    ///
    /// This method behaves like [Iterator::skip_while], but doesn't
    /// rely on repeated calls to [Iterator::next], instead on the
    /// return values to `f(0)` and `f(1)`.
    pub fn skip_bits_while<P: FnMut(u8) -> bool>(&mut self, mut f: P) -> usize {
        if self.exhausted { return 0; }

        match (f(0), f(1)) {
            (true, true) => {
                let rem = self.bits.len() - self.index;

                self.index = self.bits.len();
                self.exhausted = true;

                rem
            },
            (false, false) => 0,
            (z, _) => {
                let ct =
                    if z { self.bits.trailing_zeros() } else { self.bits.trailing_ones() };

                if ct > self.index {
                    let skipped = ct - self.index;

                    self.index = ct;
                    self.exhausted = self.index == self.bits.len();

                    skipped
                } else {
                    0
                }
            }
        }
    }

    /// Moves the iterator ahead.
    ///
    /// This method behaves like [Iterator::skip], but doesn't rely on
    /// repeated calls to [Iterator::next].
    pub fn skip_bits(&mut self, n: usize) {
        if self.exhausted {
            return;
        } else if (self.index + n) >= self.bits.len() {
            self.index = self.bits.len();
            self.exhausted = true;
        } else {
            self.index += n;
        }
    }
}

impl DoubleEndedIterator for IntoBits {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index == 0 {
            None
        } else {
            self.index -= 1;
            self.exhausted = false;

            Some(self.bits.i(self.index))
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.index < n {
            None
        } else {
            self.index -= n;
            self.exhausted = false;

            Some(self.bits.i(self.index))
        }
    }
}

impl ExactSizeIterator for IntoBits {
    fn len(&self) -> usize { self.bits.len() - self.index }
}

impl FusedIterator for IntoBits { }

impl Iterator for IntoBits {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        match self.exhausted {
            true => None,
            false => {
                let bit = self.bits.i(self.index);
                self.index += 1;
                self.exhausted = self.bits.len() == self.index;

                Some(bit)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.bits.len() - self.index;

        (rem, Some(rem))
    }

    fn count(mut self) -> usize {
        let rem = self.bits.len() - self.index;

        self.index = self.bits.len();
        self.exhausted = true;

        rem
    }

    fn last(mut self) -> Option<u8> {
        if self.exhausted {
            None
        } else {
            let bit = self.bits.i(self.bits.len() - 1);

            self.index = self.bits.len();
            self.exhausted = true;

            Some(bit)
        }
    }

    fn nth(&mut self, n: usize) -> Option<u8> {
        if self.exhausted {
            None
        } else if self.index + n >= self.bits.len() {
            self.index = self.bits.len();
            self.exhausted = true;

            None
        } else {
            let bit = self.bits.i(self.index + n);
            self.index += n + 1;
            self.exhausted = self.index == self.bits.len();

            Some(bit)
        }
    }
}


pub struct IntoBytes {
    _bytes: RawBytes,
    iter: Bytes
}

impl DoubleEndedIterator for IntoBytes {
    fn next_back(&mut self) -> Option<Self::Item> { self.iter.next_back() }
}

impl Drop for IntoBytes {
    fn drop(&mut self) { for _ in &mut *self { } }
}

impl ExactSizeIterator for IntoBytes {
    fn len(&self) -> usize { self.iter.len() }
}

impl FusedIterator for IntoBytes { }

impl Iterator for IntoBytes {
    type Item = u8;

    fn next(&mut self) -> Option<u8> { self.iter.next() }

    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}


/* Section::Operators */

impl BitAnd for Bits {
    type Output = Self;

    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 & y1, Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 & y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitand(self, rhs: Self) -> Self::Output { self.and(&rhs) }
}

impl BitAnd<&Bits> for Bits {
    type Output = Bits;

    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 & &y1, Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 & &y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitand(self, rhs: &Bits) -> Self::Output { self.and(rhs) }
}

impl BitAnd<&Bits> for &Bits {
    type Output = Bits;

    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 & &y1, Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 & &y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitand(self, rhs: &Bits) -> Self::Output { self.and(rhs) }
}

impl BitAndAssign for Bits {
    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1 &= y1;
    ///
    /// assert_eq!(x1, Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2 &= y2;
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn bitand_assign(&mut self, rhs: Self) { self.and_mut(&rhs); }
}

impl BitAndAssign<&Bits> for Bits {
    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1 &= &y1;
    ///
    /// assert_eq!(x1, Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2 &= &y2;
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn bitand_assign(&mut self, rhs: &Bits) { self.and_mut(rhs); }
}

impl BitOr for Bits {
    type Output = Self;

    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 | y1, Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 | y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitor(self, rhs: Self) -> Self::Output { self.or(&rhs) }
}

impl BitOr<&Bits> for Bits {
    type Output = Bits;

    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 | &y1, Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 | &y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitor(self, rhs: &Bits) -> Self::Output { self.or(rhs) }
}

impl BitOr<&Bits> for &Bits {
    type Output = Bits;

    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 | &y1, Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 | &y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitor(self, rhs: &Bits) -> Self::Output { self.or(rhs) }
}

impl BitOrAssign for Bits {
    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1 |= y1;
    ///
    /// assert_eq!(x1, Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2 |= y2;
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn bitor_assign(&mut self, rhs: Self) { self.or_mut(&rhs); }
}

impl BitOrAssign<&Bits> for Bits {
    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1 |= &y1;
    ///
    /// assert_eq!(x1, Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2 |= &y2;
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn bitor_assign(&mut self, rhs: &Bits) { self.or_mut(rhs); }
}

impl BitXor for Bits {
    type Output = Self;

    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 ^ y1, Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 ^ y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitxor(self, rhs: Self) -> Self::Output { self.xor(&rhs) }
}

impl BitXor<&Bits> for Bits {
    type Output = Bits;

    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 ^ &y1, Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 ^ &y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitxor(self, rhs: &Bits) -> Self::Output { self.xor(&rhs) }
}

impl BitXor<&Bits> for &Bits {
    type Output = Bits;

    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x1 ^ &y1, Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = x2 ^ &y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitxor(self, rhs: &Bits) -> Self::Output { self.xor(&rhs) }
}

impl BitXorAssign for Bits {
    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1 ^= y1;
    ///
    /// assert_eq!(x1, Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2 ^= y2;
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn bitxor_assign(&mut self, rhs: Self) { self.xor_mut(&rhs); }
}

impl BitXorAssign<&Bits> for Bits {
    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// x1 ^= &y1;
    ///
    /// assert_eq!(x1, Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let mut x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// x2 ^= &y2;
    ///
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn bitxor_assign(&mut self, rhs: &Bits) { self.xor_mut(&rhs); }
}

impl Div<usize> for Bits {
    type Output = (Bits, Bits);

    fn div(self, index: usize) -> Self::Output { self.split(index) }
}

impl Not for Bits {
    type Output = Self;

    /// Flips every bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(!x, Bits::slice(&[0xF5, 0xF4, 0x03], 20));
    /// ```
    fn not(self) -> Self::Output { self.complement() }
}

impl Not for &Bits {
    type Output = Bits;

    /// Flips every bit.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// assert_eq!(!&x, Bits::slice(&[0xF5, 0xF4, 0x03], 20));
    /// ```
    fn not(self) -> Self::Output { self.complement() }
}

impl Shl<usize> for Bits {
    type Output = Self;

    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = x1 << 17;
    ///
    /// assert_eq!(s1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(s1.len(), 20);
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = x2 << 4;
    ///
    /// assert_eq!(s2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(s2.len(), 24);
    /// ```
    fn shl(self, count: usize) -> Self::Output { self.shifted_left(count) }
}

impl Shl<usize> for &Bits {
    type Output = Bits;

    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = &x1 << 17;
    ///
    /// assert_eq!(s1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(s1.len(), x1.len());
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = &x2 << 4;
    ///
    /// assert_eq!(s2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(s2.len(), x2.len());
    /// ```
    fn shl(self, count: usize) -> Self::Output { self.shifted_left(count) }
}

impl Shl<&usize> for Bits {
    type Output = Self;

    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = x1 << &17;
    ///
    /// assert_eq!(s1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(s1.len(), 20);
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = x2 << &4;
    ///
    /// assert_eq!(s2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(s2.len(), 24);
    /// ```
    fn shl(self, count: &usize) -> Self::Output { self.shifted_left(*count) }
}

impl Shl<&usize> for &Bits {
    type Output = Bits;

    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = &x1 << &17;
    ///
    /// assert_eq!(s1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(s1.len(), x1.len());
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = &x2 << &4;
    ///
    /// assert_eq!(s2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(s2.len(), x2.len());
    /// ```
    fn shl(self, count: &usize) -> Self::Output { self.shifted_left(*count) }
}

impl ShlAssign<usize> for Bits {
    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1 <<= 17;
    ///
    /// assert_eq!(x1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2 <<= 4;
    ///
    /// assert_eq!(x2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn shl_assign(&mut self, count: usize) { self.shift_left(count); }
}

impl ShlAssign<&usize> for Bits {
    /// Shifts out upper bits, shifting in zeros on the lower end.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1 <<= &17;
    ///
    /// assert_eq!(x1, Bits::slice(&[0x00, 0x00, 0x04], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2 <<= &4;
    ///
    /// assert_eq!(x2, Bits::new([0xA0, 0xB0, 0xC0]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn shl_assign(&mut self, count: &usize) { self.shift_left(*count); }
}

impl Shr<usize> for Bits {
    type Output = Self;

    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = x1 >> 17;
    ///
    /// assert_eq!(s1.len(), 20);
    /// assert_eq!(s1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = x2 >> 4;
    ///
    /// assert_eq!(s2.len(), 24);
    /// assert_eq!(s2, Bits::new([0xB0, 0xC0, 0x00]));
    /// ```
    fn shr(self, count: usize) -> Self::Output { self.shifted_right(count) }
}

impl Shr<usize> for &Bits {
    type Output = Bits;

    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = &x1 >> 17;
    ///
    /// assert_eq!(s1.len(), x1.len());
    /// assert_eq!(s1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = &x2 >> 4;
    ///
    /// assert_eq!(s2.len(), x2.len());
    /// assert_eq!(s2, Bits::new([0xB0, 0xC0, 0x00]));
    /// ```
    fn shr(self, count: usize) -> Self::Output { self.shifted_right(count) }
}

impl Shr<&usize> for Bits {
    type Output = Self;

    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = x1 >> &17;
    ///
    /// assert_eq!(s1.len(), 20);
    /// assert_eq!(s1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = x2 >> &4;
    ///
    /// assert_eq!(s2.len(), 24);
    /// assert_eq!(s2, Bits::new([0xB0, 0xC0, 0x00]));
    /// ```
    fn shr(self, count: &usize) -> Self::Output { self.shifted_right(*count) }
}

impl Shr<&usize> for &Bits {
    type Output = Bits;

    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    /// let s1 = &x1 >> &17;
    ///
    /// assert_eq!(s1.len(), x1.len());
    /// assert_eq!(s1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    ///
    /// let x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    /// let s2 = &x2 >> &4;
    ///
    /// assert_eq!(s2.len(), 24);
    /// assert_eq!(s2, Bits::new([0xB0, 0xC0, 0x00]));
    /// ```
    fn shr(self, count: &usize) -> Self::Output { self.shifted_right(*count) }
}

impl ShrAssign<usize> for Bits {
    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1 >>= 17;
    ///
    /// assert_eq!(x1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    /// assert_eq!(x1.len(), 20);
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2 >>= 4;
    ///
    /// assert_eq!(x2, Bits::new([0xB0, 0xC0, 0x00]));
    /// assert_eq!(x2.len(), 24);
    /// ```
    fn shr_assign(&mut self, count: usize) { self.shift_right(count); }
}

impl ShrAssign<&usize> for Bits {
    /// Shifts out lower bits, shifting zeros into the upper bits.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let mut x1 = Bits::from([0x0A, 0x0B, 0x0C]);
    ///
    /// x1 >>= &17;
    ///
    /// assert_eq!(x1.len(), 20);
    /// assert_eq!(x1, Bits::slice(&[0x06, 0x00, 0x00], 20));
    ///
    /// let mut x2 = Bits::new([0x0A, 0x0B, 0x0C]);
    ///
    /// x2 >>= &4;
    ///
    /// assert_eq!(x2.len(), 24);
    /// assert_eq!(x2, Bits::new([0xB0, 0xC0, 0x00]));
    /// ```
    fn shr_assign(&mut self, count: &usize) { self.shift_right(*count); }
}


/* Section::Macro */


/// Macro implementing a subset of the [Bits] constructors
///
/// Example
/// ```
/// # use bit_byte_bit::{Bits, bits};
/// let x1 = bits![];
///
/// assert_eq!(x1, Bits::empty());
///
/// let x2 = bits![0x0A, 0x0B, 0x0C];
///
/// assert_eq!(x2, Bits::new([0x0A, 0x0B, 0x0C]));
///
/// let x3 = bits![0x0A, 0x0B, 0x0C; => 16];
///
/// assert_eq!(x3, Bits::aligned(16, [0x0A, 0x0B, 0x0C]));
///
/// let x4 = bits![0x0A, 0x0B, 0x0C; %];
///
/// assert_eq!(x4, Bits::packed([0x0A, 0x0B, 0x0C]));
///
/// let x5 = bits![1; 17];
///
/// assert_eq!(x5, Bits::ones(17));
///
/// let x6 = bits![0; 17];
///
/// assert_eq!(x6, Bits::zeros(17));
/// assert_eq!(x6.len(), 17);
///
/// let x7 = bits![8; 0; 17];
///
/// assert_eq!(x7, Bits::new(vec![0; 17]));
/// assert_eq!(x7.len(), 136);
/// ```
#[macro_export]
macro_rules! bits {
    () => { Bits::empty() };
    (0; $n:expr) => { Bits::zeros($n) };
    (1; $n:expr) => { Bits::ones($n) };
    (8; $byte:expr; $n:expr) => { Bits::new(vec![$byte; $n]) };
    ($($byte:expr),+ $(,)?) => {{ Bits::new(vec![$($byte),+]) }};
    ($($byte:expr),+; => $n:expr) => { Bits::aligned($n, vec![$($byte),+]) };
    ($($byte:expr),+; %) => { Bits::packed(vec![$($byte),+]) };
}