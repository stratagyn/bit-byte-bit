use std::iter::FusedIterator;
use std::ptr;
use crate::{Bits, RawBytes};


macro_rules! skip_bits {
    ($n:expr, $iter:expr) => {{
        if $iter.exhausted {
            return;
        } else if ($iter.index + $n) >= $iter.bits.len() {
            $iter.index = $iter.bits.len();
            $iter.exhausted = true;
        } else {
            $iter.index += $n;
        }
    }};
    ($iter:expr => $f:expr) => {{
        if $iter.exhausted { return 0; }

        match ($f(0), $f(1)) {
            (true, true) => {
                let rem = $iter.bits.len() - $iter.index;

                $iter.index = $iter.bits.len();
                $iter.exhausted = true;

                rem
            },
            (false, false) => 0,
            (z, _) => {
                let ct =
                    if z { $iter.bits.trailing_zeros() } else { $iter.bits.trailing_ones() };

                if ct > $iter.index {
                    let skipped = ct - $iter.index;

                    $iter.index = ct;
                    $iter.exhausted = $iter.index == $iter.bits.len();

                    skipped
                } else {
                    0
                }
            }
        }
    }};
}


impl IntoIterator for Bits {
    type Item = u8;
    type IntoIter = IntoBits;

    fn into_iter(self) -> Self::IntoIter { IntoBits::new(self, 0) }
}


pub(crate) struct Bytes {
    start: *const u8,
    end: *const u8
}

impl Bytes {
    pub unsafe fn new(slice: &[u8]) -> Self {
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
    pub(crate)fn new(bits: &'a Bits, index: usize) -> Self {
        Iter { bits, index, exhausted: bits.nbits == index }
    }

    /// Moves the iterator ahead until the predicate returns true.
    ///
    /// This method behaves like [Iterator::skip_while], but doesn't
    /// rely on repeated calls to [Iterator::next].
    pub fn skip_bits_while<P: FnMut(u8) -> bool>(&mut self, mut f: P) -> usize {
        skip_bits!(self => f)
    }

    /// Moves the iterator ahead.
    ///
    /// This method behaves like [Iterator::skip], but doesn't rely on
    /// repeated calls to [Iterator::next].
    pub fn skip_bits(&mut self, n: usize) { skip_bits!(n, self); }
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
    pub(crate) fn new(bits: Bits, index: usize) -> Self {
        let exhausted = bits.nbits == index;

        IntoBits { bits, index, exhausted }
    }

    /// Moves the iterator ahead until the predicate returns true.
    ///
    /// This method behaves like [Iterator::skip_while], but doesn't
    /// rely on repeated calls to [Iterator::next], instead on the
    /// return values to `f(0)` and `f(1)`.
    pub fn skip_bits_while<P: FnMut(u8) -> bool>(&mut self, mut f: P) -> usize {
        skip_bits!(self => f)
    }

    /// Moves the iterator ahead.
    ///
    /// This method behaves like [Iterator::skip], but doesn't rely on
    /// repeated calls to [Iterator::next].
    pub fn skip_bits(&mut self, n: usize) { skip_bits!(n, self); }
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

impl IntoBytes {
    pub(crate) fn new(bytes: Bytes, raw_bytes: RawBytes) -> Self {
        IntoBytes { _bytes: raw_bytes, iter: bytes }
    }
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