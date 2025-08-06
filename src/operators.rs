use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr, ShrAssign};
use crate::Bits;

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

impl<'a> BitAnd<Bits> for &'a Bits {
    type Output = Bits;

    /// Bitwise and of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(&x1 & y1, Bits::new([0x20, 0x30, 0x40]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = &x2 & y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitand(self, rhs: Bits) -> Self::Output { self.and(&rhs) }
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

impl<'a> BitOr<Bits> for &'a Bits {
    type Output = Bits;

    /// Bitwise or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(&x1 | y1, Bits::from([0xA0, 0xB0, 0xC0]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = &x2 | y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitor(self, rhs: Bits) -> Self::Output { self.or(&rhs) }
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
    fn bitxor(self, rhs: &Bits) -> Self::Output { self.xor(rhs) }
}

impl<'a> BitXor<Bits> for &'a Bits {
    type Output = Bits;

    /// Bitwise exclusive or of two bit strings.
    ///
    /// # Examples
    /// ```
    /// # use bit_byte_bit::{Bits};
    /// let x1 = Bits::from([0x20, 0x30, 0x40]);
    /// let y1 = Bits::from([0xA0, 0xB0, 0xC0]);
    ///
    /// assert_eq!(&x1 ^ y1, Bits::from([0x80, 0x80, 0x80]));
    ///
    /// let x2 = Bits::from([0x20, 0x30, 0x40]);
    /// let y2 = Bits::from([0x0A, 0xB0, 0xC0]);
    ///
    /// assert_eq!(x2.len(), 23);
    /// assert_eq!(y2.len(), 24);
    ///
    /// let z = &x2 ^ y2;
    ///
    /// assert_eq!(z.len(), 24);
    /// ```
    fn bitxor(self, rhs: Bits) -> Self::Output { self.xor(&rhs) }
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
    fn bitxor(self, rhs: &Bits) -> Self::Output { self.xor(rhs) }
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