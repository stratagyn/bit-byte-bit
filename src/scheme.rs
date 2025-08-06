use std::fmt::{Debug};
use crate::{Bits};


/// Defines a region of bits.
///
/// Each field has a unit, size, and a flag indicating if the field represents a signed integer.
/// The unit is the minimum number of bits extracted by the field. The size is the total number
/// of units extracted by the field.
///
/// The flag comes into play when a field extracts more bits than are available. If at least one
/// bit is still available and the flag is true, the bit string is sign extended to the length of
/// the field.
/// 
/// ## Constants
///
/// Common field types.
///
/// |   Constant    | Unit |   Size  | Signed |
/// |:-------------:|:----:|:-------:|:------:|
/// | `BIT`         |  1   |    1    |
/// | `BYTES`       |  8   | UNBOUND |
/// | `SIGNED`      |  1   | UNBOUND |   X
/// | `SIGNED_2`    |  1   |    2    |   X
/// | `SIGNED_4`    |  1   |    4    |   X
/// | `SIGNED_8`    |  1   |    8    |   X
/// | `SIGNED_16`   |  1   |    16   |   X
/// | `SIGNED_32`   |  1   |    32   |   X
/// | `SIGNED_64`   |  1   |    64   |   X
/// | `UNSIGNED`    |  1   | UNBOUND |
/// | `UNSIGNED_2`  |  1   |    2    |
/// | `UNSIGNED_4`  |  1   |    4    |
/// | `UNSIGNED_8`  |  1   |    8    |
/// | `UNSIGNED_16` |  1   |    16   |
/// | `UNSIGNED_32` |  1   |    32   |
/// | `UNSIGNED_64` |  1   |    64   |
///
#[derive(Debug, Copy, Clone)]
pub struct Field {
    size: isize,
    unit: usize,
    signed: bool
}

impl Field {
    pub const BIT: Field = Field { size: 1, unit: 1, signed: false };
    pub const BYTES: Field = Field { size: -1, unit: 8, signed: false };
    pub const SIGNED: Field = Field { size: -1, unit: 1, signed: true };
    pub const SIGNED_2: Field = Field { size: 2, unit: 1, signed: true };
    pub const SIGNED_4: Field = Field { size: 4, unit: 1, signed: true };
    pub const SIGNED_8: Field = Field { size: 8, unit: 1, signed: true };
    pub const SIGNED_16: Field = Field { size: 16, unit: 1, signed: true };
    pub const SIGNED_32: Field = Field { size: 32, unit: 1, signed: true };
    pub const SIGNED_64: Field = Field { size: 64, unit: 1, signed: true };
    pub const UNSIGNED: Field = Field { size: -1, unit: 1, signed: false };
    pub const UNSIGNED_2: Field = Field { size: 2, unit: 1, signed: false };
    pub const UNSIGNED_4: Field = Field { size: 4, unit: 1, signed: false };
    pub const UNSIGNED_8: Field = Field { size: 8, unit: 1, signed: false };
    pub const UNSIGNED_16: Field = Field { size: 16, unit: 1, signed: false };
    pub const UNSIGNED_32: Field = Field { size: 32, unit: 1, signed: false };
    pub const UNSIGNED_64: Field = Field { size: 64, unit: 1, signed: false };

    /// Bit field aligned to a given unit
    ///
    /// When `m` and `n` are negative `Bits::aligned(m, signed) == Bits::aligned(n, signed)`,
    /// even if `m != n`.
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// let field = Field::aligned(7, 48, false);
    ///
    /// assert_eq!(field.unit(), 7);
    /// assert_eq!(field.size(), 48);
    /// assert_eq!(field.len(), 48 * 7);
    ///
    /// let mfield = Field::aligned(7, -1, true);
    /// let nfield = Field::aligned(7, isize::MIN, true);
    ///
    /// assert_eq!(mfield, nfield);
    /// assert_eq!(mfield.size(), -1);
    /// assert_eq!(nfield.size(), -1);
    /// assert!(mfield.is_signed());
    /// ```
    pub fn aligned(unit: usize, size: isize, signed: bool) -> Self { Field { size, unit, signed } }

    /// Byte-aligned bit field
    ///
    /// When `m` and `n` are negative `Bits::bytes(m, signed) == Bits::bytes(n, signed)`,
    /// even if `m != n`.
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// let field = Field::bytes(48, false);
    ///
    /// assert_eq!(field.unit(), 8);
    /// assert_eq!(field.size(), 48);
    /// assert_eq!(field.len(), 48 * 8);
    ///
    /// let mfield = Field::bytes(-1, true);
    /// let nfield = Field::bytes(isize::MIN, true);
    ///
    /// assert_eq!(mfield, nfield);
    /// assert_eq!(mfield.size(), -1);
    /// assert_eq!(nfield.size(), -1);
    /// assert!(mfield.is_signed());
    /// ```
    pub fn bytes(size: isize, signed: bool) -> Self { Field { size, unit: 8, signed } }

    /// Bit field
    ///
    /// When `m` and `n` are negative `Bits::bits(m, signed) == Bits::bits(n, signed)`,
    /// even if `m != n`.
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// let field = Field::signed(96);
    ///
    /// assert_eq!(field.unit(), 1);
    /// assert_eq!(field.size(), 96);
    /// assert_eq!(field.len(), 96);
    /// assert!(field.is_signed());
    ///
    /// let mfield = Field::signed(-1);
    /// let nfield = Field::signed(isize::MIN);
    ///
    /// assert_eq!(mfield, nfield);
    /// assert_eq!(mfield.size(), -1);
    /// assert_eq!(nfield.size(), -1);
    /// assert!(mfield.is_signed());
    ///
    /// ```
    pub fn signed(size: isize) -> Self { Field { size, unit: 1, signed: true } }

    /// Bit field
    ///
    /// When `m` and `n` are negative `Bits::bits(m, signed) == Bits::bits(n, signed)`,
    /// even if `m != n`.
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// let field = Field::unsigned(96);
    ///
    /// assert_eq!(field.unit(), 1);
    /// assert_eq!(field.size(), 96);
    /// assert_eq!(field.len(), 96);
    /// assert!(!field.is_signed());
    ///
    /// let mfield = Field::unsigned(-1);
    /// let nfield = Field::unsigned(isize::MIN);
    ///
    /// assert_eq!(mfield, nfield);
    /// assert_eq!(mfield.size(), -1);
    /// assert_eq!(nfield.size(), -1);
    /// assert!(!mfield.is_signed());
    ///
    /// ```
    pub fn unsigned(size: isize) -> Self { Field { size, unit: 1, signed: false } }

    /// Whether this field represents a signed integer.
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// assert!(Field::aligned(7, 48, true).is_signed());
    /// assert!(!Field::aligned(7, 48, false).is_signed());
    /// assert!(Field::bytes(-1, true).is_signed());
    /// assert!(!Field::bytes(-1, false).is_signed());
    /// assert!(Field::signed(96).is_signed());
    /// assert!(!Field::unsigned(96).is_signed());
    /// ```
    pub fn is_signed(&self) -> bool { self.signed }

    /// Number of bits extracted by the field
    ///
    /// `-1` means that the field extracts the maximum number of bits that can be divided by the
    /// `unit` of the field. Extraction never exceeds the remaining the number of bits.
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// assert_eq!(Field::aligned(0, -1, true).len(), 0);
    /// assert_eq!(Field::aligned(7, 0, false).len(), 0);
    /// assert_eq!(Field::aligned(7, 48, true).len(), 48 * 7);
    /// assert_eq!(Field::aligned(7, -1, false).len(), -1);
    /// assert_eq!(Field::aligned(7, isize::MIN, true).len(), -1);
    /// assert_eq!(Field::bytes(48, true).len(), 48 * 8);
    /// assert_eq!(Field::bytes(-1, false).len(), -1);
    /// assert_eq!(Field::bytes(isize::MIN, true).len(), -1);
    /// assert_eq!(Field::signed(48).len(), 48);
    /// assert_eq!(Field::signed(-1).len(), -1);
    /// assert_eq!(Field::signed(isize::MIN).len(), -1);
    /// assert_eq!(Field::unsigned(48).len(), 48);
    /// assert_eq!(Field::unsigned(-1).len(), -1);
    /// assert_eq!(Field::unsigned(isize::MIN).len(), -1);
    /// ```
    pub fn len(&self) -> isize {
        match (self.size, self.unit) {
            (0, _) | (_, 0) => 0,
            (size, _) if size < 0 => -1,
            (size, unit) => size * (unit as isize)
        }
    }

    /// Number of units in the field
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// assert_eq!(Field::aligned(7, 48, true).size(), 48);
    /// assert_eq!(Field::aligned(7, -1, false).size(), -1);
    /// assert_eq!(Field::aligned(7, isize::MIN, true).size(), -1);
    /// assert_eq!(Field::bytes(48, true).size(), 48);
    /// assert_eq!(Field::bytes(-1, false).size(), -1);
    /// assert_eq!(Field::bytes(isize::MIN, true).size(), -1);
    /// assert_eq!(Field::signed(48).size(), 48);
    /// assert_eq!(Field::signed(-1).size(), -1);
    /// assert_eq!(Field::signed(isize::MIN).size(), -1);
    /// assert_eq!(Field::unsigned(48).size(), 48);
    /// assert_eq!(Field::unsigned(-1).size(), -1);
    /// assert_eq!(Field::unsigned(isize::MIN).size(), -1);
    /// ```
    pub fn size(&self) -> isize { if self.size < 0 { -1 } else { self.size } }

    /// Minimum number of bits extracted by the field.
    ///
    /// Example
    /// ```
    /// # use bit_byte_bit::{Field};
    /// assert_eq!(Field::aligned(7, 48, true).unit(), 7);
    /// assert_eq!(Field::aligned(7, -1, false).unit(), 7);
    /// assert_eq!(Field::aligned(7, isize::MIN, true).unit(), 7);
    /// assert_eq!(Field::bytes(48, true).unit(), 8);
    /// assert_eq!(Field::bytes(-1, false).unit(), 8);
    /// assert_eq!(Field::bytes(isize::MIN, true).unit(), 8);
    /// assert_eq!(Field::signed(48).unit(), 1);
    /// assert_eq!(Field::signed(-1).unit(), 1);
    /// assert_eq!(Field::signed(isize::MIN).unit(), 1);
    /// assert_eq!(Field::unsigned(48).unit(), 1);
    /// assert_eq!(Field::unsigned(-1).unit(), 1);
    /// assert_eq!(Field::unsigned(isize::MIN).unit(), 1);
    /// ```
    pub fn unit(&self) -> usize { self.unit }

    fn default(&self) -> Bits {
        let length = self.len();

        if length <= 0 {
            Bits::empty()
        } else {
            Bits::zeros(length as usize)
        }
    }

    fn extract(&self, bits: &Bits, bits_len: usize, start: usize) -> Bits {
        let length = self.len();

        if length == 0 { return Bits::empty() }

        if length < 0 { return self.extract_var_data(bits, bits_len, start); }

        let length = length as usize;
        let end = start + length;

        if end > bits_len {
            let x_len = bits_len - start;

            let mut remaining_bits = Bits::take(bits.bytes(), start, x_len);
            let signed = self.signed && remaining_bits.i(x_len - 1) == 1;

            remaining_bits.push_left(signed, end - bits_len);

            remaining_bits
        } else {
            Bits::take(bits.bytes(), start, length)
        }
    }

    fn extract_var_data(&self, bits: &Bits, bits_len: usize, start: usize) -> Bits {
        let remaining = bits_len - start;

        Bits::take(bits.bytes(), start, remaining - (remaining % self.unit))
    }
}

impl Eq for Field {}

impl PartialEq for Field {
    fn eq(&self, other: &Field) -> bool {
            self.unit == other.unit
            && self.signed == other.signed
            && ((self.size < 0 && other.size < 0) || (self.size == other.size))
    }
}


/// Defines a pattern giving meaning to different regions of a bit string.
pub struct Scheme(Vec<Field>);

impl Scheme {
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits, Field, Scheme};
    ///
    /// let unsigned_3 = Field::unsigned(3);
    ///
    /// let scheme = Scheme::new([
    ///     Field::signed(5),
    ///     Field::BIT,
    ///     unsigned_3,
    ///     unsigned_3,
    ///     Field::UNSIGNED_4,
    ///     Field::aligned(23, 1, true),
    ///     Field::unsigned(32),
    ///     Field::signed(32),
    ///     Field::bytes(4, false),
    ///     Field::aligned(6, 8, true)
    /// ]);
    ///
    /// let time_since_epoch = Field::UNSIGNED_64;
    /// let identifier = Field::UNSIGNED_8;
    /// let datatype = Field::UNSIGNED_4;
    /// let data = Field::BYTES;
    ///
    /// let scheme2 = Scheme::new([time_since_epoch, identifier, datatype, data]);
    /// ```
    pub fn new<I: IntoIterator<Item = Field>>(pattern: I) -> Self {
        Scheme(pattern.into_iter().collect())
    }

    /// Number of bits extracted
    ///
    /// If any field in the scheme has a negative length, this method returns -1, indicating
    /// the scheme extracts a variable number of bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits, Field, Scheme};
    ///
    /// let unsigned_3 = Field::unsigned(3);
    ///
    /// let scheme = Scheme::new([
    ///     Field::signed(5), Field::BIT, unsigned_3, unsigned_3, Field::UNSIGNED_4
    /// ]);
    ///
    /// assert_eq!(scheme.len(), 16);
    ///
    /// let scheme2 = Scheme::new([
    ///     Field::aligned(23, 1, true),
    ///     Field::unsigned(0),
    ///     Field::unsigned(32),
    ///     Field::bytes(4, false),
    ///     Field::aligned(0, 8, false),
    ///     Field::aligned(7, 8, true)
    /// ]);
    ///
    /// let scheme3 = Scheme::new([
    ///     Field::aligned(23, 1, true),
    ///     Field::unsigned(0),
    ///     Field::unsigned(32),
    ///     Field::signed(-1),
    ///     Field::bytes(4, false),
    ///     Field::aligned(0, 8, false),
    ///     Field::aligned(7, 8, true)
    /// ]);
    ///
    /// assert_eq!(scheme3.len(), -1);
    /// ```
    pub fn len(&self) -> isize {
        let mut acc = 0;

        for field in &self.0 {
            let n = field.len();

            if n < 0 { return -1; }

            acc += n
        }

        acc
    }

    /// Extracts the data associated with the fields of this scheme
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits, Field, Scheme};
    ///
    /// let unsigned_3 = Field::unsigned(3);
    ///
    /// let scheme = Scheme::new([
    ///     Field::signed(5), Field::BIT, unsigned_3, unsigned_3, Field::UNSIGNED_4
    /// ]);
    ///
    /// let bits = Bits::new([0xBA, 0x1C]);
    /// let parts = scheme.split_bits(&bits);
    ///
    /// assert_eq!(bits_as::int8(&parts[0]), -6);
    /// assert_eq!(bits_as::uint8(&parts[1]), 1);
    /// assert_eq!(bits_as::uint8(&parts[2]), 2);
    /// assert_eq!(bits_as::uint8(&parts[3]), 6);
    /// assert_eq!(bits_as::uint8(&parts[4]), 1);
    ///
    /// let bits2 = Bits::new([0xBA]);
    /// let parts2 = scheme.split_bits(&bits2);
    ///
    /// assert_eq!(bits_as::int8(&parts2[0]), -6);
    /// assert_eq!(bits_as::uint8(&parts2[1]), 1);
    /// assert_eq!(bits_as::uint8(&parts2[2]), 2);
    /// assert_eq!(bits_as::uint8(&parts2[3]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[4]), 0);
    ///
    /// let scheme2 = Scheme::new([
    ///     Field::aligned(23, -1, true),
    ///     Field::aligned(0, -1, false),
    ///     Field::bytes(-1, false),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1),
    ///     Field::unsigned(0),
    ///     Field::unsigned(32),
    ///     Field::bytes(4, false),
    ///     Field::aligned(0, 8, false),
    ///     Field::aligned(7, 8, true),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1)
    /// ]);
    ///
    /// let bytes = [0xBA, 0xDC, 0xFE, 0x10, 0x32];
    /// let bits3 = Bits::from(bytes.as_slice()); // 38-bits
    /// let parts = scheme2.split_bits(&bits3);
    ///
    /// assert_eq!(bits_as::int32(&parts[0]), 0xFFFEDCBAu32 as i32);
    /// assert_eq!(parts[1], Bits::empty());
    /// assert_eq!(bits_as::vec_u8(&parts[2]), vec![0x21]);
    /// assert_eq!(bits_as::vec_i32(&parts[3]), vec![-28]);
    /// assert_eq!(parts[4], Bits::empty());
    /// assert_eq!(parts[5], Bits::empty());
    /// assert_eq!(parts[6], Bits::zeros(32));
    /// assert_eq!(parts[7], Bits::zeros(32));
    /// assert_eq!(parts[8], Bits::empty());
    /// assert_eq!(parts[9], Bits::zeros(56));
    /// assert_eq!(parts[10], Bits::empty());
    /// assert_eq!(parts[11], Bits::empty());
    /// ```
    pub fn split_bits(&self, bits: &Bits) -> Vec<Bits> { self.split_bits_at(0, bits) }

    /// Extracts the data associated with the fields of this scheme.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits, Field, Scheme};
    ///
    /// let unsigned_3 = Field::unsigned(3);
    ///
    /// let scheme = Scheme::new([
    ///     Field::signed(5), Field::BIT, unsigned_3, unsigned_3, Field::UNSIGNED_4
    /// ]);
    ///
    /// let bits = Bits::new([0xBA, 0x1C]);
    /// let parts = scheme.split_bits_at(0, &bits);
    ///
    /// assert_eq!(bits_as::int8(&parts[0]), -6);
    /// assert_eq!(bits_as::uint8(&parts[1]), 1);
    /// assert_eq!(bits_as::uint8(&parts[2]), 2);
    /// assert_eq!(bits_as::uint8(&parts[3]), 6);
    /// assert_eq!(bits_as::uint8(&parts[4]), 1);
    ///
    /// let parts2 = scheme.split_bits_at(8, &bits);
    ///
    /// assert_eq!(bits_as::int8(&parts2[0]), -4);
    /// assert_eq!(bits_as::uint8(&parts2[1]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[2]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[3]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[4]), 0);
    ///
    /// let scheme2 = Scheme::new([
    ///     Field::aligned(23, -1, true),
    ///     Field::aligned(0, -1, false),
    ///     Field::bytes(-1, false),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1),
    ///     Field::unsigned(0),
    ///     Field::unsigned(32),
    ///     Field::bytes(4, false),
    ///     Field::aligned(0, 8, false),
    ///     Field::aligned(7, 8, true),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1)
    /// ]);
    ///
    /// let bytes = [0xBA, 0xDC, 0xFE, 0x10, 0x32];
    /// let bits3 = Bits::from(bytes.as_slice()); // 38-bits
    /// let parts = scheme2.split_bits_at(4, &bits3);
    ///
    /// assert_eq!(bits_as::int32(&parts[0]), 0x0FEDCB);
    /// assert_eq!(parts[1], Bits::empty());
    /// assert_eq!(bits_as::vec_u8(&parts[2]), vec![0x42]);
    /// assert_eq!(bits_as::vec_i32(&parts[3]), vec![-2]);
    /// assert_eq!(parts[4], Bits::empty());
    /// assert_eq!(parts[5], Bits::empty());
    /// assert_eq!(parts[6], Bits::zeros(32));
    /// assert_eq!(parts[7], Bits::zeros(32));
    /// assert_eq!(parts[8], Bits::empty());
    /// assert_eq!(parts[9], Bits::zeros(56));
    /// assert_eq!(parts[10], Bits::empty());
    /// assert_eq!(parts[11], Bits::empty());
    /// ```
    pub fn split_bits_at(&self, index: usize, bits: &Bits) -> Vec<Bits> {
        let length = bits.len();
        let mut matches = Vec::with_capacity(self.0.len());
        let mut index = index;

        for field in &self.0 {
            if index >= length {
                matches.push(field.default());
            } else {
                let data = field.extract(&bits, length, index);

                index += data.len();
                matches.push(data);
            }
        }

        matches
    }

    /// Extracts the data associated with the fields of this scheme
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits, Field, Scheme};
    ///
    /// let unsigned_3 = Field::unsigned(3);
    ///
    /// let scheme = Scheme::new([
    ///     Field::signed(5), Field::BIT, unsigned_3, unsigned_3, Field::UNSIGNED_4
    /// ]);
    ///
    /// let parts = scheme.split_bytes([0xBA, 0x1C]);
    ///
    /// assert_eq!(bits_as::int8(&parts[0]), -6);
    /// assert_eq!(bits_as::uint8(&parts[1]), 1);
    /// assert_eq!(bits_as::uint8(&parts[2]), 2);
    /// assert_eq!(bits_as::uint8(&parts[3]), 6);
    /// assert_eq!(bits_as::uint8(&parts[4]), 1);
    ///
    /// let parts2 = scheme.split_bytes([0xBA]);
    ///
    /// assert_eq!(bits_as::int8(&parts2[0]), -6);
    /// assert_eq!(bits_as::uint8(&parts2[1]), 1);
    /// assert_eq!(bits_as::uint8(&parts2[2]), 2);
    /// assert_eq!(bits_as::uint8(&parts2[3]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[4]), 0);
    ///
    /// let scheme2 = Scheme::new([
    ///     Field::aligned(23, -1, true),
    ///     Field::aligned(0, -1, false),
    ///     Field::bytes(-1, false),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1),
    ///     Field::unsigned(0),
    ///     Field::unsigned(32),
    ///     Field::bytes(4, false),
    ///     Field::aligned(0, 8, false),
    ///     Field::aligned(7, 8, true),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1)
    /// ]);
    ///
    /// let parts = scheme2.split_bytes(vec![0xBA, 0xDC, 0xFE, 0x10, 0x32]);
    ///
    /// assert_eq!(bits_as::int32(&parts[0]), 0xFFFEDCBAu32 as i32);
    /// assert_eq!(parts[1], Bits::empty());
    /// assert_eq!(bits_as::vec_u8(&parts[2]), vec![0x21, 0x64]);
    /// assert_eq!(parts[3], Bits::zeros(1));
    /// assert_eq!(bits_as::int64(&parts[4]), 0);
    /// assert_eq!(parts[5], Bits::empty());
    /// assert_eq!(parts[6], Bits::zeros(32));
    /// assert_eq!(parts[7], Bits::zeros(32));
    /// assert_eq!(parts[8], Bits::empty());
    /// assert_eq!(parts[9], Bits::zeros(56));
    /// assert_eq!(parts[10], Bits::empty());
    /// assert_eq!(parts[11], Bits::empty());
    /// ```
    pub fn split_bytes<I: IntoIterator<Item=u8>>(&self, bytes: I) -> Vec<Bits> {
        self.split_bits_at(0, &Bits::new(bytes))
    }

    /// Extracts the data associated with the fields of this scheme.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits, Field, Scheme};
    ///
    /// let unsigned_3 = Field::unsigned(3);
    ///
    /// let scheme = Scheme::new([
    ///     Field::signed(5), Field::BIT, unsigned_3, unsigned_3, Field::UNSIGNED_4
    /// ]);
    ///
    /// let parts = scheme.split_bytes_at(0, [0xBA, 0x1C]);
    ///
    /// assert_eq!(bits_as::int8(&parts[0]), -6);
    /// assert_eq!(bits_as::uint8(&parts[1]), 1);
    /// assert_eq!(bits_as::uint8(&parts[2]), 2);
    /// assert_eq!(bits_as::uint8(&parts[3]), 6);
    /// assert_eq!(bits_as::uint8(&parts[4]), 1);
    ///
    /// let parts2 = scheme.split_bytes_at(8, [0xBA, 0x1C]);
    ///
    /// assert_eq!(bits_as::int8(&parts2[0]), -4);
    /// assert_eq!(bits_as::uint8(&parts2[1]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[2]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[3]), 0);
    /// assert_eq!(bits_as::uint8(&parts2[4]), 0);
    ///
    /// let scheme2 = Scheme::new([
    ///     Field::aligned(23, -1, true),
    ///     Field::aligned(0, -1, false),
    ///     Field::bytes(-1, false),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1),
    ///     Field::unsigned(0),
    ///     Field::unsigned(32),
    ///     Field::bytes(4, false),
    ///     Field::aligned(0, 8, false),
    ///     Field::aligned(7, 8, true),
    ///     Field::signed(-1),
    ///     Field::unsigned(-1)
    /// ]);
    ///
    /// let parts = scheme2.split_bytes_at(4, [0xBA, 0xDC, 0xFE, 0x10, 0x32]);
    ///
    /// assert_eq!(bits_as::int32(&parts[0]), 0x0FEDCB);
    /// assert_eq!(parts[1], Bits::empty());
    /// assert_eq!(bits_as::vec_u8(&parts[2]), vec![0x42]);
    /// assert_eq!(bits_as::vec_i32(&parts[3]), vec![6]);
    /// assert_eq!(parts[4], Bits::empty());
    /// assert_eq!(parts[5], Bits::empty());
    /// assert_eq!(parts[6], Bits::zeros(32));
    /// assert_eq!(parts[7], Bits::zeros(32));
    /// assert_eq!(parts[8], Bits::empty());
    /// assert_eq!(parts[9], Bits::zeros(56));
    /// assert_eq!(parts[10], Bits::empty());
    /// assert_eq!(parts[11], Bits::empty());
    /// ```
    pub fn split_bytes_at<I: IntoIterator<Item=u8>>(&self, index: usize, bytes: I) -> Vec<Bits> {
        self.split_bits_at(index, &Bits::new(bytes))
    }


}

