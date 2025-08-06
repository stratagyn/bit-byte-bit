use crate::{Bits};


macro_rules! pack_to_int {
    ($int:ty; $bytes:expr; $length_in_bits:expr; 16) =>{{
        if $length_in_bits == 0 {
            0
        } else {
            let (sat_length, mask) = if $length_in_bits >= 16 {
                (16, 0xFFFFu16 as $int)
            } else {
                ($length_in_bits, ((1u16 << $length_in_bits) - 1) as $int)
            };

            let packed_bytes = match sat_length {
                n if n <= 8 => $bytes[0] as $int,
                _ => pack_to_int!($int; $bytes[0], $bytes[1]),
            };

            packed_bytes & mask
        }
    }};
    ($int:ty; $bytes:expr; $length_in_bits:expr; 32) =>{{
        if $length_in_bits == 0 {
            0
        } else {
            let (sat_length, mask) = if $length_in_bits >= 32 {
                (32, 0xFFFFFFFFu32 as $int)
            } else {
                ($length_in_bits, ((1u32 << $length_in_bits) - 1) as $int)
            };

            let packed_bytes = match sat_length {
                n if n <= 8 => $bytes[0] as $int,
                n if n <= 16 => pack_to_int!($int; $bytes[0], $bytes[1]),
                n if n <= 24 => pack_to_int!($int; $bytes[0], $bytes[1], $bytes[2]),
                _ => pack_to_int!($int; $bytes[0], $bytes[1], $bytes[2], $bytes[3])
            };

            packed_bytes & mask
        }
    }};
    ($int:ty; $bytes:expr; $length_in_bits:expr; 64) =>{{
        if $length_in_bits == 0 {
            0
        } else {
            let (sat_length, mask) = if $length_in_bits >= 64 {
                (64, 0xFFFFFFFFFFFFFFFFu64 as $int)
            } else {
                ($length_in_bits, ((1u64 << $length_in_bits) - 1) as $int)
            };

            let packed_bytes = match sat_length {
                n if n <= 8 => $bytes[0] as $int,
                n if n <= 16 => pack_to_int!($int; $bytes[0], $bytes[1]),
                n if n <= 24 => pack_to_int!($int; $bytes[0], $bytes[1], $bytes[2]),
                n if n <= 32 => pack_to_int!($int; $bytes[0], $bytes[1], $bytes[2], $bytes[3]),
                n if n <= 40 => pack_to_int!($int;
                    $bytes[0], $bytes[1], $bytes[2], $bytes[3], $bytes[4]
                ),
                n if n <= 48 => pack_to_int!($int;
                    $bytes[0], $bytes[1], $bytes[2], $bytes[3], $bytes[4], $bytes[5]
                ),
                n if n <= 56 => pack_to_int!($int;
                    $bytes[0], $bytes[1], $bytes[2], $bytes[3], $bytes[4], $bytes[5], $bytes[6]
                ),
                _ => pack_to_int!($int;
                    $bytes[0], $bytes[1], $bytes[2], $bytes[3],
                    $bytes[4], $bytes[5], $bytes[6], $bytes[7]
                )
            };

            packed_bytes & mask
        }
    }};
    ($ty:ty; $b0:expr, $b1:expr) =>{ ($b0 as $ty) | (($b1 as $ty) << 8) };
    ($ty:ty; $b0:expr, $b1:expr, $b2:expr) => {
        pack_to_int!($ty; $b0, $b1) | (($b2 as $ty) << 16)
    };
    ($ty:ty; $b0:expr, $b1:expr, $b2:expr, $b3:expr) => {
        pack_to_int!($ty; $b0, $b1, $b2) | (($b3 as $ty) << 24)
    };
    ($ty:ty; $b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr) => {
        pack_to_int!($ty; $b0, $b1, $b2, $b3) | (($b4 as $ty) << 32)
    };
    ($ty:ty; $b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr, $b5:expr) => {
        pack_to_int!($ty; $b0, $b1, $b2, $b3, $b4) | (($b5 as $ty) << 40)
    };
    ($ty:ty; $b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr, $b5:expr, $b6:expr) => {
        pack_to_int!($ty; $b0, $b1, $b2, $b3, $b4, $b5) | (($b6 as $ty) << 48)
    };
    ($ty:ty; $b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr, $b5:expr, $b6:expr, $b7:expr) => {
        pack_to_int!($ty; $b0, $b1, $b2, $b3, $b4, $b5, $b6) | (($b7 as $ty) << 56)
    };
    ($bytes:expr; $length_in_bits:expr; 16) => {{
        if $length_in_bits == 0 {
            0
        } else {
            let (sat_length, mask) = if $length_in_bits >= 16 {
                (16, 0xFFFFFu16)
            } else {
                ($length_in_bits, ((1 << $length_in_bits) - 1))
            };

            let packed = match sat_length {
                n if n <= 8 => $bytes[0],
                _ => pack_to_int!($bytes[0], $bytes[1])
            };

            packed & mask
        }
    }};
    ($bytes:expr; $length_in_bits:expr; 32) => {{
        if $length_in_bits == 0 {
            0
        } else {
            let (sat_length, mask) = if $length_in_bits >= 32 {
                (32, 0xFFFFFFFFFu64)
            } else {
                ($length_in_bits, ((1 << $length_in_bits) - 1))
            };

            let packed = match sat_length {
                n if n <= 8 => $bytes[0],
                n if n <= 16 => pack_to_int!($bytes[0], $bytes[1]),
                n if n <= 24 => pack_to_int!($bytes[0], $bytes[1], $bytes[2]),
                _ => pack_to_int!($bytes[0], $bytes[1], $bytes[2], $bytes[3])
            };

            packed & mask
        }
    }};
    ($bytes:expr; $length_in_bits:expr; 64) => {{
        if $length_in_bits == 0 {
            0
        } else {
            let (sat_length, mask) = if $length_in_bits >= 64 {
                (64, 0xFFFFFFFFFFFFFFFFu64)
            } else {
                ($length_in_bits, ((1 << $length_in_bits) - 1))
            };

            let packed = match sat_length {
                n if n <= 8 => $bytes[0],
                n if n <= 16 => pack_to_int!($bytes[0], $bytes[1]),
                n if n <= 24 => pack_to_int!($bytes[0], $bytes[1], $bytes[2]),
                n if n <= 32 => pack_to_int!($bytes[0], $bytes[1], $bytes[2], $bytes[3]),
                n if n <= 40 => pack_to_int!($bytes[0], $bytes[1], $bytes[2], $bytes[3], $bytes[4]),
                n if n <= 48 => pack_to_int!(
                    $bytes[0], $bytes[1], $bytes[2], $bytes[3], $bytes[4], $bytes[5]
                ),
                n if n <= 56 => pack_to_int!(
                    $bytes[0], $bytes[1], $bytes[2], $bytes[3], $bytes[4], $bytes[5], $bytes[6]
                ),
                _ => pack_to_int!(
                    $bytes[0], $bytes[1], $bytes[2], $bytes[3],
                    $bytes[4], $bytes[5], $bytes[6], $bytes[7]
                )
            };

            packed & mask
        }
    }};
    ($b0:expr, $b1:expr) =>{ $b0 | ( $b1 << 8) };
    ($b0:expr, $b1:expr, $b2:expr) => { pack_to_int!($b0, $b1) | ($b2 << 16) };
    ($b0:expr, $b1:expr, $b2:expr, $b3:expr) => { pack_to_int!($b0, $b1, $b2) | ($b3 << 24) };
    ($b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr) => {
        pack_to_int!($b0, $b1, $b2, $b3) | ($b4 << 32)
    };
    ($b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr, $b5:expr) => {
        pack_to_int!($b0, $b1, $b2, $b3, $b4) | ($b5 << 40)
    };
    ($b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr, $b5:expr, $b6:expr) => {
        pack_to_int!($b0, $b1, $b2, $b3, $b4, $b5) | ($b6 << 48)
    };
    ($b0:expr, $b1:expr, $b2:expr, $b3:expr, $b4:expr, $b5:expr, $b6:expr, $b7:expr) => {
        pack_to_int!($b0, $b1, $b2, $b3, $b4, $b5, $b6) | ($b7 << 56)
    }
}

macro_rules! pack_8_bytes {
    ($bytes:expr, $i:expr) => {
        pack_to_int!(u64;
            $bytes[$i], $bytes[$i + 1], $bytes[$i + 2], $bytes[$i + 3],
            $bytes[$i + 4], $bytes[$i + 5], $bytes[$i + 6], $bytes[$i + 7]
        )
    }
}

macro_rules! sign_extend {
    ($n:expr, $bits:expr) => {
        $n | ((signed_bit_mask!($n, $bits) >> $bits) << $bits)
    }
}

macro_rules! signed_bit_mask {
    ($n:expr, $bits:expr) => {
        (!(($n >> ($bits - 1)) & 1)).wrapping_add(1)
    };
}

pub mod bits_as {

    use crate::{Bits};

    /// Converts a bit string to a vector of booleans
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{Bits, bits_as};
    /// let bits = Bits::new([0x10, 0x32]);
    /// let bools = bits_as::vec_bool(&bits);
    ///
    /// assert_eq!(bools.len(), bits.len());
    ///
    /// assert_eq!(
    ///     bools,
    ///     vec![
    ///         false, false, false, false, true, false, false, false,
    ///         false, true, false, false, true, true, false, false
    ///     ]
    /// );
    /// ```
    pub fn vec_bool(bits: &Bits) -> Vec<bool> { bits.iter().map(|bit| bit == 1).collect() }

    /// Converts a bit string to a vector of 32 bit floats
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let floats = bits_as::vec_f32(&bits);
    ///
    /// assert_eq!(floats.len(), 2);
    /// assert_eq!(floats, vec![f32::from_bits(0x76543210), f32::from_bits(0xFEDCBA98)]);
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let floats = bits_as::vec_f32(&bits);
    ///
    /// assert_eq!(floats.len(), 1);
    /// assert_eq!(floats, vec![f32::from_bits(0x00543210)]);
    /// ```
    pub fn vec_f32(bits: &Bits) -> Vec<f32> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 2) + 1);

        for i in (0..(bytes_len - (bytes_len & 3))).step_by(4) {
            packed.push(
                f32::from_bits(pack_to_int!(u32; bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]))
            );
        }

        match bytes_len & 3 {
            1 => packed.push(f32::from_bits(bytes[bytes_len - 1] as u32)),
            2 => packed.push(
                f32::from_bits(pack_to_int!(u32; bytes[bytes_len - 2], bytes[bytes_len - 1]))
            ),
            3 => packed.push(
                f32::from_bits(pack_to_int!(u32;
                bytes[bytes_len - 3],bytes[bytes_len - 2],bytes[bytes_len - 1]
            ))
            ),
            _ => ()
        }

        packed
    }

    /// Converts a bit string to a vector of 64 bit floats
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let floats = bits_as::vec_f64(&bits);
    ///
    /// assert_eq!(floats.len(), 1);
    /// assert_eq!(floats, vec![f64::from_bits(0xFEDCBA9876543210)]);
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let floats = bits_as::vec_f64(&bits);
    ///
    /// assert_eq!(floats.len(), 1);
    /// assert_eq!(floats, vec![f64::from_bits(0x0000000000543210)]);
    /// ```
    pub fn vec_f64(bits: &Bits) -> Vec<f64> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 2) + 1);
        let remaining_byte_len = bytes_len & 7;
        let max_byte = bytes_len - remaining_byte_len;

        for i in (0..max_byte).step_by(8) {
            packed.push(f64::from_bits(pack_8_bytes!(bytes, i)));
        }

        if max_byte < bytes_len {
            let remaining_bytes = &bytes[max_byte..];
            let remaining_bit_len = remaining_byte_len << 3;

            packed.push(f64::from_bits(
                pack_to_int!(u64; remaining_bytes; remaining_bit_len; 64))
            );
        }

        packed
    }

    /// Converts a bit string to a vector of 8 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 8 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ibytes = bits_as::vec_i8(&bits);
    ///
    /// assert_eq!(ibytes.len(), 2);
    /// assert_eq!(ibytes, vec![0x10, 0xFEu8 as i8]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ibytes = bits_as::vec_i8(&bits);
    ///
    /// assert_eq!(ibytes.len(), 2);
    /// assert_eq!(ibytes, vec![0x10, 0xDEu8 as i8]);
    /// ```
    pub fn vec_i8(bits: &Bits) -> Vec<i8> {
        if bits.padding == 0 {
            bits.bytes().iter().map(|b| *b as i8).collect()
        } else {
            let bytes = bits.bytes();

            let mut packed = bytes[..(bytes.len() - 1)].iter()
                .map(|b| *b as i8)
                .collect::<Vec<_>>();

            let overflow = 8 - bits.padding;
            let last_byte = bytes[bytes.len() - 1];

            packed.push(sign_extend!(last_byte, overflow) as i8);

            packed
        }
    }

    /// Converts a bit string to a vector of 16 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 16 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ishorts = bits_as::vec_i16(&bits);
    ///
    /// assert_eq!(ishorts.len(), 1);
    /// assert_eq!(ishorts, vec![0xFE10u16 as i16]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ishorts = bits_as::vec_i16(&bits);
    ///
    /// assert_eq!(ishorts.len(), 1);
    /// assert_eq!(ishorts, vec![0xDE10u16 as i16]);
    /// ```
    pub fn vec_i16(bits: &Bits) -> Vec<i16> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 1) + 1);
        let remaining = bytes_len & 1;

        for i in (0..(bytes_len - remaining)).step_by(2) {
            packed.push(pack_to_int!(u16; bytes[i], bytes[i + 1]) as i16);
        }

        let overflow = 8 - bits.padding;

        if remaining == 1 {
            let last_byte = bytes[bytes.len() - 1] as u16;

            packed.push(sign_extend!(last_byte, overflow) as i16);
        } else if bits.padding != 0 {
            let last_byte = packed.pop().unwrap() as u16;

            packed.push(sign_extend!(last_byte, 8 + overflow) as i16);
        }

        packed
    }

    /// Converts a bit string to a vector of 32 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 32 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let ints = bits_as::vec_i32(&bits);
    ///
    /// assert_eq!(ints.len(), 1);
    /// assert_eq!(ints, vec![0x76543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let ints = bits_as::vec_i32(&bits);
    ///
    /// assert_eq!(ints.len(), 1);
    /// assert_eq!(ints, vec![0xF6543210u32 as i32]);
    /// ```
    pub fn vec_i32(bits: &Bits) -> Vec<i32> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 2) + 1);
        let remaining = bytes_len & 3;

        for i in (0..(bytes_len - remaining)).step_by(4) {
            packed.push(
                pack_to_int!(u32; bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]) as i32
            );
        }

        if remaining == 0 && bits.padding == 0 { return packed; }

        let overflow = 8 - bits.padding;

        let (packed_bytes, byte_len) = match remaining {
            0 => (packed.pop().unwrap() as u32, 24),
            1 => (bytes[bytes.len() - 1] as u32, 0),
            2 => (pack_to_int!(u32; bytes[bytes_len - 2], bytes[bytes_len - 1]), 8),
            _ => (
                pack_to_int!(u32; bytes[bytes_len - 3], bytes[bytes_len - 2], bytes[bytes_len - 1]),
                16
            )
        };

        let length = byte_len + overflow;

        packed.push(sign_extend!(packed_bytes, length) as i32);

        packed
    }

    /// Converts a bit string to a vector of 64 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 64 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let longs = bits_as::vec_i64(&bits);
    ///
    /// assert_eq!(longs.len(), 1);
    /// assert_eq!(longs, vec![0x0000000076543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let longs = bits_as::vec_i64(&bits);
    ///
    /// assert_eq!(longs.len(), 1);
    /// assert_eq!(longs, vec![0xFFFFFFFFF6543210u64 as i64]);
    /// ```
    pub fn vec_i64(bits: &Bits) -> Vec<i64> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 2) + 1);
        let remaining_byte_len = bytes_len & 7;
        let max_byte = bytes_len - remaining_byte_len;

        for i in (0..max_byte).step_by(8) {
            packed.push(pack_8_bytes!(bytes, i) as i64);
        }

        if remaining_byte_len == 0 && bits.padding == 0 { return packed; }

        let overflow = 8 - bits.padding;

        let (last_bytes, length) = if remaining_byte_len == 0 {
            (packed.pop().unwrap() as u64, 56 + overflow)
        } else {
            let remaining_bytes = &bytes[max_byte..];
            let remaining_bit_len = remaining_byte_len << 3;

            (
                pack_to_int!(u64; remaining_bytes; remaining_bit_len; 64),
                ((remaining_byte_len - 1) << 3) + overflow
            )
        };

        packed.push(sign_extend!(last_bytes, length) as i64);

        packed
    }

    /// Converts a bit string to a vector of 8 bit unsigned integers.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let bytes = bits_as::vec_u8(&bits);
    ///
    /// assert_eq!(bytes.len(), 2);
    /// assert_eq!(bytes, vec![0x10, 0xFE]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let bytes = bits_as::vec_u8(&bits);
    ///
    /// assert_eq!(bytes.len(), 2);
    /// assert_eq!(bytes, vec![0x10, 0x5E]);
    /// ```
    pub fn vec_u8(bits: &Bits) -> Vec<u8> { bits.bytes().to_vec() }

    /// Converts a bit string to a vector of 16 bit unsigned integers.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let shorts = bits_as::vec_u16(&bits);
    ///
    /// assert_eq!(shorts.len(), 1);
    /// assert_eq!(shorts, vec![0xFE10]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let shorts = bits_as::vec_u16(&bits);
    ///
    /// assert_eq!(shorts.len(), 1);
    /// assert_eq!(shorts, vec![0x5E10])
    /// ```
    pub fn vec_u16(bits: &Bits) -> Vec<u16> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 1) + 1);

        for i in (0..(bytes_len - (bytes_len & 1))).step_by(2) {
            packed.push(pack_to_int!(u16; bytes[i], bytes[i + 1]));
        }

        if (bytes_len & 1) == 1 {
            packed.push(bytes[bytes_len - 1] as u16);
        }

        packed
    }

    /// Converts a bit string to a vector of 32 bit unsigned integers.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let uints = bits_as::vec_u32(&bits);
    ///
    /// assert_eq!(uints.len(), 1);
    /// assert_eq!(uints, vec![0x76543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let uints = bits_as::vec_u32(&bits);
    ///
    /// assert_eq!(uints.len(), 1);
    /// assert_eq!(uints, vec![0x76543210]);
    /// ```
    pub fn vec_u32(bits: &Bits) -> Vec<u32> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 2) + 1);

        for i in (0..(bytes_len - (bytes_len & 3))).step_by(4) {
            packed.push(
                pack_to_int!(u32; bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3])
            );
        }

        match bytes_len & 3 {
            1 => packed.push(bytes[bytes_len - 1] as u32),
            2 => packed.push(pack_to_int!(u32; bytes[bytes_len - 2], bytes[bytes_len - 1])),
            3 => packed.push(
                pack_to_int!(u32;
                bytes[bytes_len - 3],bytes[bytes_len - 2],bytes[bytes_len - 1]
            )
            ),
            _ => ()
        }

        packed
    }

    /// Converts a bit string to a vector of 64 bit unsigned integers.
    ///
    /// If the length of the the bit string is not divisible by 64 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let ulongs = bits_as::vec_u64(&bits);
    ///
    /// assert_eq!(ulongs.len(), 1);
    /// assert_eq!(ulongs, vec![0x0000000076543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let ulongs = bits_as::vec_u64(&bits);
    ///
    /// assert_eq!(ulongs.len(), 1);
    /// assert_eq!(ulongs, vec![0x0000000076543210]);
    /// ```
    pub fn vec_u64(bits: &Bits) -> Vec<u64> {
        if bits.nbits == 0 { return vec![]; }

        let bytes = bits.bytes();
        let bytes_len = bytes.len();
        let mut packed = Vec::with_capacity(((bytes_len - 1) >> 2) + 1);
        let remaining_byte_len = bytes_len & 7;
        let max_byte = bytes_len - remaining_byte_len;

        for i in (0..max_byte).step_by(8) {
            packed.push(pack_8_bytes!(bytes, i));
        }

        if max_byte < bytes_len {
            let remaining_bytes = &bytes[max_byte..];
            let remaining_bit_len = remaining_byte_len << 3;

            packed.push(pack_to_int!(u64; remaining_bytes; remaining_bit_len; 64));
        }

        packed
    }

    /// Converts up to the first 32 bits of a bit string to a 32 bit float
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let float = bits_as::float32(&bits);
    ///
    /// assert_eq!(float, f32::from_bits(0x76543210));
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let float = bits_as::float32(&bits);
    ///
    /// assert_eq!(float, f32::from_bits(0x00543210));
    /// ```
    pub fn float32(bits: &Bits) -> f32 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0.0,
            1 => f32::from_bits(bytes[0] as u32),
            2 => f32::from_bits(pack_to_int!(u32; bytes[0], bytes[1])),
            3 => f32::from_bits(pack_to_int!(u32; bytes[0], bytes[1], bytes[2])),
            _ => f32::from_bits(pack_to_int!(u32; bytes[0], bytes[1], bytes[2], bytes[3])),
        }
    }

    /// Converts up to the first 64 bits of a bit string to a 64 bit float
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let float = bits_as::float64(&bits);
    ///
    /// assert_eq!(float, f64::from_bits(0xFEDCBA9876543210));
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let float = bits_as::float64(&bits);
    ///
    /// assert_eq!(float, f64::from_bits(0x0000000000543210));
    /// ```
    pub fn float64(bits: &Bits) -> f64 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0.0,
            1 => f64::from_bits(bytes[0] as u64),
            2 => f64::from_bits(pack_to_int!(u64; bytes[0], bytes[1])),
            3 => f64::from_bits(pack_to_int!(u64; bytes[0], bytes[1], bytes[2])),
            4 => f64::from_bits(pack_to_int!(u64; bytes[0], bytes[1], bytes[2], bytes[3])),
            5 => f64::from_bits(pack_to_int!(u64; bytes[0], bytes[1], bytes[2], bytes[3], bytes[4])),
            6 => f64::from_bits(pack_to_int!(u64;
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5]
        )),
            7 => f64::from_bits(pack_to_int!(u64;
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6]
        )),
            _ => f64::from_bits(pack_to_int!(u64;
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]
        ))
        }
    }

    /// Converts up to the first 8 bits of a bit string to 8 bit signed integer.
    ///
    /// If the length of the the bit string is less than 8, the result is sign-extended to 8 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0xFE]);
    /// let ibyte = bits_as::int8(&bits);
    ///
    /// assert_eq!(ibyte, 0xFEu8 as i8);
    ///
    /// let bits = Bits::from([0x5E]);
    /// let ibyte = bits_as::int8(&bits);
    ///
    /// assert_eq!(ibyte, 0xDEu8 as i8);
    /// ```
    pub fn int8(bits: &Bits) -> i8 {
        match bits.words.nbytes {
            0 => 0,
            1 => {
                let byte = bits.words[0];

                if bits.padding > 0 {
                    let overflow = 8 - bits.padding;

                    sign_extend!(byte, overflow) as i8
                } else {
                    byte as i8
                }
            }
            _ => bits.words[0] as i8
        }
    }

    /// Converts up the first 16 bits of a bit string to a 16 bit signed integer.
    ///
    /// If the length of the the bit string is less than 16, the result is sign-extended to 16 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ishort = bits_as::int16(&bits);
    ///
    /// assert_eq!(ishort, 0xFE10u16 as i16);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ishort = bits_as::int16(&bits);
    ///
    /// assert_eq!(ishort, 0xDE10u16 as i16);
    /// ```
    pub fn int16(bits: &Bits) -> i16 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0,
            1 => {
                let byte = bits.words[0] as u16;
                let overflow = 8 - bits.padding;

                sign_extend!(byte, overflow) as i16
            },
            2  if bits.padding > 0 => {
                let bytes = pack_to_int!(u16; bytes[0], bytes[1]);
                let overflow = 8 - bits.padding;

                sign_extend!(bytes, overflow + 8) as i16
            }
            _ => pack_to_int!(u16; bytes[0], bytes[1]) as i16
        }
    }

    /// Converts up to the first 32 bits of a bit string to a 32 bit signed integer.
    ///
    /// If the length of the the bit string is less than 32, the result is sign-extended to 32 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let int = bits_as::int32(&bits);
    ///
    /// assert_eq!(int, 0x76543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let int = bits_as::int32(&bits);
    ///
    /// assert_eq!(int, 0xF6543210u32 as i32);
    /// ```
    pub fn int32(bits: &Bits) -> i32 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0,
            1 => {
                let byte = bits.words[0] as u32;
                let overflow = 8 - bits.padding;

                sign_extend!(byte, overflow) as i32
            },
            2 => {
                let packed_bytes = pack_to_int!(u32; bytes[0], bytes[1]);
                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 8) as i32
            }
            3 => {
                let packed_bytes = pack_to_int!(u32; bytes[0], bytes[1], bytes[2]);
                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 16) as i32
            }
            4 if bits.padding > 0 => {
                let packed_bytes = pack_to_int!(u32; bytes[0], bytes[1], bytes[2], bytes[3]);
                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 24) as i32
            }
            _ => pack_to_int!(u32; bytes[0], bytes[1], bytes[2], bytes[3]) as i32,
        }
    }

    /// Converts up to the first 64 bits of a bit string to a 64 bit signed integer.
    ///
    /// If the length of the the bit string is less than 64, the result is sign-extended to 64 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let long = bits_as::int64(&bits);
    ///
    /// assert_eq!(long, 0x0000000076543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let long = bits_as::int64(&bits);
    ///
    /// assert_eq!(long, 0xFFFFFFFFF6543210u64 as i64);
    /// ```
    pub fn int64(bits: &Bits) -> i64 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0,
            1 => {
                let byte = bits.words[0] as u64;
                let overflow = 8 - bits.padding;

                sign_extend!(byte, overflow) as i64
            },
            2 => {
                let packed_bytes = pack_to_int!(u64; bytes[0], bytes[1]);
                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 8) as i64
            },
            3 => {
                let packed_bytes = pack_to_int!(u64; bytes[0], bytes[1], bytes[2]);
                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 16) as i64
            },
            4 => {
                let packed_bytes = pack_to_int!(u64; bytes[0], bytes[1], bytes[2], bytes[3]);
                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 24) as i64
            },
            5 => {
                let packed_bytes = pack_to_int!(u64;
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4]
            );

                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 32) as i64
            },
            6 => {
                let packed_bytes = pack_to_int!(u64;
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5]
            );

                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 40) as i64
            },
            7 => {
                let packed_bytes = pack_to_int!(u64;
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6]
            );

                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 48) as i64
            },
            8 if bits.padding > 0 => {
                let packed_bytes = pack_to_int!(u64;
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]
            );

                let overflow = 8 - bits.padding;

                sign_extend!(packed_bytes, overflow + 56) as i64
            },
            _ => pack_to_int!(u64;
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]
            ) as i64
        }
    }

    /// Converts up to the first 8 bits of a bit string to a 8 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0xFE]);
    /// let byte = bits_as::uint8(&bits);
    ///
    /// assert_eq!(byte, 0xFE);
    ///
    /// let bits = Bits::from([0x5E]);
    /// let byte = bits_as::uint8(&bits);
    ///
    /// assert_eq!(byte, 0x5E);
    /// ```
    pub fn uint8(bits: &Bits) -> u8 { *bits.bytes().first().unwrap_or(&0) }

    /// Converts up the first 16 bits of a bit string to a 16 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ushort = bits_as::uint16(&bits);
    ///
    /// assert_eq!(ushort, 0xFE10);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ushort = bits_as::uint16(&bits);
    ///
    /// assert_eq!(ushort, 0x5E10);
    /// ```
    pub fn uint16(bits: &Bits) -> u16 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0,
            1 => bytes[0] as u16,
            _ => pack_to_int!(u16; bytes[0], bytes[1])
        }
    }

    /// Converts up to the first 32 bits of a bit string to a 32 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let uint = bits_as::uint32(&bits);
    ///
    /// assert_eq!(uint, 0x76543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let uint = bits_as::uint32(&bits);
    ///
    /// assert_eq!(uint, 0x76543210);
    /// ```
    pub fn uint32(bits: &Bits) -> u32 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0,
            1 => bytes[0] as u32,
            2 => pack_to_int!(u32; bytes[0], bytes[1]),
            3 => pack_to_int!(u32; bytes[0], bytes[1], bytes[2]),
            _ => pack_to_int!(u32; bytes[0], bytes[1], bytes[2], bytes[3]),
        }
    }

    /// Converts up to the first 64 bits of a bit string to a 64 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::{bits_as, Bits};
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let ulong = bits_as::uint64(&bits);
    ///
    /// assert_eq!(ulong, 0x0000000076543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let ulong = bits_as::uint64(&bits);
    ///
    /// assert_eq!(ulong, 0x0000000076543210);
    /// ```
    pub fn uint64(bits: &Bits) -> u64 {
        let bytes = bits.bytes();

        match bytes.len() {
            0 => 0,
            1 => bytes[0] as u64,
            2 => pack_to_int!(u64; bytes[0], bytes[1]),
            3 => pack_to_int!(u64; bytes[0], bytes[1], bytes[2]),
            4 => pack_to_int!(u64; bytes[0], bytes[1], bytes[2], bytes[3]),
            5 => pack_to_int!(u64; bytes[0], bytes[1], bytes[2], bytes[3], bytes[4]),
            6 => pack_to_int!(u64; bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5]),
            7 => pack_to_int!(u64;
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6]
        ),
            _ => pack_to_int!(u64;
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]
            )
        }
    }
}

impl From<Bits> for Vec<bool> {
    /// Converts a bit string to a vector of booleans
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32]);
    /// let bools = Vec::<bool>::from(bits);
    ///
    /// assert_eq!(bools.len(), 16);
    ///
    /// assert_eq!(
    ///     bools,
    ///     vec![
    ///         false, false, false, false, true, false, false, false,
    ///         false, true, false, false, true, true, false, false
    ///     ]
    /// );
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_bool(&bits) }
}

impl From<Bits> for Vec<f32> {
    /// Converts a bit string to a vector of 32 bit floats
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let floats = Vec::<f32>::from(bits);
    ///
    /// assert_eq!(floats.len(), 2);
    /// assert_eq!(floats, vec![f32::from_bits(0x76543210), f32::from_bits(0xFEDCBA98)]);
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let floats = Vec::<f32>::from(bits);
    ///
    /// assert_eq!(floats.len(), 1);
    /// assert_eq!(floats, vec![f32::from_bits(0x00543210)]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_f32(&bits) }
}

impl From<Bits> for Vec<f64> {
    /// Converts a bit string to a vector of 64 bit floats
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let floats = Vec::<f64>::from(bits);
    ///
    /// assert_eq!(floats.len(), 1);
    /// assert_eq!(floats, vec![f64::from_bits(0xFEDCBA9876543210)]);
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let floats = Vec::<f64>::from(bits);
    ///
    /// assert_eq!(floats.len(), 1);
    /// assert_eq!(floats, vec![f64::from_bits(0x0000000000543210)]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_f64(&bits) }
}

impl From<Bits> for Vec<i8> {
    /// Converts a bit string to a vector of 8 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 8 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ibytes = Vec::<i8>::from(bits);
    ///
    /// assert_eq!(ibytes.len(), 2);
    /// assert_eq!(ibytes, vec![0x10, 0xFEu8 as i8]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ibytes = Vec::<i8>::from(bits);
    ///
    /// assert_eq!(ibytes.len(), 2);
    /// assert_eq!(ibytes, vec![0x10, 0xDEu8 as i8]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_i8(&bits) }
}

impl From<Bits> for Vec<i16> {
    /// Converts a bit string to a vector of 16 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 16 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ishorts = Vec::<i16>::from(bits);
    ///
    /// assert_eq!(ishorts.len(), 1);
    /// assert_eq!(ishorts, vec![0xFE10u16 as i16]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ishorts = Vec::<i16>::from(bits);
    ///
    /// assert_eq!(ishorts.len(), 1);
    /// assert_eq!(ishorts, vec![0xDE10u16 as i16]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_i16(&bits) }
}

impl From<Bits> for Vec<i32> {
    /// Converts a bit string to a vector of 32 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 32 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let ints = Vec::<i32>::from(bits);
    ///
    /// assert_eq!(ints.len(), 1);
    /// assert_eq!(ints, vec![0x76543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let ints = Vec::<i32>::from(bits);
    ///
    /// assert_eq!(ints.len(), 1);
    /// assert_eq!(ints, vec![0xF6543210u32 as i32]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_i32(&bits) }
}

impl From<Bits> for Vec<i64> {
    /// Converts a bit string to a vector of 64 bit signed integers.
    ///
    /// If the length of the the bit string is not divisible by 64 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let longs = Vec::<i64>::from(bits);
    ///
    /// assert_eq!(longs.len(), 1);
    /// assert_eq!(longs, vec![0x0000000076543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let longs = Vec::<i64>::from(bits);
    ///
    /// assert_eq!(longs.len(), 1);
    /// assert_eq!(longs, vec![0xFFFFFFFFF6543210u64 as i64]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_i64(&bits) }
}

impl From<Bits> for Vec<u8> {
    /// Converts a bit string to a vector of 8 bit unsigned integers.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let bytes = Vec::<u8>::from(bits);
    ///
    /// assert_eq!(bytes.len(), 2);
    /// assert_eq!(bytes, vec![0x10, 0xFE]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let bytes = Vec::<u8>::from(bits);
    ///
    /// assert_eq!(bytes.len(), 2);
    /// assert_eq!(bytes, vec![0x10, 0x5E]);
    /// ```
    fn from(bits: Bits) -> Self { bits.into_bytes().collect() }
}

impl From<Bits> for Vec<u16> {
    /// Converts a bit string to a vector of 16 bit unsigned integers.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let shorts = Vec::<u16>::from(bits);
    ///
    /// assert_eq!(shorts.len(), 1);
    /// assert_eq!(shorts, vec![0xFE10]);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let shorts = Vec::<u16>::from(bits);
    ///
    /// assert_eq!(shorts.len(), 1);
    /// assert_eq!(shorts, vec![0x5E10])
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_u16(&bits) }
}

impl From<Bits> for Vec<u32> {
    /// Converts a bit string to a vector of 32 bit unsigned integers.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let uints = Vec::<u32>::from(bits);
    ///
    /// assert_eq!(uints.len(), 1);
    /// assert_eq!(uints, vec![0x76543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let uints = Vec::<u32>::from(bits);
    ///
    /// assert_eq!(uints.len(), 1);
    /// assert_eq!(uints, vec![0x76543210]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_u32(&bits) }
}

impl From<Bits> for Vec<u64> {
    /// Converts a bit string to a vector of 64 bit unsigned integers.
    ///
    /// If the length of the the bit string is not divisible by 64 it is
    /// sign-extended to the next length that is. Then it is converted.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let ulongs = Vec::<u64>::from(bits);
    ///
    /// assert_eq!(ulongs.len(), 1);
    /// assert_eq!(ulongs, vec![0x0000000076543210]);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let ulongs = Vec::<u64>::from(bits);
    ///
    /// assert_eq!(ulongs.len(), 1);
    /// assert_eq!(ulongs, vec![0x0000000076543210]);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::vec_u64(&bits) }
}

impl From<Bits> for f32 {
    /// Converts up to the first 32 bits of a bit string to a 32 bit float
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let float = f32::from(bits);
    ///
    /// assert_eq!(float, f32::from_bits(0x76543210));
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let float = f32::from(bits);
    ///
    /// assert_eq!(float, f32::from_bits(0x00543210));
    /// ```
    fn from(bits: Bits) -> Self { bits_as::float32(&bits) }
}

impl From<Bits> for f64 {
    /// Converts up to the first 64 bits of a bit string to a 64 bit float
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE]);
    /// let float = f64::from(bits);
    ///
    /// assert_eq!(float, f64::from_bits(0xFEDCBA9876543210));
    ///
    /// let bits = Bits::new([0x10, 0x32, 0x54]);
    /// let float = f64::from(bits);
    ///
    /// assert_eq!(float, f64::from_bits(0x0000000000543210));
    /// ```
    fn from(bits: Bits) -> Self { bits_as::float64(&bits) }
}

impl From<Bits> for i8 {
    /// Converts up to the first 8 bits of a bit string to 8 bit signed integer.
    ///
    /// If the length of the the bit string is less than 8, the result is sign-extended to 8 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0xFE]);
    /// let ibyte = i8::from(bits);
    ///
    /// assert_eq!(ibyte, 0xFEu8 as i8);
    ///
    /// let bits = Bits::from([0x5E]);
    /// let ibyte = i8::from(bits);
    ///
    /// assert_eq!(ibyte, 0xDEu8 as i8);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::int8(&bits) }
}

impl From<Bits> for i16 {
    /// Converts up the first 16 bits of a bit string to a 16 bit signed integer.
    ///
    /// If the length of the the bit string is less than 16, the result is sign-extended to 16 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ishort = i16::from(bits);
    ///
    /// assert_eq!(ishort, 0xFE10u16 as i16);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ishort = i16::from(bits);
    ///
    /// assert_eq!(ishort, 0xDE10u16 as i16);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::int16(&bits) }
}

impl From<Bits> for i32 {
    /// Converts up to the first 32 bits of a bit string to a 32 bit signed integer.
    ///
    /// If the length of the the bit string is less than 32, the result is sign-extended to 32 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let int = i32::from(bits);
    ///
    /// assert_eq!(int, 0x76543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let int = i32::from(bits);
    ///
    /// assert_eq!(int, 0xF6543210u32 as i32);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::int32(&bits) }
}

impl From<Bits> for i64 {
    /// Converts up to the first 64 bits of a bit string to a 64 bit signed integer.
    ///
    /// If the length of the the bit string is less than 64, the result is sign-extended to 64 bits.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let long = i64::from(bits);
    ///
    /// assert_eq!(long, 0x0000000076543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let long = i64::from(bits);
    ///
    /// assert_eq!(long, 0xFFFFFFFFF6543210u64 as i64);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::int64(&bits) }
}

impl From<Bits> for u8 {
    /// Converts up to the first 8 bits of a bit string to a 8 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0xFE]);
    /// let byte = u8::from(bits);
    ///
    /// assert_eq!(byte, 0xFE);
    ///
    /// let bits = Bits::from([0x5E]);
    /// let byte = u8::from(bits);
    ///
    /// assert_eq!(byte, 0x5E);
    /// ```
    fn from(bits: Bits) -> Self { bits.into_bytes().next().unwrap_or(0) }
}

impl From<Bits> for u16 {
    /// Converts up the first 16 bits of a bit string to a 16 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0xFE]);
    /// let ushort = u16::from(bits);
    ///
    /// assert_eq!(ushort, 0xFE10);
    ///
    /// let bits = Bits::from([0x10, 0x5E]);
    /// let ushort = u16::from(bits);
    ///
    /// assert_eq!(ushort, 0x5E10);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::uint16(&bits) }
}

impl From<Bits> for u32 {
    /// Converts up to the first 32 bits of a bit string to a 32 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let uint = u32::from(bits);
    ///
    /// assert_eq!(uint, 0x76543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let uint = u32::from(bits);
    ///
    /// assert_eq!(uint, 0x76543210);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::uint32(&bits) }
}

impl From<Bits> for u64 {
    /// Converts up to the first 64 bits of a bit string to a 64 bit unsigned integer.
    ///
    /// # Example
    /// ```
    /// # use bit_byte_bit::Bits;
    /// let bits = Bits::new([0x10, 0x32, 0x54, 0x76]);
    /// let ulong = u64::from(bits);
    ///
    /// assert_eq!(ulong, 0x0000000076543210);
    ///
    /// let bits = Bits::from([0x10, 0x32, 0x54, 0x76]);
    /// let ulong = u64::from(bits);
    ///
    /// assert_eq!(ulong, 0x0000000076543210);
    /// ```
    fn from(bits: Bits) -> Self { bits_as::uint64(&bits) }
}