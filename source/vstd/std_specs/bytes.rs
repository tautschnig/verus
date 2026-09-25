use super::super::arithmetic::power2::pow2;
use super::super::prelude::*;

verus! {

// Byte-order conversions of the fixed-width unsigned integers, stated byte by byte with
// shifts and masks (the form in which verified code typically reasons about them, and the
// form the hand rewrites of `rand_core` and `windows-sys` used).

/// Byte `i` (0 = least significant) of the non-negative integer `x`: `(x >> (8*i)) & 0xff`,
/// written with division so it is meaningful for any width. `pow2` is `vstd::arithmetic::power2::pow2`;
/// `lemma2_to64` gives its values for `i < 8`, and `lemma_u64_shr_is_div` relates it to a shift.
pub open spec fn byte_of(x: int, i: int) -> u8 {
    ((x / pow2((8 * i) as nat) as int) % 256) as u8
}

/// `byte_of` as a shift on a `u64` value, for use with `by (bit_vector)`.
pub broadcast proof fn lemma_byte_of_u64_shr(x: u64, i: int)
    requires
        0 <= i < 8,
    ensures
        #[trigger] byte_of(x as int, i) == ((x >> ((8 * i) as u64)) & 0xff) as u8,
{
    let sh = (8 * i) as u64;
    super::super::bits::lemma_u64_shr_is_div(x, sh);
    let q = x >> sh;
    assert((q & 0xff) as u8 == (q % 256) as u8) by (bit_vector);
    assert(byte_of(x as int, i) == ((x as nat / pow2(sh as nat)) % 256) as u8);
}

macro_rules! byte_specs {
    ($uN:ty, $n:expr) => {
        verus! {

        pub assume_specification[ <$uN>::to_le_bytes ](x: $uN) -> (r: [u8; core::mem::size_of::<$uN>()])
            ensures
                forall|i: int| 0 <= i < $n ==> #[trigger] r@[i] == byte_of(x as int, i),
            opens_invariants none
            no_unwind
        ;

        pub assume_specification[ <$uN>::to_be_bytes ](x: $uN) -> (r: [u8; core::mem::size_of::<$uN>()])
            ensures
                forall|i: int| 0 <= i < $n ==> #[trigger] r@[i] == byte_of(x as int, $n - 1 - i),
            opens_invariants none
            no_unwind
        ;

        pub assume_specification[ <$uN>::from_le_bytes ](b: [u8; core::mem::size_of::<$uN>()]) -> (r: $uN)
            ensures
                forall|i: int| 0 <= i < $n ==> #[trigger] byte_of(r as int, i) == b@[i],
            opens_invariants none
            no_unwind
        ;

        pub assume_specification[ <$uN>::from_be_bytes ](b: [u8; core::mem::size_of::<$uN>()]) -> (r: $uN)
            ensures
                forall|i: int| 0 <= i < $n ==> #[trigger] byte_of(r as int, $n - 1 - i) == b@[i],
            opens_invariants none
            no_unwind
        ;

        }
    };
}

byte_specs!(u16, 2);
byte_specs!(u32, 4);
byte_specs!(u64, 8);
byte_specs!(u128, 16);

} // verus!
