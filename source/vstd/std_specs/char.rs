use super::super::prelude::*;
use super::super::utf8::encode_scalar;

verus! {

/// The byte width of `c`'s UTF-8 encoding, using the same scalar-value
/// boundaries as [`encode_scalar`].
#[verifier::allow_in_spec]
pub assume_specification[ char::len_utf8 ](c: char) -> usize
    returns
        encode_scalar(c as u32).len() as usize,
;

/// Unicode's `White_Space` property:
/// <https://www.unicode.org/reports/tr44/#White_Space>.
pub open spec fn is_white_space(c: char) -> bool {
    c == '\u{9}' || c == '\u{A}' || c == '\u{B}' || c == '\u{C}' || c == '\u{D}' || c == '\u{20}'
        || c == '\u{85}' || c == '\u{A0}' || c == '\u{1680}' || c == '\u{2000}' || c == '\u{2001}'
        || c == '\u{2002}' || c == '\u{2003}' || c == '\u{2004}' || c == '\u{2005}' || c
        == '\u{2006}' || c == '\u{2007}' || c == '\u{2008}' || c == '\u{2009}' || c == '\u{200A}'
        || c == '\u{2028}' || c == '\u{2029}' || c == '\u{202F}' || c == '\u{205F}' || c
        == '\u{3000}'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_whitespace ](c: char) -> (res: bool)
    returns
        is_white_space(c),
;

/// `char::is_ascii` and the ASCII class predicates, defined by the code-point ranges std
/// uses (`core::char::methods`). The `u8` versions below state the same ranges on bytes;
/// they carry no `allow_in_spec` (their spec-mode names would collide with the `char` ones).
#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii ](c: &char) -> (res: bool)
    returns
        (*c as u32) < 128,
;

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_digit ](c: &char) -> (res: bool)
    returns
        '0' <= *c && *c <= '9',
;

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_alphabetic ](c: &char) -> (res: bool)
    returns
        ('a' <= *c && *c <= 'z') || ('A' <= *c && *c <= 'Z'),
;

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_alphanumeric ](c: &char) -> (res: bool)
    returns
        ('0' <= *c && *c <= '9') || ('a' <= *c && *c <= 'z') || ('A' <= *c && *c <= 'Z'),
;

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_uppercase ](c: &char) -> (res: bool)
    returns
        'A' <= *c && *c <= 'Z',
;

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_lowercase ](c: &char) -> (res: bool)
    returns
        'a' <= *c && *c <= 'z',
;

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_whitespace ](c: &char) -> (res: bool)
    returns
        *c == ' ' || *c == '\t' || *c == '\n' || *c == '\u{C}' || *c == '\r',
;

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_hexdigit ](c: &char) -> (res: bool)
    returns
        ('0' <= *c && *c <= '9') || ('a' <= *c && *c <= 'f') || ('A' <= *c && *c <= 'F'),
;

pub assume_specification[ u8::is_ascii ](b: &u8) -> (res: bool)
    returns
        *b < 128,
;

pub assume_specification[ u8::is_ascii_digit ](b: &u8) -> (res: bool)
    returns
        b'0' <= *b && *b <= b'9',
;

pub assume_specification[ u8::is_ascii_alphabetic ](b: &u8) -> (res: bool)
    returns
        (b'a' <= *b && *b <= b'z') || (b'A' <= *b && *b <= b'Z'),
;

pub assume_specification[ u8::is_ascii_alphanumeric ](b: &u8) -> (res: bool)
    returns
        (b'0' <= *b && *b <= b'9') || (b'a' <= *b && *b <= b'z') || (b'A' <= *b && *b <= b'Z'),
;

pub assume_specification[ u8::is_ascii_whitespace ](b: &u8) -> (res: bool)
    returns
        *b == b' ' || *b == b'\t' || *b == b'\n' || *b == 0x0C || *b == b'\r',
;

} // verus!
