use super::super::prelude::*;
use core::fmt::{Arguments, DebugList, DebugMap, DebugSet, DebugStruct, DebugTuple, Error, Formatter};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExError(Error);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFormatter<'a>(Formatter<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExArguments<'a>(Arguments<'a>);

// Rust has a specially handled private module core::fmt::rt,
// for which we can't directly declare specifications because it is private.
// To work around this, declare our own rt module,
// which Verus specially recognizes as a stand-in for core::fmt::rt:
#[verifier::external]
mod rt {
    #[verusfmt::skip]
    #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument")]
    pub struct Argument<'a>(&'a ());

    impl<'a> Argument<'a> {
        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_binary")]
        pub fn new_binary<'b, T: core::fmt::Binary>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_debug")]
        pub fn new_debug<'b, T: core::fmt::Debug>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_debug_noop")]
        pub fn new_debug_noop<'b, T: core::fmt::Debug>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_display")]
        pub fn new_display<'b, T: core::fmt::Display>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_lower_exp")]
        pub fn new_lower_exp<'b, T: core::fmt::LowerExp>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_lower_hex")]
        pub fn new_lower_hex<'b, T: core::fmt::LowerHex>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_octal")]
        pub fn new_octal<'b, T: core::fmt::Octal>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_pointer")]
        pub fn new_pointer<'b, T: core::fmt::Pointer>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_upper_exp")]
        pub fn new_upper_exp<'b, T: core::fmt::UpperExp>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_upper_hex")]
        pub fn new_upper_hex<'b, T: core::fmt::UpperHex>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::from_usize")]
        pub fn from_usize<'b>(x: &'b usize) -> Argument<'b> {
            unimplemented!()
        }
    }

}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExArgument<'a>(rt::Argument<'a>);

macro_rules! def_fmt_trait {
    ($trait:path, $extrait: ident, $spec_trait:ident, $impl_trait:ident, $new:ident) => {
        $crate::vstd::prelude::verus! {
            #[verifier::external_trait_specification]
            #[verifier::external_trait_extension($spec_trait via $impl_trait)]
            pub trait $extrait: core::marker::PointeeSized {
                type ExternalTraitSpecificationFor: $trait;

                spec fn fmt_req(&self, f: &Formatter<'_>) -> bool;

                fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                    requires
                        self.fmt_req(f);
            }

            #[doc(hidden)]
            pub assume_specification<'a, 'b, T: $trait>[ rt::Argument::<'a>::$new ](x: &'b T) -> rt::Argument<'b>
                requires
                    forall|f: &Formatter<'a>| x.fmt_req(f),
            ;
        }
};
}

def_fmt_trait!(core::fmt::Binary, ExBinary, BinarySpec, BinarySpecImpl, new_binary);

def_fmt_trait!(core::fmt::Debug, ExDebug, DebugSpec, DebugSpecImpl, new_debug);

def_fmt_trait!(core::fmt::Display, ExDisplay, DisplaySpec, DisplaySpecImpl, new_display);

def_fmt_trait!(core::fmt::LowerExp, ExLowerExp, LowerExpSpec, LowerExpSpecImpl, new_lower_exp);

def_fmt_trait!(core::fmt::LowerHex, ExLowerHex, LowerHexSpec, LowerHexSpecImpl, new_lower_hex);

def_fmt_trait!(core::fmt::Octal, ExOctal, OctalSpec, OctalSpecImpl, new_octal);

def_fmt_trait!(core::fmt::Pointer, ExPointer, PointerSpec, PointerSpecImpl, new_pointer);

def_fmt_trait!(core::fmt::UpperExp, ExUpperExp, UpperExpSpec, UpperExpSpecImpl, new_upper_exp);

def_fmt_trait!(core::fmt::UpperHex, ExUpperHex, UpperHexSpec, UpperHexSpecImpl, new_upper_hex);

#[doc(hidden)]
pub assume_specification<'a, 'b, T: core::fmt::Debug>[ rt::Argument::<'a>::new_debug_noop ](
    x: &'b T,
) -> rt::Argument<'b>
    requires
        forall|f: &Formatter<'a>| x.fmt_req(f),
;

#[doc(hidden)]
pub assume_specification<'a, 'b>[ rt::Argument::<'a>::from_usize ](x: &'b usize) -> rt::Argument<'b>
;

pub assume_specification<'a>[ Arguments::<'a>::from_str ](s: &'static str) -> Arguments<'a>
;

pub assume_specification<'a>[ Arguments::<'a>::from_str_nonconst ](s: &'static str) -> Arguments<'a>
;

// Specially handled stand-in for Arguments::new (because it uses the private Argument type)
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::Arguments::new")]
#[verifier::external]
#[doc(hidden)]
pub fn arguments_new<'a, const N: usize, const M: usize>(
    template: &'a [u8; N],
    args: &'a [rt::Argument<'a>; M],
) -> Arguments<'a> {
    unimplemented!()
}

#[doc(hidden)]
pub assume_specification<'a, const N: usize, const M: usize>[ arguments_new ](
    template: &'a [u8; N],
    args: &'a [rt::Argument<'a>; M],
) -> Arguments<'a>
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ alloc::fmt::format ](args: Arguments<'_>) -> alloc::string::String
;

// Formatting output: content-free specifications. Nothing is known about what a
// `Formatter` or builder has written, and any write may return `Err` (a `Formatter` passes
// through the error of its destination). A value handed to a builder is later formatted by
// unverified code, so, as for `format_args!` arguments above, its `fmt_req` must hold.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDebugStruct<'a, 'b: 'a>(DebugStruct<'a, 'b>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDebugTuple<'a, 'b: 'a>(DebugTuple<'a, 'b>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDebugList<'a, 'b: 'a>(DebugList<'a, 'b>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDebugSet<'a, 'b: 'a>(DebugSet<'a, 'b>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDebugMap<'a, 'b: 'a>(DebugMap<'a, 'b>);

pub assume_specification<'a>[ Formatter::<'a>::write_str ](f: &mut Formatter<'a>, data: &str) -> Result<(), Error>;

pub assume_specification<'a>[ Formatter::<'a>::write_fmt ](f: &mut Formatter<'a>, fmt: Arguments<'_>) -> Result<(), Error>;

pub assume_specification<'a>[ Formatter::<'a>::pad ](f: &mut Formatter<'a>, s: &str) -> Result<(), Error>;

pub assume_specification<'a>[ Formatter::<'a>::pad_integral ](f: &mut Formatter<'a>, is_nonnegative: bool, prefix: &str, buf: &str) -> Result<(), Error>;

pub assume_specification<'a>[ Formatter::<'a>::alternate ](f: &Formatter<'a>) -> bool;

pub assume_specification<'a>[ Formatter::<'a>::sign_plus ](f: &Formatter<'a>) -> bool;

pub assume_specification<'a>[ Formatter::<'a>::width ](f: &Formatter<'a>) -> Option<usize>;

pub assume_specification<'a>[ Formatter::<'a>::precision ](f: &Formatter<'a>) -> Option<usize>;

pub assume_specification<'a>[ Formatter::<'a>::fill ](f: &Formatter<'a>) -> char;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_struct ](f: &'b mut Formatter<'a>, name: &str) -> DebugStruct<'b, 'a>;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_tuple ](f: &'b mut Formatter<'a>, name: &str) -> DebugTuple<'b, 'a>;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_list ](f: &'b mut Formatter<'a>) -> DebugList<'b, 'a>;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_set ](f: &'b mut Formatter<'a>) -> DebugSet<'b, 'a>;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_map ](f: &'b mut Formatter<'a>) -> DebugMap<'b, 'a>;

pub assume_specification<'c, 'a, 'b: 'a>[ DebugStruct::<'a, 'b>::field ](d: &'c mut DebugStruct<'a, 'b>, name: &str, value: &dyn core::fmt::Debug) -> &'c mut DebugStruct<'a, 'b>
    requires
        forall|f: &Formatter<'b>| value.fmt_req(f),
;

pub assume_specification<'a, 'b: 'a>[ DebugStruct::<'a, 'b>::finish ](d: &mut DebugStruct<'a, 'b>) -> Result<(), Error>;

pub assume_specification<'a, 'b: 'a>[ DebugStruct::<'a, 'b>::finish_non_exhaustive ](d: &mut DebugStruct<'a, 'b>) -> Result<(), Error>;

pub assume_specification<'c, 'a, 'b: 'a>[ DebugTuple::<'a, 'b>::field ](d: &'c mut DebugTuple<'a, 'b>, value: &dyn core::fmt::Debug) -> &'c mut DebugTuple<'a, 'b>
    requires
        forall|f: &Formatter<'b>| value.fmt_req(f),
;

pub assume_specification<'a, 'b: 'a>[ DebugTuple::<'a, 'b>::finish ](d: &mut DebugTuple<'a, 'b>) -> Result<(), Error>;

pub assume_specification<'a, 'b: 'a>[ DebugTuple::<'a, 'b>::finish_non_exhaustive ](d: &mut DebugTuple<'a, 'b>) -> Result<(), Error>;

pub assume_specification<'c, 'a, 'b: 'a>[ DebugList::<'a, 'b>::entry ](d: &'c mut DebugList<'a, 'b>, entry: &dyn core::fmt::Debug) -> &'c mut DebugList<'a, 'b>
    requires
        forall|f: &Formatter<'b>| entry.fmt_req(f),
;

pub assume_specification<'a, 'b: 'a>[ DebugList::<'a, 'b>::finish ](d: &mut DebugList<'a, 'b>) -> Result<(), Error>;

pub assume_specification<'c, 'a, 'b: 'a>[ DebugSet::<'a, 'b>::entry ](d: &'c mut DebugSet<'a, 'b>, entry: &dyn core::fmt::Debug) -> &'c mut DebugSet<'a, 'b>
    requires
        forall|f: &Formatter<'b>| entry.fmt_req(f),
;

pub assume_specification<'a, 'b: 'a>[ DebugSet::<'a, 'b>::finish ](d: &mut DebugSet<'a, 'b>) -> Result<(), Error>;

pub assume_specification<'c, 'a, 'b: 'a>[ DebugMap::<'a, 'b>::entry ](d: &'c mut DebugMap<'a, 'b>, key: &dyn core::fmt::Debug, value: &dyn core::fmt::Debug) -> &'c mut DebugMap<'a, 'b>
    requires
        forall|f: &Formatter<'b>| key.fmt_req(f),
        forall|f: &Formatter<'b>| value.fmt_req(f),
;

pub assume_specification<'a, 'b: 'a>[ DebugMap::<'a, 'b>::finish ](d: &mut DebugMap<'a, 'b>) -> Result<(), Error>;

// `fmt::Write`: the destination of `write!`. Implementors are verified against no
// requires; callers learn nothing about what was written.
#[verifier::external_trait_specification]
pub trait ExWrite {
    type ExternalTraitSpecificationFor: core::fmt::Write;

    fn write_str(&mut self, s: &str) -> Result<(), Error>;

    fn write_char(&mut self, c: char) -> Result<(), Error>;

    fn write_fmt(&mut self, args: Arguments<'_>) -> Result<(), Error>;
}

pub uninterp spec fn fmt_req_all<A>() -> bool;

macro_rules! def_type_axiom {
    ($ty:ty, $name: ident) => {
        $crate::vstd::prelude::verus! {
            pub broadcast axiom fn $name()
                ensures
                    #[trigger] fmt_req_all::<$ty>();
        }
};
}

def_type_axiom!(u8, axiom_fmt_req_all_u8);

def_type_axiom!(u16, axiom_fmt_req_all_u16);

def_type_axiom!(u32, axiom_fmt_req_all_u32);

def_type_axiom!(u64, axiom_fmt_req_all_u64);

def_type_axiom!(u128, axiom_fmt_req_all_u128);

def_type_axiom!(usize, axiom_fmt_req_all_usize);

def_type_axiom!(i8, axiom_fmt_req_all_i8);

def_type_axiom!(i16, axiom_fmt_req_all_i16);

def_type_axiom!(i32, axiom_fmt_req_all_i32);

def_type_axiom!(i64, axiom_fmt_req_all_i64);

def_type_axiom!(i128, axiom_fmt_req_all_i128);

def_type_axiom!(isize, axiom_fmt_req_all_isize);

def_type_axiom!(f32, axiom_fmt_req_all_f32);

def_type_axiom!(f64, axiom_fmt_req_all_f64);

def_type_axiom!(bool, axiom_fmt_req_all_bool);

def_type_axiom!(char, axiom_fmt_req_all_char);

def_type_axiom!(&str, axiom_fmt_req_all_str);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_type_axiom!(alloc::string::String, axiom_fmt_req_all_string);

// std types whose Debug/Display impls have no precondition (exec test
// `fmt_std_types_total` in tools/vstd-kani formats them).
#[cfg(feature = "std")]
def_type_axiom!(std::io::Error, axiom_fmt_req_all_io_error);

def_type_axiom!(core::time::Duration, axiom_fmt_req_all_duration);

#[cfg(feature = "std")]
def_type_axiom!(std::path::Display<'_>, axiom_fmt_req_all_path_display);

#[cfg(not(verus_verify_core))]
def_type_axiom!(core::num::ParseIntError, axiom_fmt_req_all_parse_int_error);

#[cfg(not(verus_verify_core))]
def_type_axiom!(core::num::ParseFloatError, axiom_fmt_req_all_parse_float_error);

def_type_axiom!(core::num::TryFromIntError, axiom_fmt_req_all_try_from_int_error);

#[cfg(not(verus_verify_core))]
def_type_axiom!(core::str::Utf8Error, axiom_fmt_req_all_utf8_error);

#[cfg(not(verus_verify_core))]
def_type_axiom!(core::str::ParseBoolError, axiom_fmt_req_all_parse_bool_error);

def_type_axiom!(core::fmt::Error, axiom_fmt_req_all_fmt_error);

#[cfg(feature = "std")]
def_type_axiom!(std::time::SystemTimeError, axiom_fmt_req_all_system_time_error);

#[cfg(feature = "std")]
def_type_axiom!(std::env::VarError, axiom_fmt_req_all_var_error);

#[cfg(feature = "std")]
def_type_axiom!(std::path::PathBuf, axiom_fmt_req_all_path_buf);

// containers whose Debug formats the elements with their Debug
pub broadcast axiom fn axiom_fmt_req_all_option<A>()
    requires
        fmt_req_all::<A>(),
    ensures
        #[trigger] fmt_req_all::<Option<A>>(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_fmt_req_all_vec<A>()
    requires
        fmt_req_all::<A>(),
    ensures
        #[trigger] fmt_req_all::<alloc::vec::Vec<A>>(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_fmt_req_all_box<A>()
    requires
        fmt_req_all::<A>(),
    ensures
        #[trigger] fmt_req_all::<alloc::boxed::Box<A>>(),
;

pub broadcast axiom fn axiom_fmt_req_all_ref<A>()
    requires
        fmt_req_all::<A>(),
    ensures
        #[trigger] fmt_req_all::<&A>(),
;

macro_rules! def_trait_axiom {
    ($trait:path, $name: ident) => {
        $crate::vstd::prelude::verus! {
            pub broadcast axiom fn $name<A: $trait>(a: &A, f: &Formatter)
                requires
                    fmt_req_all::<A>(),
                ensures
                    #[trigger] a.fmt_req(f);
        }
};
}

def_trait_axiom!(core::fmt::Binary, axiom_fmt_req_all_binary);

def_trait_axiom!(core::fmt::Debug, axiom_fmt_req_all_debug);

def_trait_axiom!(core::fmt::Display, axiom_fmt_req_all_display);

def_trait_axiom!(core::fmt::LowerExp, axiom_fmt_req_all_lower_exp);

def_trait_axiom!(core::fmt::LowerHex, axiom_fmt_req_all_lower_hex);

def_trait_axiom!(core::fmt::Octal, axiom_fmt_req_all_octal);

def_trait_axiom!(core::fmt::Pointer, axiom_fmt_req_all_pointer);

def_trait_axiom!(core::fmt::UpperExp, axiom_fmt_req_all_upper_exp);

def_trait_axiom!(core::fmt::UpperHex, axiom_fmt_req_all_upper_hex);

// `core::fmt` implements these traits for `&T` by delegation (the `fmt_ref!` impls:
// `$tr::fmt(&**self, f)`), so `&T`'s precondition is implied by `T`'s, value by value.
// (`Pointer` for `&T` prints the address instead and is not included.)
macro_rules! def_ref_axiom {
    ($trait:path, $spec:path, $name: ident) => {
        $crate::vstd::prelude::verus! {
            pub broadcast axiom fn $name<A: $trait + ?Sized>(a: &A, f: &Formatter)
                requires
                    <A as $spec>::fmt_req(a, f),
                ensures
                    #[trigger] <&A as $spec>::fmt_req(&a, f);
        }
};
}

def_ref_axiom!(core::fmt::Binary, BinarySpec, axiom_fmt_req_ref_binary);

def_ref_axiom!(core::fmt::Debug, DebugSpec, axiom_fmt_req_ref_debug);

def_ref_axiom!(core::fmt::Display, DisplaySpec, axiom_fmt_req_ref_display);

def_ref_axiom!(core::fmt::LowerExp, LowerExpSpec, axiom_fmt_req_ref_lower_exp);

def_ref_axiom!(core::fmt::LowerHex, LowerHexSpec, axiom_fmt_req_ref_lower_hex);

def_ref_axiom!(core::fmt::Octal, OctalSpec, axiom_fmt_req_ref_octal);

def_ref_axiom!(core::fmt::UpperExp, UpperExpSpec, axiom_fmt_req_ref_upper_exp);

def_ref_axiom!(core::fmt::UpperHex, UpperHexSpec, axiom_fmt_req_ref_upper_hex);

// `alloc` implements `Debug` and `Display` for `Box<T>`, `Rc<T>` and `Arc<T>` by delegation
// (`fmt::Debug::fmt(&**self, f)`), so the pointer's precondition is implied by `T`'s on the
// pointee. (`Pointer` prints the address and is not included; the other fmt traits are not
// implemented for these pointers.)
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
macro_rules! def_ptr_axiom {
    ($ptr:ident, $trait:path, $spec:path, $name: ident) => {
        $crate::vstd::prelude::verus! {
            pub broadcast axiom fn $name<A: $trait + ?Sized>(a: &$ptr<A>, f: &Formatter)
                requires
                    <A as $spec>::fmt_req(&**a, f),
                ensures
                    #[trigger] <$ptr<A> as $spec>::fmt_req(a, f);
        }
};
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::{boxed::Box, rc::Rc, sync::Arc};

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_ptr_axiom!(Box, core::fmt::Debug, DebugSpec, axiom_fmt_req_box_debug);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_ptr_axiom!(Box, core::fmt::Display, DisplaySpec, axiom_fmt_req_box_display);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_ptr_axiom!(Rc, core::fmt::Debug, DebugSpec, axiom_fmt_req_rc_debug);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_ptr_axiom!(Rc, core::fmt::Display, DisplaySpec, axiom_fmt_req_rc_display);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_ptr_axiom!(Arc, core::fmt::Debug, DebugSpec, axiom_fmt_req_arc_debug);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_ptr_axiom!(Arc, core::fmt::Display, DisplaySpec, axiom_fmt_req_arc_display);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast group group_fmt_ptr_axioms {
    axiom_debug_elements_vec_deque,
    axiom_debug_elements_btree_set,
    axiom_debug_elements_btree_map,
    axiom_fmt_req_box_debug,
    axiom_fmt_req_box_display,
    axiom_fmt_req_rc_debug,
    axiom_fmt_req_rc_display,
    axiom_fmt_req_arc_debug,
    axiom_fmt_req_arc_display,
}

/// `debug_elements::<C, A>()` declares that `C`'s `Debug` impl formats values of type `A` with
/// `A`'s `Debug` and calls nothing else with a precondition (core's `debug_list`, `debug_set`,
/// `debug_map`; a map states it for its key and its value type). It has no meaning in proofs;
/// Verus's derived-`fmt_req` synthesis (`synthesize_derived_fmt_impls`) reads the broadcast
/// axioms that state it, and walks through such a container to its elements as through `Vec`.
/// Trusted, like any axiom: state it only for an impl that formats exactly so.
pub uninterp spec fn debug_elements<C, A>() -> bool;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_debug_elements_vec_deque<T>()
    ensures
        #[trigger] debug_elements::<alloc::collections::VecDeque<T>, T>(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_debug_elements_btree_set<K>()
    ensures
        #[trigger] debug_elements::<alloc::collections::BTreeSet<K>, K>(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_debug_elements_btree_map<K, V>()
    ensures
        #[trigger] debug_elements::<alloc::collections::BTreeMap<K, V>, K>(),
        #[trigger] debug_elements::<alloc::collections::BTreeMap<K, V>, V>(),
;

#[cfg(all(feature = "std", not(verus_verify_core)))]
pub broadcast axiom fn axiom_debug_elements_hash_set<K, S>()
    ensures
        #[trigger] debug_elements::<std::collections::HashSet<K, S>, K>(),
;

#[cfg(all(feature = "std", not(verus_verify_core)))]
pub broadcast axiom fn axiom_debug_elements_hash_map<K, V, S>()
    ensures
        #[trigger] debug_elements::<std::collections::HashMap<K, V, S>, K>(),
        #[trigger] debug_elements::<std::collections::HashMap<K, V, S>, V>(),
;

#[cfg(all(feature = "std", not(verus_verify_core)))]
pub broadcast group group_fmt_std_container_axioms {
    axiom_debug_elements_hash_set,
    axiom_debug_elements_hash_map,
}

pub broadcast group group_fmt_axioms {
    // types
    axiom_fmt_req_all_u8,
    axiom_fmt_req_all_u16,
    axiom_fmt_req_all_u32,
    axiom_fmt_req_all_u64,
    axiom_fmt_req_all_u128,
    axiom_fmt_req_all_usize,
    axiom_fmt_req_all_i8,
    axiom_fmt_req_all_i16,
    axiom_fmt_req_all_i32,
    axiom_fmt_req_all_i64,
    axiom_fmt_req_all_i128,
    axiom_fmt_req_all_isize,
    axiom_fmt_req_all_f32,
    axiom_fmt_req_all_f64,
    axiom_fmt_req_all_bool,
    axiom_fmt_req_all_char,
    axiom_fmt_req_all_str,
    #[cfg(all(feature = "alloc", not(verus_verify_core)))]
    axiom_fmt_req_all_string,
    axiom_fmt_req_all_ref,
    #[cfg(feature = "std")]
    axiom_fmt_req_all_io_error,
    axiom_fmt_req_all_duration,
    #[cfg(feature = "std")]
    axiom_fmt_req_all_path_display,
    #[cfg(not(verus_verify_core))]
    axiom_fmt_req_all_parse_int_error,
    #[cfg(not(verus_verify_core))]
    axiom_fmt_req_all_parse_float_error,
    axiom_fmt_req_all_try_from_int_error,
    #[cfg(not(verus_verify_core))]
    axiom_fmt_req_all_utf8_error,
    #[cfg(not(verus_verify_core))]
    axiom_fmt_req_all_parse_bool_error,
    axiom_fmt_req_all_fmt_error,
    #[cfg(feature = "std")]
    axiom_fmt_req_all_system_time_error,
    #[cfg(feature = "std")]
    axiom_fmt_req_all_var_error,
    #[cfg(feature = "std")]
    axiom_fmt_req_all_path_buf,
    axiom_fmt_req_all_option,
    #[cfg(all(feature = "alloc", not(verus_verify_core)))]
    axiom_fmt_req_all_vec,
    #[cfg(all(feature = "alloc", not(verus_verify_core)))]
    axiom_fmt_req_all_box,
    // traits
    axiom_fmt_req_all_binary,
    axiom_fmt_req_all_debug,
    axiom_fmt_req_all_display,
    axiom_fmt_req_all_lower_exp,
    axiom_fmt_req_all_lower_hex,
    axiom_fmt_req_all_octal,
    axiom_fmt_req_all_pointer,
    axiom_fmt_req_all_upper_exp,
    axiom_fmt_req_all_upper_hex,
    // `&T` by delegation
    axiom_fmt_req_ref_binary,
    axiom_fmt_req_ref_debug,
    axiom_fmt_req_ref_display,
    axiom_fmt_req_ref_lower_exp,
    axiom_fmt_req_ref_lower_hex,
    axiom_fmt_req_ref_octal,
    axiom_fmt_req_ref_upper_exp,
    axiom_fmt_req_ref_upper_hex,
}

} // verus!
