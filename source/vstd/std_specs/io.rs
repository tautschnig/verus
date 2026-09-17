use super::super::prelude::*;
use core::fmt::Arguments;

verus! {

// Specifications for the `std::io` printing entry points.
//
// `print!`/`println!` desugar to `std::io::_print`, and `eprint!`/`eprintln!`
// desugar to `std::io::_eprint`; both take a `core::fmt::Arguments` value built
// by the `format_args!` machinery (whose per-argument obligations are
// discharged by the specs in `std_specs::fmt`).
//
// These functions perform I/O and have no observable functional postcondition,
// so the specification is deliberately minimal: no `requires`, no `ensures`.
// The `Arguments` value is always well-formed by construction, so no
// precondition is needed to rule out unsafety. (Per the std documentation,
// these functions may panic if writing to the stream fails; that unwinding
// behavior is the default, so we do not mark them `no_unwind`.)
//
// Making these part of `vstd` means verified `exec` code can use the standard
// `println!`/`eprintln!` macros directly, without each project having to add
// its own `assume_specification`.

pub assume_specification[ std::io::_print ](args: Arguments<'_>)
;

pub assume_specification[ std::io::_eprint ](args: Arguments<'_>)
;

} // verus!
