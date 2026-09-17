# Generated-harness coverage report

Generator: `generate.py`  •  std_specs: `/home/ubuntu/verus.git/source/vstd/std_specs`

**Emitted 56 Kani harnesses** into `src/generated.rs`.

## Per-file textual `assume_specification` sites

| file | sites | harnesses emitted |
|---|---|---|
| num.rs | 52 | 56 |
| cmp.rs | 24 | 0 |
| ops.rs | 13 | 0 |
| bits.rs | 16 | 0 |
| result.rs | 10 | 0 |
| option.rs | 23 | 0 |

Total textual sites across the six files: 138.
num.rs sites are macro templates instantiated over 6 integer pairs.

## Skips (grouped by reason)

### trait-method item carries no inline postcondition (contract on extension trait)  — 108

- `num.rs:35`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:80`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:82`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:84`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:86`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:88`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:90`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:92`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:94`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:299`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:344`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:346`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:348`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:350`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:352`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:354`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:356`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:358`  [types: u128,u16,u32,u64,u8,usize]

### references macro-local spec module ($mod_*) — postcondition delegates to a vstd wrapping/spec fn (R3)  — 72

- `num.rs:98`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:105`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:112`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:119`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:126`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:133`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:362`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:369`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:376`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:383`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:390`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:397`  [types: u128,u16,u32,u64,u8,usize]

### multi-clause ensures (R1)  — 37

- `cmp.rs:279`
- `cmp.rs:285`
- `cmp.rs:290`
- `cmp.rs:295`
- `cmp.rs:300`
- `cmp.rs:305`
- `cmp.rs:310`
- `cmp.rs:316`
- `cmp.rs:322`
- `cmp.rs:327`
- `cmp.rs:332`
- `cmp.rs:337`
- `cmp.rs:342`
- `cmp.rs:347`
- `ops.rs:754`
- `ops.rs:759`
- `ops.rs:764`
- `ops.rs:769`
- `ops.rs:774`
- `ops.rs:779`
- `ops.rs:784`
- `ops.rs:789`
- `ops.rs:794`
- `ops.rs:799`
- `option.rs:143`
- `option.rs:201`
- `option.rs:209`
- `option.rs:227`
- `option.rs:239`
- `option.rs:363`
- `option.rs:372`
- `option.rs:381`
- `option.rs:395`
- `option.rs:402`
- `result.rs:155`
- `result.rs:226`
- `result.rs:242`

### R6 tractability: division/remainder is only CBMC-tractable at 8-bit within the CI budget  — 20

- `num.rs:225`  [types: u16,u32,u64,usize]
- `num.rs:238`  [types: u16,u32,u64,usize]
- `num.rs:287`  [types: u16,u32,u64,usize]
- `num.rs:476`  [types: u16,u32,u64,usize]
- `num.rs:500`  [types: u16,u32,u64,usize]

### i128 widening insufficient: needs 130 bits (sum of 128-bit) (R5)  — 19

- `num.rs:140`  [types: u128]
- `num.rs:152`  [types: u128]
- `num.rs:164`  [types: u128]
- `num.rs:188`  [types: u128]
- `num.rs:210`  [types: u128]
- `num.rs:217`  [types: u128]
- `num.rs:225`  [types: u128]
- `num.rs:238`  [types: u128]
- `num.rs:251`  [types: u128]
- `num.rs:263`  [types: u128]
- `num.rs:287`  [types: u128]
- `num.rs:404`  [types: u128]
- `num.rs:416`  [types: u128]
- `num.rs:428`  [types: u128]
- `num.rs:440`  [types: u128]
- `num.rs:464`  [types: u128]
- `num.rs:476`  [types: u128]
- `num.rs:488`  [types: u128]
- `num.rs:500`  [types: u128]

### no inline postcondition (contract on extension trait / separate spec fn) (R1)  — 16

- `cmp.rs:250`
- `cmp.rs:252`
- `cmp.rs:367`
- `cmp.rs:375`
- `cmp.rs:396`
- `cmp.rs:404`
- `cmp.rs:412`
- `cmp.rs:420`
- `cmp.rs:428`
- `cmp.rs:446`
- `ops.rs:360`
- `ops.rs:384`
- `ops.rs:408`
- `option.rs:298`
- `option.rs:320`
- `option.rs:341`

### references non-translatable symbol: checked_div  — 10

- `num.rs:210`  [types: u16,u32,u64,u8,usize]
- `num.rs:217`  [types: u16,u32,u64,u8,usize]

### i128 widening insufficient: needs 130 bits (product of 64-bit) (R5)  — 6

- `num.rs:176`  [types: u64,usize]
- `num.rs:275`  [types: u64,usize]
- `num.rs:452`  [types: u64,usize]

### expected '{' got ('ID', 'if')  — 5

- `num.rs:188`  [types: u16,u32,u64,u8,usize]

### references non-translatable symbol: rust_div  — 5

- `num.rs:464`  [types: u16,u32,u64,u8,usize]

### references non-translatable symbol: rust_rem  — 5

- `num.rs:488`  [types: u16,u32,u64,u8,usize]

### unexpected char '.' in expr  — 4

- `option.rs:219`
- `option.rs:254`
- `option.rs:263`
- `option.rs:275`

### R6 tractability: multiplication is only CBMC-tractable up to 16-bit within the CI budget  — 3

- `num.rs:176`  [types: u32]
- `num.rs:275`  [types: u32]
- `num.rs:452`  [types: u32]

### i128 widening insufficient: needs 258 bits (product of 128-bit) (R5)  — 3

- `num.rs:176`  [types: u128]
- `num.rs:275`  [types: u128]
- `num.rs:452`  [types: u128]

### cannot parse primary at ('OP', '>')  — 3

- `result.rs:177`
- `result.rs:196`
- `result.rs:215`

### references non-translatable symbol: u8_trailing_zeros  — 1

- `bits.rs:48`

### references non-translatable symbol: u8_trailing_ones  — 1

- `bits.rs:54`

### references non-translatable symbol: u8_leading_zeros  — 1

- `bits.rs:60`

### references non-translatable symbol: u8_leading_ones  — 1

- `bits.rs:66`

### references non-translatable symbol: u16_trailing_zeros  — 1

- `bits.rs:218`

### references non-translatable symbol: u16_trailing_ones  — 1

- `bits.rs:224`

### references non-translatable symbol: u16_leading_zeros  — 1

- `bits.rs:230`

### references non-translatable symbol: u16_leading_ones  — 1

- `bits.rs:236`

### references non-translatable symbol: u32_trailing_zeros  — 1

- `bits.rs:394`

### references non-translatable symbol: u32_trailing_ones  — 1

- `bits.rs:400`

### references non-translatable symbol: u32_leading_zeros  — 1

- `bits.rs:406`

### references non-translatable symbol: u32_leading_ones  — 1

- `bits.rs:412`

### references non-translatable symbol: u64_trailing_zeros  — 1

- `bits.rs:571`

### references non-translatable symbol: u64_trailing_ones  — 1

- `bits.rs:577`

### references non-translatable symbol: u64_leading_zeros  — 1

- `bits.rs:583`

### references non-translatable symbol: u64_leading_ones  — 1

- `bits.rs:589`

### references non-translatable symbol: is_ok  — 1

- `result.rs:135`

### references non-translatable symbol: is_err  — 1

- `result.rs:148`

### references non-translatable symbol: ok  — 1

- `result.rs:262`

### references non-translatable symbol: err  — 1

- `result.rs:278`

### references non-translatable symbol: is_some  — 1

- `option.rs:123`

### references non-translatable symbol: is_none  — 1

- `option.rs:136`

### references non-translatable symbol: spec_unwrap  — 1

- `option.rs:160`

### references non-translatable symbol: spec_unwrap_or  — 1

- `option.rs:177`

### references non-translatable symbol: spec_expect  — 1

- `option.rs:193`

### references non-translatable symbol: spec_ok_or  — 1

- `option.rs:357`

## Emitted harnesses

- `gen_i16_checked_add`
- `gen_i16_checked_add_unsigned`
- `gen_i16_checked_mul`
- `gen_i16_checked_sub`
- `gen_i16_checked_sub_unsigned`
- `gen_i32_checked_add`
- `gen_i32_checked_add_unsigned`
- `gen_i32_checked_sub`
- `gen_i32_checked_sub_unsigned`
- `gen_i64_checked_add`
- `gen_i64_checked_add_unsigned`
- `gen_i64_checked_sub`
- `gen_i64_checked_sub_unsigned`
- `gen_i8_checked_add`
- `gen_i8_checked_add_unsigned`
- `gen_i8_checked_div_euclid`
- `gen_i8_checked_mul`
- `gen_i8_checked_rem_euclid`
- `gen_i8_checked_sub`
- `gen_i8_checked_sub_unsigned`
- `gen_isize_checked_add`
- `gen_isize_checked_add_unsigned`
- `gen_isize_checked_sub`
- `gen_isize_checked_sub_unsigned`
- `gen_u16_checked_add`
- `gen_u16_checked_add_signed`
- `gen_u16_checked_mul`
- `gen_u16_checked_sub`
- `gen_u16_saturating_add`
- `gen_u16_saturating_mul`
- `gen_u16_saturating_sub`
- `gen_u32_checked_add`
- `gen_u32_checked_add_signed`
- `gen_u32_checked_sub`
- `gen_u32_saturating_add`
- `gen_u32_saturating_sub`
- `gen_u64_checked_add`
- `gen_u64_checked_add_signed`
- `gen_u64_checked_sub`
- `gen_u64_saturating_add`
- `gen_u64_saturating_sub`
- `gen_u8_checked_add`
- `gen_u8_checked_add_signed`
- `gen_u8_checked_mul`
- `gen_u8_checked_rem`
- `gen_u8_checked_rem_euclid`
- `gen_u8_checked_sub`
- `gen_u8_is_multiple_of`
- `gen_u8_saturating_add`
- `gen_u8_saturating_mul`
- `gen_u8_saturating_sub`
- `gen_usize_checked_add`
- `gen_usize_checked_add_signed`
- `gen_usize_checked_sub`
- `gen_usize_saturating_add`
- `gen_usize_saturating_sub`
