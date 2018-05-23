module LowParseExample3.Aux
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = FStar.Buffer
module M = FStar.Modifies
module HST = FStar.HyperStack.ST

include LowParse.Low

type t = {
  a: U16.t;
  b: U32.t;
  c: U16.t;
}

let synth_t ((x, y), z) = {a=x; b=y; c=z}

let parse_t : parser _ t =
  (parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16)
  `parse_synth` synth_t

inline_for_extraction
let validate32_t : validator32 parse_t =
  validate32_synth
  (validate32_u16 `validate32_nondep_then` validate32_u32 `validate32_nondep_then` validate32_u16)
  synth_t
  ()

inline_for_extraction
let access_a : accessor parse_t parse_u16 (fun x y -> y == x.a) =
  accessor_weaken (
    accessor_synth
      ((validate_nochk32_u16 `validate_nochk32_nondep_then` validate_nochk32_u32) `validate_nochk32_nondep_then` validate_nochk32_u16)
      synth_t
      ()
    `accessor_compose`
    nondep_then_fst (validate_nochk32_u16 `validate_nochk32_nondep_then` validate_nochk32_u32) parse_u16
    `accessor_compose`
    nondep_then_fst validate_nochk32_u16 parse_u32
  )
  (fun x y -> y == x.a) ()

inline_for_extraction
let access_b : accessor parse_t parse_u32 (fun x y -> y == x.b) =
  accessor_weaken (
    accessor_synth
      ((validate_nochk32_u16 `validate_nochk32_nondep_then` validate_nochk32_u32) `validate_nochk32_nondep_then` validate_nochk32_u16)
      synth_t
      ()
    `accessor_compose`
    nondep_then_fst (validate_nochk32_u16 `validate_nochk32_nondep_then` validate_nochk32_u32) parse_u16
    `accessor_compose`
    nondep_then_snd validate_nochk32_u16 validate_nochk32_u32
  )
  (fun x y -> y == x.b) ()

inline_for_extraction
let access_c : accessor parse_t parse_u16 (fun x y -> y == x.c) =
  accessor_weaken (
    accessor_synth
      ((validate_nochk32_u16 `validate_nochk32_nondep_then` validate_nochk32_u32) `validate_nochk32_nondep_then` validate_nochk32_u16)
      synth_t
      ()
    `accessor_compose`
    nondep_then_snd (validate_nochk32_u16 `validate_nochk32_nondep_then` validate_nochk32_u32) validate_nochk32_u16
  )
  (fun x y -> y == x.c) ()
