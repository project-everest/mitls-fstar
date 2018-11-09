module LowParse.Low.FLData
include LowParse.Low.Combinators
include LowParse.Spec.FLData

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack

inline_for_extraction
let validate_fldata
  [| validator_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator (parse_fldata p sz))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_fldata p sz) h input pos in
  if (input.len `U32.sub` pos) `U32.lt` sz32
  then validator_max_length `U32.add` 1ul
  else
    let base' = B.sub input.base pos sz32 in
    [@inline_let] let input' = { base = base'; len = sz32; } in
    [@inline_let] let _ = valid_facts p h input' 0ul in
    let pos' = v input' 0ul in
    if validator_max_length `U32.lt` pos'
    then pos' // error propagation
    else if pos' <> sz32
    then validator_max_length `U32.add` 1ul // TODO: more error control
    else pos `U32.add` pos'

inline_for_extraction
let validate_fldata_strong
  [| validator_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator (parse_fldata_strong s sz))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_fldata p sz) h input pos in
  [@inline_let] let _ = valid_facts (parse_fldata_strong s sz) h input pos in
  validate_fldata v sz sz32 input pos

inline_for_extraction
let jump_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (jumper (parse_fldata p sz))
= jump_constant_size (parse_fldata p sz) sz32 ()

inline_for_extraction
let jump_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (jumper (parse_fldata_strong s sz))
= jump_constant_size (parse_fldata_strong s sz) sz32 ()

(*
inline_for_extraction
let accessor_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (accessor (parse_fldata p sz) p (fun x y -> x == y))
= fun x ->
  let h = HST.get () in // TODO: WHY WHY WHY is this necessary?
  B.sub x 0ul sz32

inline_for_extraction
let accessor_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (accessor (parse_fldata_strong s sz) p (fun x y -> x == y))
= fun x -> accessor_fldata p sz sz32 x

