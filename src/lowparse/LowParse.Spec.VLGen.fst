module LowParse.Spec.VLGen
include LowParse.Spec.Combinators
include LowParse.Spec.AllIntegers
include LowParse.Spec.FLData

(* TODO: this module should deprecate and replace LowParse.Spec.VLData *)

module U32 = FStar.UInt32
module Seq = FStar.Seq

let tag_of_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
: GTot (bounded_int32 min max)
= U32.uint_to_t (Seq.length (serialize s x))

inline_for_extraction
let synth_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: bounded_int32 min max)
  (x: parse_fldata_strong_t s (U32.v sz))
: Tot (refine_with_tag (tag_of_bounded_vlgen_payload min max s) sz)
= x

inline_for_extraction
let parse_bounded_vlgen_payload_kind
  (min: nat)
  (max: nat { min <= max } )
  (k: parser_kind)
: Tot parser_kind
= [@inline_let]
  let kmin = k.parser_kind_low in
  [@inline_let]
  let min' = if kmin > min then kmin else min in
  [@inline_let]
  let max' = match k.parser_kind_high with
  | None -> max
  | Some kmax -> if kmax < max then kmax else max
  in
  [@inline_let]
  let max' = if max' < min' then min' else max' in
  strong_parser_kind min' max' (
    match k.parser_kind_metadata with
    | Some ParserKindMetadataFail -> Some ParserKindMetadataFail
    | _ -> None
  )

let parse_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: bounded_int32 min max)
: Tot (parser (parse_bounded_vlgen_payload_kind min max k) (refine_with_tag (tag_of_bounded_vlgen_payload min max s) sz))
= let bounds_off =
    k.parser_kind_low > U32.v sz || (
    match k.parser_kind_high with
    | None -> false
    | Some kmax -> kmax < U32.v sz
  )
  in
  if bounds_off
  then fail_parser (parse_bounded_vlgen_payload_kind min max k) (refine_with_tag (tag_of_bounded_vlgen_payload min max s) sz)
  else
    weaken (parse_bounded_vlgen_payload_kind min max k)
      (parse_fldata_strong s (U32.v sz)
      `parse_synth`
      synth_bounded_vlgen_payload min max s sz)

inline_for_extraction
let parse_bounded_vlgen_kind
  (sk: parser_kind)
  (min: nat)
  (max: nat { min <= max } )
  (k: parser_kind)
= and_then_kind sk (parse_bounded_vlgen_payload_kind min max k)

let parse_bounded_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 min max))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (parser (parse_bounded_vlgen_kind sk min max k) (parse_bounded_vldata_strong_t min max s))
= parse_tagged_union
    pk
    (tag_of_bounded_vlgen_payload min max s)
    (parse_bounded_vlgen_payload min max s)

inline_for_extraction
let synth_vlgen
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
: Tot t
= x

let parse_vlgen_precond
  (min: nat)
  (max: nat { min <= max } )
  (k: parser_kind)
: GTot bool
= match k.parser_kind_high with
  | None -> false
  | Some kmax -> min <= k.parser_kind_low && kmax <= max

let parse_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 min max))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k })
: Tot (parser (parse_bounded_vlgen_kind sk min max k) t)
= parse_bounded_vlgen min max pk s
  `parse_synth`
  synth_vlgen min max s

inline_for_extraction
let synth_bounded_vlgen_payload_recip
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: bounded_int32 min max)
  (x: refine_with_tag (tag_of_bounded_vlgen_payload min max s) sz)
: Tot (parse_fldata_strong_t s (U32.v sz))
= x

let serialize_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: bounded_int32 min max)
: Tot (serializer (parse_bounded_vlgen_payload min max s sz))
= let bounds_off =
    k.parser_kind_low > U32.v sz || (
    match k.parser_kind_high with
    | None -> false
    | Some kmax -> kmax < U32.v sz
  )
  in
  if bounds_off
  then fail_serializer (parse_bounded_vlgen_payload_kind min max k) (refine_with_tag (tag_of_bounded_vlgen_payload min max s) sz) (fun _ -> ())
  else
    serialize_weaken (parse_bounded_vlgen_payload_kind min max k)
      (serialize_synth
        (parse_fldata_strong s (U32.v sz))
        (synth_bounded_vlgen_payload min max s sz)
        (serialize_fldata_strong s (U32.v sz))
        (synth_bounded_vlgen_payload_recip min max s sz)
        ()
      )

let serialize_bounded_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 min max))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (serializer (parse_bounded_vlgen min max pk s))
= serialize_tagged_union
    ssk
    (tag_of_bounded_vlgen_payload min max s)
    (serialize_bounded_vlgen_payload min max s)

inline_for_extraction
let synth_vlgen_recip
  (min: nat)
  (max: nat { min <= max } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k } )
  (x: t)
: Tot (parse_bounded_vldata_strong_t min max s)
= [@inline_let] let _ =
    let sl = Seq.length (serialize s x) in
    assert (min <= sl /\ sl <= max)
  in
  x

let serialize_vlgen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 min max))
  (ssk: serializer pk { sk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k })
: Tot (serializer (parse_vlgen min max pk s))
= serialize_synth
    (parse_bounded_vlgen min max pk s)
    (synth_vlgen min max s)
    (serialize_bounded_vlgen min max ssk s)
    (synth_vlgen_recip min max s)
    ()
