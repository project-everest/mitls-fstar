module LowParse.SLow.Array
include LowParse.SLow.FLData
include LowParse.SLow.List
include LowParse.Spec.Array

module U32 = FStar.UInt32

#set-options "--z3rlimit 32"

inline_for_extraction
let parse32_array'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t { U32.v array_byte_size32 == array_byte_size } )
  (precond: unit { array_type_of_parser_kind_precond p array_byte_size == true } )
: Tot (parser32 (parse_array' p array_byte_size precond))
= assert_norm (array_type_of_parser p array_byte_size == (x: list t { array_pred (array_byte_size / k.parser_kind_low) x}));
  coerce_parser32
    (array_type_of_parser p array_byte_size)
    (parse32_strengthen
          #_
          #_
          #(parse_fldata (parse_list p) array_byte_size)
          (parse32_fldata (parse32_list p32) array_byte_size array_byte_size32)
          (array_pred (array_byte_size / k.parser_kind_low))
          (parse_array_correct p array_byte_size precond)
    )
    ()

inline_for_extraction
let parse32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t { U32.v array_byte_size32 == array_byte_size } )
  (precond: unit { array_type_of_parser_kind_precond p array_byte_size == true } )
: Tot (parser32 (parse_array p array_byte_size precond))
= make_parser32
    (parse_array p array_byte_size precond)
    (fun (input: bytes32) ->
      let res = // : option ((l: list t { array_pred (array_byte_size / k.parser_kind_low) l } ) * U32.t) =
        parse32_array' p32 array_byte_size array_byte_size32 precond
          input
      in
      match res with
      | None -> None
      | Some (x, consumed) ->
        let x1 : list t = x in
        Some ((x1 <: array_type_of_parser p array_byte_size), consumed)
    )

inline_for_extraction
let serialize32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (array_byte_size: nat { array_byte_size < 4294967296 } )
  (precond: unit { array_type_of_parser_kind_precond p array_byte_size == true } )
  (lprecond: unit { serialize_list_precond k } )
: Tot (serializer32 (serialize_array s array_byte_size precond lprecond))
= fun (input: array_type_of_parser p array_byte_size) ->
  serialize32_fldata_strong (partial_serialize32_list _ _ s32 lprecond) array_byte_size (synth_array_recip s array_byte_size precond lprecond input)
  <: (res: bytes32 { serializer32_correct (serialize_array s array_byte_size precond lprecond) input res })

include LowParse.SLow.VLData

inline_for_extraction
let parse32_vlarray
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (array_byte_size_min: nat)
  (array_byte_size_min32: U32.t { U32.v array_byte_size_min32 == array_byte_size_min } )
  (array_byte_size_max: nat)
  (array_byte_size_max32: U32.t { U32.v array_byte_size_max32 == array_byte_size_max } )  
  (precond: unit {vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max == true})
: Tot (parser32 (parse_vlarray p array_byte_size_min array_byte_size_max precond))
= let elem_byte_size : pos = k.parser_kind_low in
  parse32_strengthen
    (parse32_bounded_vldata
      array_byte_size_min
      array_byte_size_min32
      array_byte_size_max
      array_byte_size_max32
      (parse32_list p32)
    )
    (vlarray_pred (array_byte_size_min / elem_byte_size) (array_byte_size_max / elem_byte_size))
    (parse_vlarray_correct p array_byte_size_min array_byte_size_max precond)

assume
val serialize32_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (array_byte_size_min array_byte_size_max: nat)
  (precond: unit {vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max == true})
  (lprecond: unit { serialize_list_precond k } )
: Tot (serializer32 (serialize_bounded_vldata_strong min max s))
