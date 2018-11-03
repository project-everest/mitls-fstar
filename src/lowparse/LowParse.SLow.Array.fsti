module LowParse.SLow.Array
include LowParse.SLow.FLData
include LowParse.SLow.VLData
include LowParse.SLow.List
include LowParse.Spec.Array

module U32 = FStar.UInt32

inline_for_extraction
val parse32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t { U32.v array_byte_size32 == array_byte_size } )
  (elem_count: nat)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (parser32 (parse_array s array_byte_size elem_count))

inline_for_extraction
val serialize32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (array_byte_size: nat { array_byte_size < 4294967296 } )
  (elem_count: nat)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (serializer32 (serialize_array s array_byte_size elem_count u))

inline_for_extraction
val size32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t { U32.v array_byte_size32 == array_byte_size } )
  (elem_count: nat)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (size32 (serialize_array s array_byte_size elem_count u))

inline_for_extraction
val parse32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_min32: U32.t { U32.v array_byte_size_min32 == array_byte_size_min } )
  (array_byte_size_max: nat)
  (array_byte_size_max32: U32.t { U32.v array_byte_size_max32 == array_byte_size_max } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (parser32 (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))

inline_for_extraction
val serialize32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4 to account for the size of the length header
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (serializer32 (serialize_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))

inline_for_extraction
val size32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4 to account for the size of the length header
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
  (size_header_byte_size32: U32.t { U32.v size_header_byte_size32 == log256' array_byte_size_max } )
  (elem_byte_size32: U32.t { U32.v elem_byte_size32 == k.parser_kind_low } )
: Tot (size32 (serialize_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))
