module Format.ECCurveType

module B = FStar.Bytes
module L = FStar.List
module U8 = FStar.UInt8
module LP = LowParse.SLow


(* Types *)

(* 
    https://tools.ietf.org/html/rfc4492#section-5.4

    enum { explicit_prime (1), explicit_char2 (2),
           named_curve (3), reserved(248..255) } ECCurveType;
*)

inline_for_extraction
let ecCurveType_of_byte (b:byte)
  : Tot ecCurveType
  = match b with
  | 0x01uy -> EXPLICIT_PRIME
  | 0x02uy -> EXPLICIT_CHAR2
  | 0x03uy -> NAMED_CURVE
  | r      -> if U8.lt 248uy r && U8.lt r 255uy then RESERVED r 
              else UNKNOWN r

inline_for_extraction
let byte_of_ecCurveType (c:ecCurveType)
  : Tot byte
  = match c with
  | EXPLICIT_PRIME -> 0x01uy
  | EXPLICIT_CHAR2 -> 0x02uy
  | NAMED_CURVE    -> 0x03uy
  | RESERVED r     -> r
  | UNKNOWN r      -> r

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics'"
let lemma_ecCurveType_of_byte_is_injective () 
  : Lemma (LP.synth_injective ecCurveType_of_byte) 
  = LP.synth_injective_intro ecCurveType_of_byte
#reset-options

(* Parsers *)

inline_for_extraction
let ecCurveType_parser_kind' = LP.parse_u8_kind

let ecCurveType_parser_kind_metadata = ecCurveType_parser_kind'.LP.parser_kind_metadata

let ecCurveType_parser =
  lemma_ecCurveType_of_byte_is_injective ();
  LP.parse_u8 `LP.parse_synth` ecCurveType_of_byte 

let ecCurveType_parser32 =
  lemma_ecCurveType_of_byte_is_injective ();
  LP.parse32_synth LP.parse_u8 ecCurveType_of_byte (fun x -> ecCurveType_of_byte x) LP.parse32_u8 ()


// (* Validators? *)


// (* Serialization *) 

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics'"
let lemma_ecCurveType_of_byte_of_ecCurveType () 
  : Lemma (LP.synth_inverse ecCurveType_of_byte byte_of_ecCurveType)
  = LP.synth_inverse_intro ecCurveType_of_byte byte_of_ecCurveType
#reset-options

let ecCurveType_serializer =
  lemma_ecCurveType_of_byte_is_injective ();
  lemma_ecCurveType_of_byte_of_ecCurveType ();
  LP.serialize_synth #ecCurveType_parser_kind #byte #ecCurveType
    LP.parse_u8 ecCurveType_of_byte LP.serialize_u8 byte_of_ecCurveType ()

let ecCurveType_serializer32 =
  lemma_ecCurveType_of_byte_is_injective ();
  lemma_ecCurveType_of_byte_of_ecCurveType ();
  LP.serialize32_synth #ecCurveType_parser_kind #byte #ecCurveType
    LP.parse_u8 ecCurveType_of_byte LP.serialize_u8 LP.serialize32_u8 byte_of_ecCurveType (fun x -> byte_of_ecCurveType x) ()

