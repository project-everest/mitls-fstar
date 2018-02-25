module Format.ECCurveType

module B = FStar.Bytes
module L = FStar.List
module U8 = FStar.UInt8
module LP = LowParse.SLow

type byte = B.byte

unfold type is_injective (#a:Type) (#b:Type) (f:a -> b) 
  = forall x y . f x == f y ==> x == y


(* Types *)

(* 
    https://tools.ietf.org/html/rfc4492#section-5.4

    enum { explicit_prime (1), explicit_char2 (2),
           named_curve (3), reserved(248..255) } ECCurveType;
*)

noeq type ecCurveType = 
  | EXPLICIT_PRIME
  | EXPLICIT_CHAR2
  | NAMED_CURVE
  | RESERVED of (r:byte{U8.(248uy <=^ r && r <=^ 255uy)})
  | UNKNOWN of (r:byte{not U8.(248uy <=^ r && r <=^ 255uy) /\
                       not U8.(r =^ 1uy) /\
                       not U8.(r =^ 2uy) /\
                       not U8.(r =^ 3uy)})

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
  : byte
  = match c with
  | EXPLICIT_PRIME -> 0x01uy
  | EXPLICIT_CHAR2 -> 0x02uy
  | NAMED_CURVE    -> 0x03uy
  | RESERVED r     -> r
  | UNKNOWN r      -> r

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_ecCurveType_of_byte_is_injective () 
  : Lemma (is_injective ecCurveType_of_byte) 
  = ()
#reset-options


(* Parsers *)

let ecCurveType_parser_kind = LP.parse_u8_kind

let ecCurveType_parser: LP.parser ecCurveType_parser_kind ecCurveType =
  lemma_ecCurveType_of_byte_is_injective ();
  LP.parse_u8 `LP.parse_synth` ecCurveType_of_byte 

inline_for_extraction
let ecCurveType_parser32: LP.parser32 ecCurveType_parser =
  lemma_ecCurveType_of_byte_is_injective ();
  LP.parse32_synth LP.parse_u8 ecCurveType_of_byte (fun x -> ecCurveType_of_byte x) LP.parse32_u8 ()


// (* Validators? *)


// (* Serialization *) 

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_ecCurveType_of_byte_of_ecCurveType () 
  : Lemma (forall x . ecCurveType_of_byte (byte_of_ecCurveType x) == x)
  = ()
#reset-options

let ecCurveType_serializer: LP.serializer ecCurveType_parser = 
  lemma_ecCurveType_of_byte_is_injective ();
  lemma_ecCurveType_of_byte_of_ecCurveType ();
  LP.serialize_synth #ecCurveType_parser_kind #byte #ecCurveType
    LP.parse_u8 ecCurveType_of_byte LP.serialize_u8 byte_of_ecCurveType ()

inline_for_extraction
let ecCurveType_serializer32: LP.serializer32 ecCurveType_serializer = 
  lemma_ecCurveType_of_byte_is_injective ();
  lemma_ecCurveType_of_byte_of_ecCurveType ();
  LP.serialize32_synth #ecCurveType_parser_kind #byte #ecCurveType
    LP.parse_u8 ecCurveType_of_byte LP.serialize_u8 LP.serialize32_u8 byte_of_ecCurveType (fun x -> byte_of_ecCurveType x) ()

