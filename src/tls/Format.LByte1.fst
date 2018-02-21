module Format.LBytes1

module B = FStar.Bytes
module LP = LowParse.SLow

unfold type is_injective (#a:Type) (#b:Type) (f:a -> b) 
  = forall x y . f x == f y ==> x == y


(* 
   Frequently used 

   opaque x<1..2^8-1> 
*)


(* Types *)

let is_lbytes_1 (b:bytes) = 0 < B.length b && B.length b < 256

type lbytes_1 = b:bytes{is_lbytes_1 b}


(* Parsers *)

inline_for_extraction 
let lbytes_1_of_bytes (b:bytes{is_lbytes_1 b}): Tot lbytes_1 = b

inline_for_extraction
let bytes_of_lbytes_1 (p:lbytes_1): Tot lbytes_1 = p

let lemma_lbytes_1_of_bytes_is_injective () 
  : Lemma (is_injective lbytes_1_of_bytes) 
  = ()

let lbytes_1_parser_kind = LP.parse_bounded_vldata_kind 1 255

let lbytes_1_parser
  : LP.parser lbytes_1_parser_kind lbytes_1 
  = lemma_lbytes_1_of_bytes_is_injective ();
    LP.parse_bounded_vldata 1 255 LP.parse_u8

inline_for_extraction 
let lbytes_1_parser32
  : LP.parser32 lbytes_1_parser 
  = lemma_lbytes_1_of_bytes_is_injective ();
    LP.parse32_bounded_vldata 1 1ul 255 255ul LP.parse32_u8


(* Serialization *)

let lemma_lbytes_1_of_bytes_of_lbytes_1 () 
  : Lemma (forall x . lbytes_1_of_bytes (bytes_of_lbytes_1 x) == x)
  = ()

let lbytes_1_serializer
  : LP.serializer lbytes_1_parser 
  = lemma_lbytes_1_of_bytes_is_injective ();
    lemma_lbytes_1_of_bytes_of_lbytes_1 ();
    LP.serialize_bounded_vldata_strong 1 255 LP.serialize_u8

inline_for_extraction 
let lbytes_1_serializer32
  : LP.serializer32 lbytes_1_serializer 
  = lemma_lbytes_1_of_bytes_is_injective ();
    lemma_lbytes_1_of_bytes_of_lbytes_1 ();
    LP.serialize32_bounded_vldata_strong 1 255 LP.serialize32_u8
