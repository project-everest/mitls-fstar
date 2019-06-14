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


(* Parsers *)

inline_for_extraction 
let lbytes_1_of_bytes (b: LP.parse_bounded_vlbytes_t 1 255): Tot lbytes_1 = b

inline_for_extraction
let bytes_of_lbytes_1 (p:lbytes_1): Tot (LP.parse_bounded_vlbytes_t 1 255) = p

let lemma_lbytes_1_of_bytes_is_injective () 
  : Lemma (is_injective lbytes_1_of_bytes) 
  = ()

let lbytes_1_parser_kind' = LP.parse_bounded_vldata_kind 1 255

let lbytes_1_parser_kind_metadata = lbytes_1_parser_kind'.LP.parser_kind_metadata

let lbytes_1_parser
  = assert_norm (lbytes_1_parser_kind' == lbytes_1_parser_kind);
    lemma_lbytes_1_of_bytes_is_injective ();
    LP.parse_bounded_vlbytes 1 255 `LP.parse_synth` lbytes_1_of_bytes

let lbytes_1_parser32
  = assert_norm (lbytes_1_parser_kind' == lbytes_1_parser_kind);
    lemma_lbytes_1_of_bytes_is_injective ();
    LP.parse32_synth
      _
      lbytes_1_of_bytes
      (fun x -> lbytes_1_of_bytes x)
      (LP.parse32_bounded_vlbytes 1 1ul 255 255ul)
      ()


(* Serialization *)

let lemma_lbytes_1_of_bytes_of_lbytes_1 () 
  : Lemma (forall x . lbytes_1_of_bytes (bytes_of_lbytes_1 x) == x)
  = ()

let lbytes_1_serializer
  = lemma_lbytes_1_of_bytes_is_injective ();
    lemma_lbytes_1_of_bytes_of_lbytes_1 ();
    LP.serialize_synth
      _
      lbytes_1_of_bytes
      (LP.serialize_bounded_vlbytes 1 255)
      bytes_of_lbytes_1
      ()

let lbytes_1_serializer32
  = lemma_lbytes_1_of_bytes_is_injective ();
    lemma_lbytes_1_of_bytes_of_lbytes_1 ();
    LP.serialize32_synth
      _
      lbytes_1_of_bytes
      _
      (LP.serialize32_bounded_vlbytes 1 255)
      bytes_of_lbytes_1
      (fun x -> bytes_of_lbytes_1 x)
      ()
