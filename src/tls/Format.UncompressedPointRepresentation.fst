module Format.UncompressedPointRepresentation

open Format.Constants

module B = FStar.Bytes
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module LP = LowParse.SLow


(* Types *)

(*
    https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.8.2
    
    struct {
        uint8 legacy_form = 4;
        opaque X[coordinate_length];
        opaque Y[coordinate_length];
    } UncompressedPointRepresentation;
*)

type uncompressedPointRepresentation (coordinate_length:nat) = {
    legacy_form : l:B.byte{l = 4uy};
    x           : B.lbytes coordinate_length;
    y           : B.lbytes coordinate_length
}

private 
type lbytes_pair (coordinate_length:nat) = (B.lbytes coordinate_length * B.lbytes coordinate_length)


(* Parsers *)

private
let lbytes_pair_parser_kind (coordinate_length:nat)
  : LP.parser_kind
  = LP.and_then_kind 
      (LP.total_constant_size_parser_kind coordinate_length) 
      (LP.total_constant_size_parser_kind coordinate_length)

let lbytes_pair_parser (coordinate_length:nat)
  : LP.parser (lbytes_pair_parser_kind coordinate_length) (lbytes_pair coordinate_length)
  = LP.nondep_then
      (LP.parse_flbytes coordinate_length)
      (LP.parse_flbytes coordinate_length)

private
inline_for_extraction
let lbytes_pair_parser32 (coordinate_length:nat)
  : LP.parser32 (lbytes_pair_parser coordinate_length) 
  = LP.parse32_nondep_then
      (LP.parse32_flbytes coordinate_length (U32.uint_to_t coordinate_length))
      (LP.parse32_flbytes coordinate_length (U32.uint_to_t coordinate_length))


let uncompressedPointRepresentation_parser_kind (coordinate_length:nat) 
  = LP.and_then_kind
      constantByte_parser_kind
      (lbytes_pair_parser_kind coordinate_length)

private
inline_for_extraction
let ucp_of_uv (#n:nat) (p:(B.lbytes n) * (B.lbytes n))
  : uncompressedPointRepresentation n
  = { legacy_form = 4uy; x = (fst p); y = (snd p) }

private
inline_for_extraction
let uv_of_ucp (#n:nat) (x:uncompressedPointRepresentation n)
  : Tot (B.byte * (B.lbytes n * B.lbytes n))
  = (4uy, (x.x, x.y))

let uncompressedPointRepresentation_parser (coordinate_length:nat)
  : LP.parser (uncompressedPointRepresentation_parser_kind coordinate_length) (uncompressedPointRepresentation coordinate_length) 
  = LP.parse_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      (fun (c, uv) -> ucp_of_uv uv)

inline_for_extraction
let uncompressedPointRepresentation_parser32 (coordinate_length:nat)
  : LP.parser32 (uncompressedPointRepresentation_parser coordinate_length)
  = LP.parse32_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      (fun (c, uv) -> ucp_of_uv uv)
      (fun (c, uv) -> ucp_of_uv uv)
      (LP.parse32_nondep_then (constantByte_parser32 4uy) (lbytes_pair_parser32 coordinate_length))
      ()

(* Serializers *)

private
let lbytes_pair_serializer (coordinate_length:nat)
  : LP.serializer (lbytes_pair_parser coordinate_length) 
  = let p = LP.parse_flbytes coordinate_length in
    let s = LP.serialize_flbytes coordinate_length in
    LP.serialize_nondep_then p s () p s

private
inline_for_extraction
let lbytes_pair_serializer32 (coordinate_length:nat)
  : LP.serializer32 (lbytes_pair_serializer coordinate_length) 
  = LP.serialize32_nondep_then
      (LP.serialize32_flbytes coordinate_length) ()
      (LP.serialize32_flbytes coordinate_length) ()

let uncompressedPointRepresentation_serializer (coordinate_length:nat) 
  : LP.serializer (uncompressedPointRepresentation_parser coordinate_length)
  = LP.serialize_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      (fun (c, uv) -> ucp_of_uv uv)
      (LP.serialize_nondep_then 
        (constantByte_parser 4uy)
        (constantByte_serializer 4uy) 
        ()
        (lbytes_pair_parser coordinate_length)
        (lbytes_pair_serializer coordinate_length))
      (fun ucp -> (ucp.legacy_form, (ucp.x, ucp.y)))
      ()

inline_for_extraction
let uncompressedPointRepresentation_serializer32 (coordinate_length:nat) 
  : LP.serializer32 (uncompressedPointRepresentation_serializer coordinate_length)
  = LP.serialize32_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      (fun (c, uv) -> ucp_of_uv uv)
      (LP.serialize_nondep_then 
        (constantByte_parser 4uy)
        (constantByte_serializer 4uy) 
        ()
        (lbytes_pair_parser coordinate_length)
        (lbytes_pair_serializer coordinate_length))
      (LP.serialize32_nondep_then 
        (constantByte_serializer32 4uy) ()
        (lbytes_pair_serializer32 coordinate_length) ())
      uv_of_ucp
      uv_of_ucp
      ()
