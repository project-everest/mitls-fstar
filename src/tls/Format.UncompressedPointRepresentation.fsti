module Format.UncompressedPointRepresentation

module B = FStar.Bytes
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base

(* Types *)

(*
    https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.8.2

    struct {
        uint8 legacy_form = 4;
        opaque X[coordinate_length];
        opaque Y[coordinate_length];
    } UncompressedPointRepresentation;
*)

type coordinate_length_type = (r:U32.t{UInt.fits (U32.v r) 8}) // cwinter: assumption, not clearly specified by RFC.

type uncompressedPointRepresentation (coordinate_length:coordinate_length_type) = {
    legacy_form : l:B.byte{l = 4uy};
    x           : B.lbytes32 coordinate_length;
    y           : B.lbytes32 coordinate_length;
}

inline_for_extraction
val uncompressedPointRepresentation_parser_kind (coordinate_length:coordinate_length_type): LP.parser_kind

val uncompressedPointRepresentation_parser (coordinate_length:coordinate_length_type)
  : LP.parser (uncompressedPointRepresentation_parser_kind coordinate_length) (uncompressedPointRepresentation coordinate_length) 

inline_for_extraction
val uncompressedPointRepresentation_parser32 (coordinate_length:coordinate_length_type) 
  : LP.parser32 (uncompressedPointRepresentation_parser coordinate_length)

val uncompressedPointRepresentation_serializer (coordinate_length:coordinate_length_type) 
  : LP.serializer (uncompressedPointRepresentation_parser coordinate_length)

inline_for_extraction
val uncompressedPointRepresentation_serializer32 (coordinate_length:coordinate_length_type) 
  : LP.serializer32 (uncompressedPointRepresentation_serializer coordinate_length)
