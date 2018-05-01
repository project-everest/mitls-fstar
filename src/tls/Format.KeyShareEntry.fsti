module Format.KeyShareEntry

open Format.NamedGroup

module B = FStar.Bytes
module LP = LowParse.SLow.Base
module U32 = FStar.UInt32

(* Types *)

(* 
   https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.8

   struct {
       NamedGroup group;
       opaque key_exchange<1..2^16-1>;
   } KeyShareEntry;


   https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#ffdhe-param
   
   Diffie-Hellman [DH] parameters for both clients and servers are encoded in the 
   opaque key_exchange field of a KeyShareEntry in a KeyShare structure. The opaque
   value contains the Diffie-Hellman public value (Y = g^X mod p) for the specified
   group (see [RFC7919] for group definitions) encoded as a big-endian integer
   and padded to the left with zeros to the size of p in bytes.


   https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#ecdhe-param
   
   ECDHE parameters for both clients and servers are encoded in the the opaque 
   key_exchange field of a KeyShareEntry in a KeyShare structure. 
   For secp256r1, secp384r1 and secp521r1, the contents are the serialized value
   of the following struct:
   
     struct {
         uint8 legacy_form = 4;
         opaque X[coordinate_length];
         opaque Y[coordinate_length];
     } UncompressedPointRepresentation;

*)

type keyShareEntry = {
  group        : namedGroup; 
  key_exchange : (bs:B.bytes{1 <= B.length bs && B.length bs <= 65535});
}

inline_for_extraction
val keyShareEntry_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction
let keyShareEntry_parser_kind =
  LP.strong_parser_kind 5 65539 keyShareEntry_parser_kind_metadata

val keyShareEntry_parser: LP.parser keyShareEntry_parser_kind keyShareEntry

inline_for_extraction
val keyShareEntry_parser32: LP.parser32 keyShareEntry_parser

val keyShareEntry_serializer: LP.serializer keyShareEntry_parser

inline_for_extraction
val keyShareEntry_serializer32: LP.serializer32 keyShareEntry_serializer
