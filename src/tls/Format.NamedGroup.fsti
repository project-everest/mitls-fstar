module Format.NamedGroup
include Format.AutoGen_namedGroup
// module U16 = FStar.UInt16 
// module U32 = FStar.UInt32
// module L = FStar.List.Tot
// module LP = LowParse.SLow.Base
// module B32 = FStar.Bytes

// (* Types *)

// (* 
//    https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#negotiated-groups 

//    enum {

//        /* Elliptic Curve Groups (ECDHE) */
//        secp256r1(0x0017), secp384r1(0x0018), secp521r1(0x0019),
//        x25519(0x001D), x448(0x001E),

//        /* Finite Field Groups (DHE) */
//        ffdhe2048(0x0100), ffdhe3072(0x0101), ffdhe4096(0x0102),
//        ffdhe6144(0x0103), ffdhe8192(0x0104),

//        /* Reserved Code Points */
//        ffdhe_private_use(0x01FC..0x01FF),
//        ecdhe_private_use(0xFE00..0xFEFF),
//        (0xFFFF)
//    } NamedGroup;

// *)
 
// type namedGroup =
//   (* Elliptic Curve Groups (ECDHE) *)
//   | SECP256R1
//   | SECP384R1
//   | SECP521R1
//   | X25519
//   | X448

//   (* Finite Field Groups (DHE) *)
//   | FFDHE2048
//   | FFDHE3072
//   | FFDHE4096
//   | FFDHE6144
//   | FFDHE8192

//   (* Reserved Code Points *)
//   | FFDHE_PRIVATE_USE of (u:U16.t{U16.(0x01FCus <=^ u && u <=^ 0x01FFus)})
//   | ECDHE_PRIVATE_USE of (u:U16.t{U16.(0xFE00us <=^ u && u <=^ 0xFEFFus)})

//   | UNKNOWN of (u:U16.t{
//       not (L.mem u [ 0x0017us; 0x0018us; 0x0019us; 0x001Dus; 
//                      0x001Eus; 0x0100us; 0x0101us; 0x0102us; 0x0103us; 0x0104us]) /\ 
//       not U16.(0x01FCus <=^ u && u <=^ 0x01FFus) /\
//       not U16.(0xFE00us <=^ u && u <=^ 0xFEFFus)})

// let bytesize = 2


// (* Parsers *)

// inline_for_extraction
// val namedGroup_parser_kind_metadata: LP.parser_kind_metadata_t

// inline_for_extraction
// let namedGroup_parser_kind =
//   LP.strong_parser_kind 2 2 namedGroup_parser_kind_metadata

// val namedGroup_parser: LP.parser namedGroup_parser_kind namedGroup

// inline_for_extraction
// val namedGroup_parser32: LP.parser32 namedGroup_parser


// (* Serialization *) 

// val namedGroup_serializer: LP.serializer namedGroup_parser

// inline_for_extraction
// val namedGroup_serializer32: LP.serializer32 namedGroup_serializer
