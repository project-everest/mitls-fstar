module Format.ECPointFormat

module U8 = FStar.UInt8

(*
    https://tools.ietf.org/html/rfc4492#section-5.1.2

    enum { uncompressed (0), ansiX962_compressed_prime (1),
           ansiX962_compressed_char2 (2), reserved (248..255)
    } ECPointFormat;
*)

type ecPointFormat =
  | UNCOMPRESSED             
  | ANSIX962_COMPRESSED_PRIME
  | ANSIX962_COMPRESSED_CHAR2
  | RESERVED of u:U8.t{U8.(248uy <=^ u && u <=^ 255uy)}

let ecPointFormat_of_u8 (x:U8.t): Tot ecPointFormat =
  match x with
  | 1uy -> UNCOMPRESSED
  | 2uy -> ANSIX962_COMPRESSED_PRIME
  | 3uy -> ANSIX962_COMPRESSED_CHAR2
  | u   -> RESERVED u

let u8_of_ecPointFormat (x:ecPointFormat): Tot U8.t =
  match x with
  | UNCOMPRESSED              -> 1uy
  | ANSIX962_COMPRESSED_PRIME -> 2uy
  | ANSIX962_COMPRESSED_CHAR2 -> 3uy
  | RESERVED                u -> u

// cwinter: do we need this for TLS 1.2?
