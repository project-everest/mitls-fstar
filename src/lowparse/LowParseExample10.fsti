module LowParseExample10

module LPB = LowParse.SLow.Bytes
module LPI = LowParse.SLow.Int
module LL = LowParse.Low.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module BY = LowParse.Bytes32

(* Ideal output for something like:

struct {
  opaque msg_type[3];
  (if msg_type=abcdef then uint32 else uint16) contents;
} t;

*)

type msg_type = BY.lbytes 3

let msg_type_HelloRetryRequest' : BY.bytes = BY.bytes_of_hex "abcdef"

let msg_type_HelloRetryRequest : msg_type =
  assume (BY.length msg_type_HelloRetryRequest' == 3);
  msg_type_HelloRetryRequest'

type msg_type_other = (msg_type: msg_type { msg_type <> msg_type_HelloRetryRequest } )

noeq
type t_other = {
  msg_type: msg_type_other;
  contents: U16.t;
}

noeq
type t =
  | HelloRetryRequest of U32.t
  | Other of t_other

inline_for_extraction
let parse_t_kind : LPB.parser_kind = LPB.strong_parser_kind 5 7 (Some LPB.ParserKindMetadataTotal)

val parse_t: LPB.parser parse_t_kind t

val serialize_t: LPB.serializer parse_t

val parse32_t : LPB.parser32 parse_t

val serialize32_t : LPB.serializer32 serialize_t

val size32_t : LPB.size32 serialize_t

val validate_t : LL.validator parse_t

val jump_t : LL.jumper parse_t

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
