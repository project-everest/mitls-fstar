module Crypto.Util.IntCast
module I = Lib.IntTypes
module U8 = FStar.UInt8
module Seq = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack

friend Lib.IntTypes

let to_uint8 x = x

let to_seq_uint8 x = x

let to_seq_uint8_correct x i = ()

let to_sec8 x = x

let to_seq_sec8 x = x

let to_seq_sec8_correct x i = ()

let to_buf_sec8 x = x

let as_seq_to_buf_sec8 x h = ()

let live_to_buf_sec8 x h = ()

let gsub_to_buf_sec8 x off len = ()

let loc_buffer_to_buf_sec8 x = ()

let seq_sec8_has_eq _ = ()
