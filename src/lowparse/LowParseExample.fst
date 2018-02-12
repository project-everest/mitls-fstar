module LowParseExample

let f (input: FStar.Bytes.bytes) : option (LowParseExample.Aux.t * FStar.UInt32.t) =
  LowParseExample.Aux.parse32_t input
