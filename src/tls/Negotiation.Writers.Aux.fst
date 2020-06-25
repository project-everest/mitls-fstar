module Negotiation.Writers.Aux

friend Parsers.PskBinderEntry

module LP = LowParse.Spec

let valid_pskBinderEntry_intro =
   [@inline_let] let _ = assert_norm (Parsers.PskBinderEntry.pskBinderEntry == LowParse.Spec.Bytes.parse_bounded_vlbytes_t 32 255) in
   LWP.valid_synth_parser_eq (LWP.parse_vlbytes 32ul 255ul) Parsers.PskBinderEntry.lwp_pskBinderEntry
