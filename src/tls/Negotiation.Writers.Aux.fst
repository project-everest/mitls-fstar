module Negotiation.Writers.Aux

friend Parsers.PskBinderEntry
friend Parsers.PskIdentity

module LWP = LowParseWriters.Compat
module LP = LowParse.Spec

let valid_pskBinderEntry_intro =
   [@inline_let] let _ = assert_norm (Parsers.PskBinderEntry.pskBinderEntry == LowParse.Spec.Bytes.parse_bounded_vlbytes_t 32 255) in
   LWP.valid_synth_parser_eq (LWP.parse_vlbytes 32ul 255ul) Parsers.PskBinderEntry.lwp_pskBinderEntry

let valid_pskIdentity_intro =
  let open Parsers.PskIdentity in
  assert_norm (pskIdentity' == LP.get_parser_type pskIdentity'_parser);
  assert_norm (pskIdentity_parser_kind == pskIdentity'_parser_kind);
  synth_pskIdentity_injective ();
  synth_pskIdentity_inverse ();
  LWP.valid_synth_implies _ _ _ _
  (LWP.valid_synth_compose
    _ _ _ _
    (LWP.valid_synth_parse_synth (lwp_pskIdentity_identity `LWP.star` LWP.parse_u32) synth_pskIdentity synth_pskIdentity_recip ())
    _ _ _
    (LWP.valid_synth_parser_eq (LWP.parse_synth (lwp_pskIdentity_identity `LWP.star` LWP.parse_u32) synth_pskIdentity synth_pskIdentity_recip) lwp_pskIdentity)
  )
  _ _
