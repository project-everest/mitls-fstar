module Negotiation.Writers.Aux

friend Parsers.PskBinderEntry
friend Parsers.PskIdentity
friend Parsers.OfferedPsks_identities
friend Parsers.OfferedPsks_binders
friend Parsers.OfferedPsks
friend Parsers.ClientHelloExtension_CHE_pre_shared_key

module LWP = LowParseWriters.Compat
module LP = LowParse.Spec

let valid_pskBinderEntry_intro =
   [@inline_let] let _ = assert_norm (Parsers.PskBinderEntry.pskBinderEntry == LowParse.Spec.Bytes.parse_bounded_vlbytes_t 32 255) in
   LWP.valid_synth_parser_eq (LWP.parse_vlbytes 32ul 255ul) Parsers.PskBinderEntry.lwp_pskBinderEntry

let valid_pskBinderEntry_elim =
   [@inline_let] let _ = assert_norm (Parsers.PskBinderEntry.pskBinderEntry == LowParse.Spec.Bytes.parse_bounded_vlbytes_t 32 255) in
   LWP.valid_synth_parser_eq Parsers.PskBinderEntry.lwp_pskBinderEntry (LWP.parse_vlbytes 32ul 255ul)

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


let valid_offeredPsks_binders_intro =
  let open Parsers.OfferedPsks_binders in
  LWP.valid_synth_implies _ _ _ _
    (LWP.valid_synth_compose
      _ _ _ _
      (LWP.valid_synth_parse_synth (LWP.parse_vllist Parsers.PskBinderEntry.lwp_pskBinderEntry 33ul 65535ul) synth_offeredPsks_binders synth_offeredPsks_binders_recip ())
      _ _ _
      (LWP.valid_synth_parser_eq _ _)
    )
    _ _

let valid_offeredPsks_binders_elim =
  let open Parsers.OfferedPsks_binders in
  LWP.valid_synth_implies _ _ _ _
    (LWP.valid_synth_compose
      _ _ _ _
      (LWP.valid_synth_parser_eq _ _)
      _ _ _
      (LWP.valid_synth_parse_synth_recip (LWP.parse_vllist Parsers.PskBinderEntry.lwp_pskBinderEntry 33ul 65535ul) synth_offeredPsks_binders synth_offeredPsks_binders_recip ())
    )
    _ _

let valid_offeredPsks_identities_intro =
  let open Parsers.OfferedPsks_identities in
  LWP.valid_synth_implies _ _ _ _
    (LWP.valid_synth_compose
      _ _ _ _
      (LWP.valid_synth_parse_synth (LWP.parse_vllist Parsers.PskIdentity.lwp_pskIdentity 7ul 65535ul) synth_offeredPsks_identities synth_offeredPsks_identities_recip ())
      _ _ _
      (LWP.valid_synth_parser_eq _ _)
    )
    _ _

let valid_offeredPsks_identities_elim =
  let open Parsers.OfferedPsks_identities in
  LWP.valid_synth_implies _ _ _ _
    (LWP.valid_synth_compose
      _ _ _ _
      (LWP.valid_synth_parser_eq _ _)
      _ _ _
      (LWP.valid_synth_parse_synth_recip (LWP.parse_vllist Parsers.PskIdentity.lwp_pskIdentity 7ul 65535ul) synth_offeredPsks_identities synth_offeredPsks_identities_recip ())
    )
    _ _

let valid_offeredPsks_intro =
  let open Parsers.OfferedPsks in
  LWP.valid_synth_implies _ _ _ _
    (LWP.valid_synth_compose
      _ _ _ _
      (LWP.valid_synth_parse_synth (lwp_offeredPsks_identities `LWP.star` lwp_offeredPsks_binders) synth_offeredPsks synth_offeredPsks_recip ())
      _ _ _
      (LWP.valid_synth_parser_eq _ _)
    )
  _ _

let valid_clientHelloExtension_CHE_pre_shared_key_intro =
  let open Parsers.ClientHelloExtension_CHE_pre_shared_key in
  Classical.forall_intro Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_bytesize_eq;
  LWP.valid_synth_implies _ _ _ _
    (LWP.valid_synth_compose
      _ _ _ _
      (LWP.valid_synth_parse_synth (LWP.parse_vldata Parsers.PreSharedKeyClientExtension.lwp_preSharedKeyClientExtension 0ul 65535ul) synth_clientHelloExtension_CHE_pre_shared_key synth_clientHelloExtension_CHE_pre_shared_key_recip ())
      _ _ _
      (LWP.valid_synth_parser_eq _ _)
    )
  _ _
