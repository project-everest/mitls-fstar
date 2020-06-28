module Negotiation.Writers.Aux

friend Parsers.PskBinderEntry
friend Parsers.PskIdentity
friend Parsers.OfferedPsks_identities
friend Parsers.OfferedPsks_binders
friend Parsers.OfferedPsks
friend Parsers.ClientHelloExtension_CHE_pre_shared_key
friend Parsers.ExtensionType
friend Parsers.ClientHelloExtension

module LWP = LowParseWriters.Compat
module LP = LowParse.Spec

#set-options "--z3rlimit 32" // necessary due to cluttered context (too many `friend`s)

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

inline_for_extraction
noextract
let che_dsum =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  let open LWP in {
    dsum_kt = _;
    dsum_t = clientHelloExtension_sum;
    dsum_p = extensionType_repr_parser;
    dsum_s = extensionType_repr_serializer;
    dsum_pc = parse_clientHelloExtension_cases;
    dsum_sc = serialize_clientHelloExtension_cases;
    dsum_ku = _;
    dsum_pu = clientHelloExtension_CHE_default_parser;
    dsum_su = clientHelloExtension_CHE_default_serializer;
  }

inline_for_extraction
noextract
let che_enum : LWP.pparser _ _ _ (LP.serialize_maybe_enum_key _ che_dsum.LWP.dsum_s (LP.dsum_enum che_dsum.LWP.dsum_t)) =
  LWP.parse_maybe_enum
    LWP.parse_u16
    (LP.dsum_enum che_dsum.LWP.dsum_t)

#push-options "--z3rlimit 128"

let valid_synth_constr_clientHelloExtension_CHE_pre_shared_key =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind extensionType_repr_parser) clientHelloExtension_sum parse_clientHelloExtension_cases (LP.get_parser_kind clientHelloExtension_CHE_default_parser) == clientHelloExtension_parser_kind);
  lemma_synth_extensionType_inj ();
  lemma_synth_extensionType_inv ();
  assert_norm (LP.list_mem Pre_shared_key (LP.list_map fst extensionType_enum) == true);
  LWP.valid_synth_implies _ _ _ _
  (LWP.valid_synth_compose
    _ _ _ _
    (LWP.valid_synth_star_compat_r
      _ _ _ _ _
      (LWP.valid_synth_compose
        _ _ _ _
        (LWP.valid_synth_parser_eq _ _)
        _ _ _
        (LWP.valid_synth_parse_synth_recip che_enum synth_extensionType synth_extensionType_inv ())
      )
    )
    _ _ _
    (LWP.valid_synth_parse_dsum_known
      che_dsum
      _
      _
      Pre_shared_key
      _
    )
  )
  _ _

#pop-options
