module Negotiation.Writers.Aux2

friend Parsers.ExtensionType
friend Parsers.ClientHelloExtension

module LWP = LowParseWriters.Compat
module LP = LowParse.Spec

#set-options "--z3rlimit 32" // necessary due to cluttered context (too many `friend`s)


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
