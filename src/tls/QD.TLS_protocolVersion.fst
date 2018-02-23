module QD.TLS_protocolVersion

module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

inline_for_extraction let protocolVersion_enum : LP.enum protocolVersion UInt16.t =
  [@inline_let] let e = [
    SSL_3p0, 768us;
    TLS_1p0, 769us;
    TLS_1p1, 770us;
    TLS_1p2, 771us;
    TLS_1p3, 772us;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (L.map fst e));
    assert_norm (L.noRepeats (L.map snd e))
  in e

inline_for_extraction let synth_protocolVersion' (x:LP.maybe_enum_key protocolVersion_enum) : Tot protocolVersion' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : UInt16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd protocolVersion_enum)) in
    Unknown_protocolVersion v

let lemma_synth_protocolVersion'_inj () : Lemma
  (forall (x1 x2: LP.maybe_enum_key protocolVersion_enum).
    synth_protocolVersion' x1 == synth_protocolVersion' x2 ==> x1 == x2) = ()

inline_for_extraction let synth_protocolVersion'_inv (x:protocolVersion') : Tot (LP.maybe_enum_key protocolVersion_enum) = 
  match x with
  | Unknown_protocolVersion y ->
    [@inline_let] let v : UInt16.t = y in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd protocolVersion_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst protocolVersion_enum)) in
    LP.Known (x1 <: LP.enum_key protocolVersion_enum)

let lemma_synth_protocolVersion'_inv () : Lemma
  (forall (x: LP.maybe_enum_key protocolVersion_enum). synth_protocolVersion'_inv (synth_protocolVersion' x) == x) = ()

let parse_maybe_protocolVersion_key : LP.parser _ (LP.maybe_enum_key protocolVersion_enum) =
  LP.parse_maybe_enum_key LP.parse_u16 protocolVersion_enum

let serialize_maybe_protocolVersion_key : LP.serializer parse_maybe_protocolVersion_key =
  LP.serialize_maybe_enum_key LP.parse_u16 LP.serialize_u16 protocolVersion_enum

let parse_protocolVersion' : LP.parser _ protocolVersion' =
  lemma_synth_protocolVersion'_inj ();
  parse_maybe_protocolVersion_key `LP.parse_synth` synth_protocolVersion'

let serialize_protocolVersion' : LP.serializer parse_protocolVersion' =
  lemma_synth_protocolVersion'_inj ();
  lemma_synth_protocolVersion'_inv ();
  LP.serialize_synth _ synth_protocolVersion' serialize_maybe_protocolVersion_key synth_protocolVersion'_inv ()

inline_for_extraction let parse32_maybe_protocolVersion_key : LP.parser32 parse_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u16 protocolVersion_enum parse_maybe_protocolVersion_key ())

inline_for_extraction let parse32_protocolVersion' : LP.parser32 parse_protocolVersion' =
  lemma_synth_protocolVersion'_inj ();
  LP.parse32_synth _ synth_protocolVersion' (fun x->synth_protocolVersion' x) parse32_maybe_protocolVersion_key ()

inline_for_extraction let serialize32_maybe_protocolVersion_key : LP.serializer32 serialize_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u16 #LP.serialize_u16 // FIXME(implicits for machine int parsers)
    LP.serialize32_u16 protocolVersion_enum serialize_maybe_protocolVersion_key ())

inline_for_extraction let serialize32_protocolVersion' : LP.serializer32 serialize_protocolVersion' =
  lemma_synth_protocolVersion'_inj ();
  lemma_synth_protocolVersion'_inv ();
  LP.serialize32_synth _ synth_protocolVersion' _ serialize32_maybe_protocolVersion_key synth_protocolVersion'_inv (fun x->synth_protocolVersion'_inv x) ()

let protocolVersion_bytes x = serialize32_protocolVersion' x <: LP.bytes32

let parse_protocolVersion' x =
  LP.parse32_total parse32_protocolVersion' v;
  match parse32_protocolVersion' x with
  | Some (v, _) -> Correct v
  | None -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let parse_protocolVersion x =
  LP.parse32_total parse32_protocolVersion' v;
  match parse32_protocolVersion' x with
  | Some (v, _) -> if v = Unknown_protocolVersion then Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "") else Correct v
  | None -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

