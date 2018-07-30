module LowParseExample6.Aux

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot

type cases : eqtype u#0 =
  | Case_A
  | Case_B

inline_for_extraction
let case_enum : LP.enum cases U8.t =
  [@inline_let]
  let e : list (cases * U8.t) = [
    Case_A, 18uy;
    Case_B, 42uy;
  ]
  in
  [@inline_let]
  let _ : squash (L.noRepeats (LP.list_map fst e) /\ L.noRepeats (LP.list_map snd e)) =
    assert_norm (L.noRepeats (LP.list_map fst e));
    assert_norm (L.noRepeats (LP.list_map snd e))
  in
  e

noeq
type t =
  | A of (U8.t * U8.t)
  | B of (x: U16.t { U16.v x > 0 } )
  | C : LP.unknown_enum_repr case_enum -> U16.t -> t

inline_for_extraction
let cases_of_t
  (x: t)
: Tot (LP.maybe_enum_key case_enum)
= match x with
  | A _ -> LP.Known Case_A
  | B _ -> LP.Known Case_B
  | C x _ -> LP.Unknown x

inline_for_extraction
let t_sum
= LP.make_dsum case_enum cases_of_t

inline_for_extraction
let synth_case_A (z: (U8.t * U8.t)) : Tot (LP.dsum_cases t_sum (LP.Known Case_A)) =
  [@inline_let]
  let res : t = A z in
  [@inline_let]
  let _ : squash (LP.dsum_tag_of_data t_sum res == LP.Known Case_A) =
    assert_norm (LP.dsum_tag_of_data t_sum res == LP.Known Case_A)
  in
  res

let synth_case_A_inj () : Lemma
  (LP.synth_injective synth_case_A)
= ()

inline_for_extraction
let synth_case_B (z: (U16.t) { U16.v z > 0 } ) : Tot (LP.dsum_cases t_sum (LP.Known Case_B)) =
  [@inline_let]
  let res : t = B z in
  [@inline_let]
  let _ : squash (LP.dsum_tag_of_data t_sum res == LP.Known Case_B) =
    assert_norm (LP.dsum_tag_of_data t_sum res == LP.Known Case_B)
  in
  res

let synth_case_B_inj () : Lemma
  (LP.synth_injective synth_case_B)
= ()

let parse_case_B_filter
  (x: U16.t)
: GTot bool
= U16.v x > 0

inline_for_extraction
let synth_case_C (x: LP.unknown_enum_repr case_enum) (y: U16.t) : Tot (LP.dsum_cases t_sum (LP.Unknown x)) =
  C x y

let synth_case_C_inj (x: LP.unknown_enum_repr case_enum) : Lemma
  (LP.synth_injective (synth_case_C x))
= ()

let parse_case_A : LP.parser _ (LP.dsum_cases t_sum (LP.Known Case_A)) =
    synth_case_A_inj ();
    LP.parse_synth (LP.parse_u8 `LP.nondep_then` LP.parse_u8) synth_case_A

let parse_case_B : LP.parser _ (LP.dsum_cases t_sum (LP.Known Case_B)) =
    synth_case_B_inj ();
    LP.parse_synth (LP.parse_filter LP.parse_u16 parse_case_B_filter) synth_case_B

let parse_case_C (x: LP.unknown_enum_repr case_enum) : Tot (LP.parser _ (LP.dsum_cases t_sum (LP.Unknown x))) =
  synth_case_C_inj x;
  LP.parse_synth LP.parse_u16 (synth_case_C x)

let parse_cases'
  (x: LP.dsum_known_key t_sum)
: Tot (k: LP.parser_kind & LP.parser k  (LP.dsum_cases t_sum (LP.Known x)))
= match x with
  | Case_A -> (| _, parse_case_A |)
  | Case_B -> (| _, parse_case_B |)

let parse_cases :
  (x: LP.dsum_key t_sum) ->
  Tot (LP.parser _ (LP.dsum_cases t_sum x))
= LP.parse_dsum_cases t_sum parse_cases' parse_case_C

inline_for_extraction
let parse32_cases_A
: (LP.parser32 parse_case_A)
=
    [@inline_let]
    let _ = synth_case_A_inj () in
    LP.parse32_synth
      _
      synth_case_A
      (fun x -> synth_case_A x)
      (LP.parse32_nondep_then LP.parse32_u8 LP.parse32_u8)
      ()

inline_for_extraction
let parse32_cases_B
: (LP.parser32 parse_case_B)
=
    [@inline_let]
    let _ = synth_case_B_inj () in
    LP.parse32_synth
      _
      synth_case_B
      (fun (x: U16.t { parse_case_B_filter x == true } ) -> synth_case_B x)
      (LP.parse32_filter LP.parse32_u16 parse_case_B_filter (fun x -> U16.gt x 0us))
      ()

inline_for_extraction
let parse32_cases'
  (x: LP.dsum_known_key t_sum)
: Tot (LP.parser32 (dsnd (parse_cases' x)))
= match x with
  | Case_A -> parse32_cases_A
  | Case_B -> parse32_cases_B

inline_for_extraction
let parse32_cases_C
  (x: LP.unknown_enum_repr case_enum)
: Tot (LP.parser32 (parse_case_C x))
=   [@inline_let]
    let _ = synth_case_C_inj x in
    LP.parse32_synth
      _
      (synth_case_C x)
      (fun (y: U16.t) -> synth_case_C x y)
      (LP.parse32_u16)
      ()

inline_for_extraction
let parse32_cases
: (x: LP.dsum_key t_sum) ->
  Tot (LP.parser32 (parse_cases x))
= LP.parse32_dsum_cases t_sum parse_cases' parse32_cases' parse_case_C parse32_cases_C

let parse_t : LP.parser _ t =
  LP.parse_dsum t_sum LP.parse_u8 parse_cases

module T = FStar.Tactics

inline_for_extraction
let destr_case_enum
  (t: Type)
: Tot (LP.maybe_enum_destr_t t case_enum)
= _ by (
    T.apply (`LP.maybe_enum_destr_t_intro);
    T.apply (`LP.maybe_enum_destr_cons);
    T.apply (`LP.maybe_enum_destr_cons);
    T.apply (`LP.maybe_enum_destr_nil);
    T.qed ()
  )

inline_for_extraction
let parse32_t
: LP.parser32 parse_t
= LP.parse32_dsum_gen
    _
    LP.parse32_u8
    _
    parse32_cases
    (destr_case_enum _)

(*
FStar.Tactics.synth_by_tactic
    (LP.parse32_sum_tac
      t_sum
      LP.parse32_u8
      parse32_cases
      parse_t
      ()
    )

let cases_of_t_A (x: t) : Lemma
  (cases_of_t x == Case_A <==> A? x)
= ()

inline_for_extraction
let synth_case_A_inv (z: LP.sum_cases t_sum Case_A) : Tot (z: (U8.t * U8.t)) =
  [@inline_let]
  let z' : t = z in
  let _ = cases_of_t_A z' in
  match z' with
  | A res -> res

let synth_case_A_inv_correct () : Lemma
  (LP.synth_inverse synth_case_A synth_case_A_inv)
= ()

let cases_of_t_B (x: t) : Lemma
  (cases_of_t x == Case_B <==> B? x)
= ()

inline_for_extraction
let synth_case_B_inv (z: LP.sum_cases t_sum Case_B) : Tot (z: U16.t { UInt16.v z > 0 } ) =
  [@inline_let]
  let z' : t = z in
  let _ = cases_of_t_B z' in
  match z' with
  | B res -> res

let synth_case_B_inv_correct () : Lemma
  (LP.synth_inverse synth_case_B synth_case_B_inv)
= ()

let serialize_case_A
: LP.serializer parse_case_A
= 
    synth_case_A_inj ();
    synth_case_A_inv_correct ();
      (LP.serialize_synth
        (LP.nondep_then LP.parse_u8 LP.parse_u8)
        synth_case_A
        (LP.serialize_nondep_then LP.parse_u8 LP.serialize_u8 () LP.parse_u8 LP.serialize_u8)
        synth_case_A_inv
        ()
      )

let serialize_case_B
: LP.serializer parse_case_B
= 
    synth_case_B_inj ();
    synth_case_B_inv_correct ();
      (LP.serialize_synth
        (LP.parse_filter LP.parse_u16 parse_case_B_filter)
        synth_case_B
        (LP.serialize_filter #_ #_ #LP.parse_u16 LP.serialize_u16 parse_case_B_filter)
        synth_case_B_inv
        ()
      )

let serialize_cases'
  (x: LP.sum_key t_sum)
: Tot (LP.serializer (dsnd (parse_cases' x)))
= match x with
  | Case_A -> serialize_case_A
  | Case_B -> serialize_case_B

let serialize_cases
: (x: LP.sum_key t_sum) ->
  Tot (LP.serializer (parse_cases x))
= LP.serialize_sum_cases t_sum parse_cases' serialize_cases'

let serialize_t : LP.serializer parse_t =
  LP.serialize_sum t_sum LP.serialize_u8 serialize_cases

inline_for_extraction
let serialize32_case_A
: LP.serializer32 (serialize_case_A)
= 
      [@inline_let]
      let _ = synth_case_A_inj () in
      [@inline_let]
      let _ = synth_case_A_inv_correct () in
      LP.serialize32_synth
        _
        synth_case_A
        _
        (LP.serialize32_nondep_then #_ #_ #LP.parse_u8 #LP.serialize_u8 LP.serialize32_u8 () #_ #_ #LP.parse_u8 #LP.serialize_u8 LP.serialize32_u8 ())
        synth_case_A_inv
        (fun x -> synth_case_A_inv x)
        ()

inline_for_extraction
let serialize32_case_B
: LP.serializer32 (serialize_case_B)
=
      [@inline_let]
      let _ = synth_case_B_inj () in
      [@inline_let]
      let _ = synth_case_B_inv_correct () in
      LP.serialize32_synth
        (LP.parse_filter LP.parse_u16 parse_case_B_filter)
        synth_case_B
        (LP.serialize_filter LP.serialize_u16 parse_case_B_filter)
        (LP.serialize32_filter LP.serialize32_u16 parse_case_B_filter)
        synth_case_B_inv
        (fun x -> synth_case_B_inv x)
        ()

inline_for_extraction
let serialize32_cases'
  (x: LP.sum_key t_sum)
: Tot (LP.serializer32 (serialize_cases' x))
= match x with
  | Case_A -> serialize32_case_A
  | Case_B -> serialize32_case_B

inline_for_extraction
let serialize32_cases
: (x: LP.sum_key t_sum) ->
  Tot (LP.serializer32 (serialize_cases x))
= LP.serialize32_sum_cases
    t_sum
    parse_cases'
    serialize_cases'
    serialize32_cases'

inline_for_extraction
let serialize32_t : LP.serializer32 serialize_t =
  [@inline_let]
  let (u: unit {
    LP.serializer32_sum_gen_precond
      LP.parse_u8_kind
      (LP.weaken_parse_cases_kind t_sum parse_cases')
  }) = assert_norm (
    LP.serializer32_sum_gen_precond
      LP.parse_u8_kind
      (LP.weaken_parse_cases_kind t_sum parse_cases')
  )
  in
  FStar.Tactics.synth_by_tactic (LP.serialize32_sum_tac
    t_sum
    #_
    #LP.serialize_u8
    LP.serialize32_u8
    serialize32_cases
    u
    (fun x -> cases_of_t x)
    serialize_t
    ()
  )
*)
