module LowParseExample6.Aux

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot

type cases : eqtype =
  | Case_A
  | Case_B

inline_for_extraction
let case_enum : LP.total_enum cases U8.t =
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

inline_for_extraction
let case_B = (x: U16.t { U16.v x > 0 } )

noeq
type t =
  | A of (U8.t * U8.t)
  | B of case_B
  | C : LP.unknown_enum_repr case_enum -> U16.t -> t

inline_for_extraction
let cases_of_t
  (x: t)
: Tot (LP.maybe_total_enum_key case_enum)
= match x with
  | A _ -> LP.TotalKnown Case_A
  | B _ -> LP.TotalKnown Case_B
  | C x _ -> LP.TotalUnknown x

inline_for_extraction
let type_of_known_case
  (x: LP.enum_key case_enum)
: Tot Type0
= match x with
  | Case_A -> U8.t * U8.t
  | Case_B -> case_B

inline_for_extraction
let synth_known_case
  (x: LP.enum_key case_enum)
  (y: type_of_known_case x)
: Tot (LP.refine_with_tag cases_of_t (LP.TotalKnown x))
= match x with
  | Case_A -> (A y <: t)
  | Case_B -> (B y <: t)

inline_for_extraction
let synth_unknown_case
  (x: LP.unknown_enum_repr case_enum)
  (y: U16.t)
: Tot (LP.refine_with_tag cases_of_t (LP.TotalUnknown x))
= C x y

inline_for_extraction
let synth_case_recip
  (x: t)
: Tot (LP.dsum_type_of_tag case_enum type_of_known_case U16.t (cases_of_t x))
= match x with
  | A y -> (y <: LP.dsum_type_of_tag case_enum type_of_known_case U16.t (cases_of_t x))
  | B y -> (y <: LP.dsum_type_of_tag case_enum type_of_known_case U16.t (cases_of_t x))
  | C _ y ->  (y <: LP.dsum_type_of_tag case_enum type_of_known_case U16.t (cases_of_t x))

inline_for_extraction
let t_sum : LP.dsum
= LP.make_dsum case_enum cases_of_t type_of_known_case U16.t synth_known_case synth_unknown_case synth_case_recip
    (_ by (LP.synth_case_recip_synth_case_tac ()))
    (fun x -> ())

let parse_case_B_filter
  (x: U16.t)
: GTot bool
= U16.v x > 0

let parse_case_B : LP.parser _ case_B =
  LP.parse_filter LP.parse_u16 parse_case_B_filter

let parse_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (k: LP.parser_kind & LP.parser k (type_of_known_case x))
= match x with
  | Case_A -> (| _, LP.parse_u8 `LP.nondep_then` LP.parse_u8 |)
  | Case_B -> (| _, parse_case_B |)

let parse_t : LP.parser _ t =
  LP.parse_dsum t_sum LP.parse_u8 parse_known_cases LP.parse_u16

inline_for_extraction
let parse32_cases_B
: (LP.parser32 parse_case_B)
= LP.parse32_filter LP.parse32_u16 parse_case_B_filter (fun x -> U16.gt x 0us)

inline_for_extraction
let parse32_known_cases
  (x: LP.dsum_known_key t_sum)
: Tot (LP.parser32 (dsnd (parse_known_cases x)))
= match x with
  | Case_A -> LP.parse32_u8 `LP.parse32_nondep_then` LP.parse32_u8
  | Case_B -> parse32_cases_B

let parse32_t
: LP.parser32 parse_t
= LP.parse32_dsum t_sum LP.parse32_u8 parse_known_cases parse32_known_cases LP.parse32_u16 (_ by (LP.maybe_enum_destr_t_tac ()))

(*
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

module T = FStar.Tactics

inline_for_extraction
let destr_case_enum
  (t: Type)
: Tot (LP.maybe_enum_destr_t t case_enum)
= _ by (LP.maybe_enum_destr_t_tac ())

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
*)


let cases_of_t_A (x: t) : Lemma
  (cases_of_t x == LP.Known Case_A <==> A? x)
= ()

inline_for_extraction
let synth_case_A_inv (z: LP.dsum_cases t_sum (LP.Known Case_A)) : Tot (z: (U8.t * U8.t)) =
  [@inline_let]
  let z' : t = z in
  let _ = cases_of_t_A z' in
  match z' with
  | A res -> res

let synth_case_A_inv_correct () : Lemma
  (LP.synth_inverse synth_case_A synth_case_A_inv)
= ()

let cases_of_t_B (x: t) : Lemma
  (cases_of_t x == LP.Known Case_B <==> B? x)
= ()

inline_for_extraction
let synth_case_B_inv (z: LP.dsum_cases t_sum (LP.Known Case_B)) : Tot (z: U16.t { UInt16.v z > 0 } ) =
  [@inline_let]
  let z' : t = z in
  let _ = cases_of_t_B z' in
  match z' with
  | B res -> res

let synth_case_B_inv_correct () : Lemma
  (LP.synth_inverse synth_case_B synth_case_B_inv)
= ()

let cases_of_t_C (x: t) : Lemma
  ((LP.Unknown? (cases_of_t x) <==> C? x) /\ (match cases_of_t x, x with
    | LP.Unknown k1, C k2 _ -> k1 == k2
    | _ -> True
  ))
= ()

inline_for_extraction
let synth_case_C_inv (x: LP.unknown_enum_repr case_enum) (y: LP.dsum_cases t_sum (LP.Unknown x)) : Tot U16.t =
  [@inline_let]
  let z : t = y in
  let _ = cases_of_t_C z in
  match z with
  | C _ y -> y

let synth_case_C_inv_correct (x: LP.unknown_enum_repr case_enum) : Lemma (LP.synth_inverse (synth_case_C x) (synth_case_C_inv x))
= Classical.forall_intro cases_of_t_C

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

let serialize_case_C
  (x: LP.unknown_enum_repr case_enum)
: Tot (LP.serializer (parse_case_C x))
= synth_case_C_inj x;
  synth_case_C_inv_correct x;
  LP.serialize_synth
    LP.parse_u16
    (synth_case_C x)
    LP.serialize_u16
    (synth_case_C_inv x)
    ()

let serialize_cases'
  (x: LP.dsum_known_key t_sum)
: Tot (LP.serializer (dsnd (parse_cases' x)))
= match x with
  | Case_A -> serialize_case_A
  | Case_B -> serialize_case_B

let serialize_cases
: (x: LP.dsum_key t_sum) ->
  Tot (LP.serializer (parse_cases x))
= LP.serialize_dsum_cases t_sum parse_cases' serialize_cases' parse_case_C serialize_case_C

let serialize_t : LP.serializer parse_t =
  LP.serialize_dsum t_sum LP.serialize_u8 serialize_cases

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
let serialize32_case_C
  (x: LP.unknown_enum_repr case_enum)
: Tot (LP.serializer32 (serialize_case_C x))
=
      [@inline_let]
      let _ = synth_case_C_inj x in
      [@inline_let]
      let _ = synth_case_C_inv_correct x in
      LP.serialize32_synth
        LP.parse_u16
        (synth_case_C x)
        LP.serialize_u16
        LP.serialize32_u16
        (synth_case_C_inv x)
        (fun y -> synth_case_C_inv x y)
        ()

inline_for_extraction
let serialize32_cases'
  (x: LP.dsum_known_key t_sum)
: Tot (LP.serializer32 (serialize_cases' x))
= match x with
  | Case_A -> serialize32_case_A
  | Case_B -> serialize32_case_B

inline_for_extraction
let dep_destr
  (t: (k: LP.enum_key case_enum) -> Tot Type)
: Tot (LP.dep_enum_destr case_enum t)
= _ by (LP.dep_enum_destr_tac ())

inline_for_extraction
let serialize32_cases
: (x: LP.dsum_key t_sum) ->
  Tot (LP.serializer32 (serialize_cases x))
= LP.serialize32_dsum_cases
    t_sum
    parse_cases'
    serialize_cases'
    serialize32_cases'
    _
    _
    serialize32_case_C
    (dep_destr _)

inline_for_extraction
let serialize32_key : LP.serializer32 (LP.serialize_maybe_enum_key _ LP.serialize_u8 (LP.dsum_enum t_sum))
= _ by (LP.serialize32_maybe_enum_key_tac LP.serialize32_u8 (LP.dsum_enum t_sum) ())

inline_for_extraction
let serialize32_t : LP.serializer32 serialize_t =
  [@inline_let]
  let (u: unit {
    LP.serializer32_sum_gen_precond
      LP.parse_u8_kind
      (LP.weaken_parse_dsum_cases_kind' t_sum parse_cases' parse_case_C)
  }) = assert_norm (
    LP.serializer32_sum_gen_precond
      LP.parse_u8_kind
      (LP.weaken_parse_dsum_cases_kind' t_sum parse_cases' parse_case_C)
  )
  in
  LP.serialize32_dsum_gen
    t_sum
    serialize32_key
    serialize32_cases
    ()
    (fun x -> cases_of_t x)


(*
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
