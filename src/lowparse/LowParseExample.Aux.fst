module LowParseExample.Aux

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot

noeq
type t =
  | A of (U8.t * U8.t)
  | B of U16.t

type cases =
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

inline_for_extraction
let cases_of_t
  (x: t)
: Tot cases
= match x with
  | A _ -> Case_A
  | B _ -> Case_B

inline_for_extraction
let t_sum
= LP.make_sum case_enum cases_of_t

inline_for_extraction
let synth_case_A (z: (U8.t * U8.t)) : Tot (LP.sum_cases t_sum Case_A) =
  [@inline_let]
  let res : t = A z in
  [@inline_let]
  let _ : squash (LP.sum_tag_of_data t_sum res == Case_A) =
    assert_norm (LP.sum_tag_of_data t_sum res == Case_A)
  in
  res

let synth_case_A_inj () : Lemma
  (LP.synth_injective synth_case_A)
= ()

inline_for_extraction
let synth_case_B (z: (U16.t)) : Tot (LP.sum_cases t_sum Case_B) =
  [@inline_let]
  let res : t = B z in
  [@inline_let]
  let _ : squash (LP.sum_tag_of_data t_sum res == Case_B) =
    assert_norm (LP.sum_tag_of_data t_sum res == Case_B)
  in
  res

let synth_case_B_inj () : Lemma
  (LP.synth_injective synth_case_B)
= ()
  
let parse_cases
  (x: LP.sum_key t_sum)
: Tot (LP.parser LP.parse_u16_kind  (LP.sum_cases t_sum x))
= match x with
  | Case_A ->
    synth_case_A_inj ();
    LP.parse_synth (LP.parse_u8 `LP.nondep_then` LP.parse_u8) synth_case_A
  | Case_B ->
    synth_case_B_inj ();
    LP.parse_synth LP.parse_u16 synth_case_B

inline_for_extraction
let parse32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.parser32 (parse_cases x))
= match x with
  | Case_A ->
    [@inline_let]
    let _ = synth_case_A_inj () in
    LP.parse32_synth
      _
      synth_case_A
      (fun x -> synth_case_A x)
      (LP.parse32_nondep_then LP.parse32_u8 LP.parse32_u8)
      ()
  | Case_B ->
    [@inline_let]
    let _ = synth_case_B_inj () in
    LP.parse32_synth
      _
      synth_case_B
      (fun x -> synth_case_B x)
      LP.parse32_u16
      ()

let parse_t : LP.parser _ t =
  LP.parse_sum t_sum LP.parse_u8 parse_cases

inline_for_extraction
let parse32_t
: LP.parser32 parse_t
= FStar.Tactics.synth_by_tactic
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
let synth_case_B_inv (z: LP.sum_cases t_sum Case_B) : Tot (z: U16.t) =
  [@inline_let]
  let z' : t = z in
  let _ = cases_of_t_B z' in
  match z' with
  | B res -> res

let synth_case_B_inv_correct () : Lemma
  (LP.synth_inverse synth_case_B synth_case_B_inv)
= ()

let serialize_cases
  (x: LP.sum_key t_sum)
: Tot (LP.serializer (parse_cases x))
= match x with
  | Case_A ->
    synth_case_A_inj ();
    synth_case_A_inv_correct ();
    LP.serialize_ext'
      _
      (LP.serialize_synth
        _
        synth_case_A
        (LP.serialize_nondep_then _ LP.serialize_u8 () _ LP.serialize_u8)
        synth_case_A_inv
        ()
      )
      (parse_cases x)
  | Case_B ->
    synth_case_B_inj ();
    synth_case_B_inv_correct ();
    LP.serialize_ext'
      _
      (LP.serialize_synth
        LP.parse_u16
        synth_case_B
        LP.serialize_u16
        synth_case_B_inv
        ()
      )
      (parse_cases x)

let serialize_t : LP.serializer parse_t =
  LP.serialize_sum t_sum LP.serialize_u8 serialize_cases

inline_for_extraction
let serialize32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.serializer32 (serialize_cases x))
= match x with
  | Case_A ->
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
  | Case_B ->
      [@inline_let]
      let _ = synth_case_B_inj () in
      [@inline_let]
      let _ = synth_case_B_inv_correct () in
      LP.serialize32_synth
        LP.parse_u16
        synth_case_B
        LP.serialize_u16
        LP.serialize32_u16
        synth_case_B_inv
        (fun x -> synth_case_B_inv x)
        ()

inline_for_extraction
let serialize32_t : LP.serializer32 serialize_t =
  FStar.Tactics.synth_by_tactic (
    LP.serialize32_sum_tac
      t_sum
      #_
      #LP.serialize_u8
      LP.serialize32_u8
      #_
      serialize32_cases
      ()
      (fun x -> cases_of_t x)
      serialize_t
      ()
  )

let parse_t_array : LP.parser _ (LP.array t 18) =
  LP.parse_array serialize_t 54 18

inline_for_extraction
let parse32_t_array : LP.parser32 parse_t_array =
  LP.parse32_array serialize_t parse32_t 54 54ul 18 ()

let serialize_t_array : LP.serializer parse_t_array =
  LP.serialize_array serialize_t 54 18 ()

inline_for_extraction
let serialize32_t_array : LP.serializer32 serialize_t_array =
  LP.serialize32_array #_ #_ #parse_t #serialize_t serialize32_t 54 18 ()

// NOTE: in this example, byte-size bounds do not need to exactly match element-count bounds (which would be 15 and 21 respectively)

let parse_t_vlarray : LP.parser _ (LP.vlarray t 5 7) =
  LP.parse_vlarray 13 22 serialize_t 5 7 ()

inline_for_extraction
let parse32_t_vlarray : LP.parser32 parse_t_vlarray =
  LP.parse32_vlarray 13 13ul 22 22ul serialize_t parse32_t 5 7 ()

let serialize_t_vlarray : LP.serializer parse_t_vlarray =
  LP.serialize_vlarray 13 22 serialize_t 5 7 ()

inline_for_extraction
let serialize32_t_vlarray : LP.serializer32 serialize_t_vlarray =
  LP.serialize32_vlarray 13 22 #_ #_ #parse_t #serialize_t serialize32_t 5 7 ()
