module LowParseExample.Aux

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot

let parse_case_B_filter
  (x: U16.t)
: GTot bool
= U16.v x > 0

inline_for_extraction
let case_B = (x: U16.t { parse_case_B_filter x } )

noeq
type t =
  | A of (U8.t * U8.t)
  | B of case_B

type cases : eqtype =
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
let type_of_case
  (x: cases)
: Tot Type0
= match x with
  | Case_A -> U8.t * U8.t
  | Case_B -> case_B

inline_for_extraction
let synth_case
  (x: cases)
  (y: type_of_case x)
: Tot (LP.refine_with_tag cases_of_t x)
= match x with
  | Case_A -> A y
  | Case_B -> B y

inline_for_extraction
let synth_case_recip
  (x: t)
: Tot (type_of_case (cases_of_t x))
= match x with
  | A y -> (y <: type_of_case (cases_of_t x))
  | B y -> (y <: type_of_case (cases_of_t x))

inline_for_extraction
let t_sum : LP.sum
= LP.make_sum case_enum cases_of_t type_of_case synth_case synth_case_recip (fun x y -> ()) (fun x -> ())

let parse_case_B : LP.parser _ case_B =
  LP.parse_filter LP.parse_u16 parse_case_B_filter

let parse_cases
  (x: LP.sum_key t_sum)
: Tot (k: LP.parser_kind & LP.parser k (type_of_case x))
= match x with
  | Case_A -> (| _, LP.parse_u8 `LP.nondep_then` LP.parse_u8 |)
  | Case_B -> (| _, parse_case_B |)

let parse32_case_B : LP.parser32 parse_case_B =
  LP.parse32_filter LP.parse32_u16 parse_case_B_filter (fun x -> U16.gt x 0us)

inline_for_extraction
let parse32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.parser32 (dsnd (parse_cases x)))
= match x with
  | Case_A -> (LP.parse32_nondep_then LP.parse32_u8 LP.parse32_u8 <: LP.parser32 (dsnd (parse_cases x)))
  | Case_B -> (parse32_case_B <: LP.parser32 (dsnd (parse_cases x)))

let parse_t : LP.parser _ t =
  LP.parse_sum t_sum LP.parse_u8 parse_cases

inline_for_extraction
let parse32_case_destr
: (LP.enum_destr_t (option (t * FStar.UInt32.t)) case_enum)
= _ by (LP.enum_destr_tac case_enum)

let parse32_case_enum
: LP.parser32 (LP.parse_enum_key LP.parse_u8 case_enum)
= _ by (LP.parse32_enum_key_tac LP.parse32_u8 case_enum ())

let parse32_t
: LP.parser32 parse_t
= LP.parse32_sum t_sum _ parse32_case_enum _ parse32_cases parse32_case_destr

let serialize_case_B : LP.serializer parse_case_B =
  LP.serialize_filter LP.serialize_u16 parse_case_B_filter

inline_for_extraction
let serialize32_case_B: LP.serializer32 serialize_case_B =
  LP.serialize32_filter LP.serialize32_u16 parse_case_B_filter

let serialize_cases
  (x: LP.sum_key t_sum)
: Tot (LP.serializer (dsnd (parse_cases x)))
= match x with
  | Case_A -> (LP.serialize_nondep_then _ LP.serialize_u8 () _ LP.serialize_u8 <: LP.serializer (dsnd (parse_cases x)))
  | Case_B -> (serialize_case_B <: LP.serializer (dsnd (parse_cases x)))

inline_for_extraction
let serialize32_cases
  (x: LP.sum_key t_sum)
: Tot (LP.serializer32 (serialize_cases x))
= match x with
  | Case_A -> (LP.serialize32_nondep_then LP.serialize32_u8 () LP.serialize32_u8 () <: LP.serializer32 (serialize_cases x))
  | Case_B -> (serialize32_case_B <: LP.serializer32 (serialize_cases x))

let serialize_t : LP.serializer parse_t =
  LP.serialize_sum t_sum LP.serialize_u8 serialize_cases

inline_for_extraction
let serialize32_key : LP.serializer32 (LP.serialize_enum_key _ LP.serialize_u8 case_enum) =
  _ by (LP.serialize32_enum_key_gen_tac LP.serialize32_u8 case_enum ())

let serialize32_t : LP.serializer32 serialize_t =
  assert_norm (LP.serializer32_sum_gen_precond (LP.get_parser_kind LP.parse_u8) (LP.weaken_parse_cases_kind t_sum parse_cases));
  LP.serialize32_sum
    t_sum
    _
    serialize32_key
    _
    serialize32_cases
    (_ by (LP.dep_enum_destr_tac ()))
    ()

let parse_t_array_precond () : Lemma
  (LP.fldata_array_precond
      parse_t
      54
      18
    == true)
= assert_norm (
    LP.fldata_array_precond
      parse_t
      54
      18
    == true   
  )

let parse_t_array : LP.parser _ (LP.array t 18) =
  parse_t_array_precond ();
  LP.parse_array serialize_t 54 18

inline_for_extraction
let parse32_t_array : LP.parser32 parse_t_array =
  [@inline_let]
  let _ = parse_t_array_precond () in
  LP.parse32_array serialize_t parse32_t 54 54ul 18 ()

let serialize_t_array : LP.serializer parse_t_array =
  parse_t_array_precond ();
  LP.serialize_array serialize_t 54 18 ()

inline_for_extraction
let serialize32_t_array : LP.serializer32 serialize_t_array =
  [@inline_let]
  let _ = parse_t_array_precond () in
  LP.serialize32_array #_ #_ #parse_t #serialize_t serialize32_t 54 18 ()

// NOTE: in this example, byte-size bounds do not need to exactly match element-count bounds (which would be 15 and 21 respectively)

let parse_t_vlarray_precond () : Lemma
  (LP.vldata_vlarray_precond 13 22 parse_t 5 7 == true)
= assert_norm (LP.vldata_vlarray_precond 13 22 parse_t 5 7 == true)

let parse_t_vlarray : LP.parser _ (LP.vlarray t 5 7) =
  parse_t_vlarray_precond ();
  LP.parse_vlarray 13 22 serialize_t 5 7 ()

inline_for_extraction
let parse32_t_vlarray : LP.parser32 parse_t_vlarray =
  [@inline_let]
  let _ = parse_t_vlarray_precond () in
  LP.parse32_vlarray 13 13ul 22 22ul serialize_t parse32_t 5 7 ()

let serialize_t_vlarray : LP.serializer parse_t_vlarray =
  parse_t_vlarray_precond ();
  LP.serialize_vlarray 13 22 serialize_t 5 7 ()

inline_for_extraction
let serialize32_t_vlarray : LP.serializer32 serialize_t_vlarray =
  [@inline_let]
  let _ = parse_t_vlarray_precond () in
  LP.serialize32_vlarray 13 22 #_ #_ #parse_t #serialize_t serialize32_t 5 7 ()
