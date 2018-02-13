module LowParse.SLow.Sum
include LowParse.Spec.Sum
include LowParse.SLow.Enum

module B32 = FStar.Bytes
module U32 = FStar.UInt32

let serializer32_sum_gen_precond
  (kt: parser_kind)
  (k: parser_kind)
: GTot Type0
= kt.parser_kind_subkind == Some ParserStrong /\
  Some? kt.parser_kind_high /\
  Some? k.parser_kind_high /\ (
  let (Some vt) = kt.parser_kind_high in
  let (Some v) = k.parser_kind_high in
  vt + v < 4294967296
  )

inline_for_extraction
let serialize32_sum_gen
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p)
  (s32: serializer32 (serialize_enum_key _ s (sum_enum t)))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == sum_tag_of_data t x} )))
: Tot (serializer32 (serialize_sum t s sc))
= fun (input: sum_type t) -> ((
    let tg = tag_of_data input in
    let stg = s32 tg in
    let s = sc32 tg input in
    b32append stg s
  ) <: (res: bytes32 { serializer32_correct (serialize_sum t s sc) input res } ))

(* Universal destructor *)

let r_reflexive
  (t: Type)
  (r: (t -> t -> GTot Type0))
: GTot Type0
= forall (x: t) . r x x

let r_symmetric
  (t: Type)
  (r: (t -> t -> GTot Type0))
: GTot Type0
= forall (x y: t) . r x y ==> r y x

let r_transitive
  (t: Type)
  (r: (t -> t -> GTot Type0))
: GTot Type0
= forall (x y z: t) . (r x y /\ r y z) ==> r x z

inline_for_extraction
let if_combinator
  (t: Type)
  (eq: (t -> t -> GTot Type0))
: Tot Type
= (cond: bool) ->
  (sv_true: (cond_true cond -> Tot t)) ->
  (sv_false: (cond_false cond -> Tot t)) ->
  Tot (y: t { eq y (if cond then sv_true () else sv_false ()) } )

inline_for_extraction
let default_if
  (t: Type)
: Tot (if_combinator t (eq2 #t))
= fun
  (cond: bool)
  (s_true: (cond_true cond -> Tot t))
  (s_false: (cond_false cond -> Tot t))
-> (if cond
  then s_true ()
  else s_false ()) <: (y: t { y == (if cond then s_true () else s_false ()) } )

let feq
  (u v: Type)
  (eq: (v -> v -> GTot Type0))
  (f1 f2: (u -> Tot v))
: GTot Type0
= (forall (x: u) . eq (f1 x) (f2 x))

inline_for_extraction
let fif
  (u v: Type)
  (eq: (v -> v -> GTot Type0))
  (ifc: if_combinator v eq)
: Tot (if_combinator (u -> Tot v) (feq u v eq))
= fun (cond: bool) (s_true: (cond_true cond -> u -> Tot v)) (s_false: (cond_false cond -> u -> Tot v)) (x: u) ->
    ifc
      cond
      (fun h -> s_true () x)
      (fun h -> s_false () x)

inline_for_extraction
let enum_destr_t
  (#key #repr: eqtype)
  (t: Type)
  (eq: (t -> t -> GTot Type0))
  (e: enum key repr)
: Tot Type
= (f: ((x: enum_key e) -> Tot t)) ->
  (x: enum_key e) ->
  Tot (y: t { eq y (f x) } )

inline_for_extraction
let enum_destr_cons
  (#key #repr: eqtype)
  (#t: Type)
  (eq: (t -> t -> GTot Type0))
  (ift: if_combinator t eq)
  (e: enum key repr)
  (u: unit { Cons? e /\ r_reflexive t eq /\ r_transitive t eq } )
  (g: enum_destr_t t eq (enum_tail e))
: Tot (enum_destr_t t eq e)
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, _) :: _ ->
     (fun (f: (enum_key e -> Tot t)) (x: enum_key e) -> ((
       [@inline_let]
       let f' : (enum_key (enum_tail e) -> Tot t) =
         (fun (x' : enum_key (enum_tail e)) ->
           [@inline_let]
           let (x_ : enum_key e) = (x' <: key) in
           f x_
         )
       in
       [@inline_let]
       let (y: t) =
       ift
         ((k <: key) = x)
         (fun h -> f k)
         (fun h ->
           [@inline_let]
           let x' : enum_key (enum_tail e) = (x <: key) in
           (g f' x' <: t))
       in
       y
     ) <: (y: t { eq y (f x) } )))
  ) e

inline_for_extraction
let enum_destr_cons_nil
  (#key #repr: eqtype)
  (#t: Type)
  (eq: (t -> t -> GTot Type0))
  (e: enum key repr)
  (u: unit { Cons? e /\ Nil? (enum_tail e) /\ r_reflexive t eq } )
: Tot (enum_destr_t t eq e)
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, _) :: _ ->
     (fun (f: (enum_key e -> Tot t)) (x: enum_key e) -> ((
       f k
     ) <: (y: t { eq y (f x) } )))
  ) e

#set-options "--z3rlimit 64"

inline_for_extraction
let parse32_sum_gen'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (pc x))))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (destr: enum_destr_t (bytes32 -> Tot (option (sum_type t * U32.t))) (feq bytes32 _ (eq2 #(option (sum_type t * U32.t)))) (sum_enum t))
: Tot (parser32 (parse_sum t p pc))
= fun (input: bytes32) -> ((
    match p32 input with
    | Some (tg, consumed_tg) ->
      let input' = b32slice input consumed_tg (B32.len input) in
      begin match destr (fun (x: sum_key t) (input: bytes32) -> match pc32 x input with | Some (d, consumed_d) -> Some ((d <: sum_type t), consumed_d) | _ -> None) tg input' with
      | Some (d, consumed_d) ->
        // FIXME: implicit arguments are not inferred because (synth_tagged_union_data ...) is Tot instead of GTot
        assert (parse (parse_synth #_ #_ #(sum_type t) (pc tg) (synth_tagged_union_data (sum_tag_of_data t) tg)) (B32.reveal input') == Some (d, U32.v consumed_d));
        Some (d, U32.add consumed_tg consumed_d)
      | _ -> None
      end
    | _ -> None
  )
  <: (res: option (sum_type t * U32.t) { parser32_correct (parse_sum t p pc) input res } )
  )

#reset-options

module Seq = FStar.Seq

let parse_sum_with_nondep_aux
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#knd: parser_kind)
  (#nondep_t: Type0)
  (pnd: parser knd nondep_t)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (input: bytes)
: GTot (option ((nondep_t * sum_type t) * consumed_length input))
= match parse (parse_enum_key p (sum_enum t)) input with
  | Some (tg, consumed_tg) ->
    let input1 = Seq.slice input consumed_tg (Seq.length input) in
    begin match parse pnd input1 with
    | Some (nd, consumed_nd) ->
      let input2 = Seq.slice input1 consumed_nd (Seq.length input1) in
      begin match parse (pc tg) input2 with
      | Some (d, consumed_d) ->
        Some ((nd, d), consumed_tg + (consumed_nd + consumed_d))
      | _ -> None
    end
    | _ -> None
    end
  | _ -> None

#set-options "--z3rlimit 256 --max_fuel 32"

let parse_sum_with_nondep_aux_correct
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#knd: parser_kind)
  (#nondep_t: Type0)
  (pnd: parser knd nondep_t)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (input: bytes)
: Lemma
  (parse_sum_with_nondep_aux t p pnd pc input == parse (parse_sum_with_nondep t p pnd pc) input)
=   match parse (parse_enum_key p (sum_enum t)) input with
    | Some (tg, consumed_tg) ->
      let input1 = Seq.slice input consumed_tg (Seq.length input) in
      begin match parse pnd input1 with
      | Some (nd, consumed_nd) ->
        let input2 = Seq.slice input1 consumed_nd (Seq.length input1) in
        begin match parse (pc tg) input2 with
        | Some (d, consumed_d) ->
          // FIXME: implicit arguments are not inferred because (synth_tagged_union_data ...) is Tot instead of GTot
          let (tg' : sum_key (make_sum_with_nondep nondep_t t)) = (tg <: sum_key_type (make_sum_with_nondep nondep_t t)) in
          let (ndd_ : (nondep_t * sum_type t)) = (nd, (d <: sum_type t)) in
          let (ndd_ : sum_type (make_sum_with_nondep nondep_t t)) = ndd_ in
          let u' : sum_key_type (make_sum_with_nondep nondep_t t) = sum_tag_of_data (make_sum_with_nondep nondep_t t) ndd_ in
          let u : sum_key_type (make_sum_with_nondep nondep_t t) = sum_tag_of_data t (d <: sum_type t) in
          assert_norm (u' == u);
          assert (sum_tag_of_data (make_sum_with_nondep nondep_t t) ndd_ == tg');
          let (ndd : sum_cases (make_sum_with_nondep nondep_t t) tg') = ndd_ in
          assert_norm (synth_sum_with_nondep_case nondep_t t tg (nd, d) == ndd);
          let p1 : option (sum_cases (make_sum_with_nondep nondep_t t) tg' * consumed_length input1) = parse (parse_sum_with_nondep_cases t pnd pc tg') input1 in
          assert (p1 == Some (ndd, consumed_nd + consumed_d));
//          assert (parse (parse_sum_with_nondep t p pnd pc) input == Some (ndd_, consumed_tg + (consumed_nd + consumed_d)));
          assert (parse (parse_synth #_ #_ #(sum_type (make_sum_with_nondep nondep_t t)) (parse_sum_with_nondep_cases t pnd pc tg) (synth_tagged_union_data (sum_tag_of_data (make_sum_with_nondep nondep_t t)) tg)) (input1) == Some (ndd_, consumed_nd + consumed_d));
//          admit
          ()
        | _ -> ()
      end
      | _ -> ()
      end
    | _ -> ()

#reset-options

#set-options "--z3rlimit 32"

inline_for_extraction
let parse32_sum_with_nondep_aux
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#knd: parser_kind)
  (#nondep_t: Type0)
  (#pnd: parser knd nondep_t)
  (pnd32: parser32 pnd)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (pc x))))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (destr: enum_destr_t (bytes32 -> Tot (option (sum_type t * U32.t))) (feq bytes32 _ (eq2 #(option (sum_type t * U32.t)))) (sum_enum t))
  (input: bytes32)
: Tot (option ((nondep_t * sum_type t) * U32.t))
= match p32 input with
  | Some (tg, consumed_tg) ->
    let input1 = b32slice input consumed_tg (B32.len input) in
    begin match pnd32 input1 with
    | Some (nd, consumed_nd) ->
      let input2 = b32slice input1 consumed_nd (B32.len input1) in
      begin match 
        destr (fun (x: sum_key t) (input: bytes32) -> match pc32 x input with | Some (d, consumed_d) -> Some ((d <: sum_type t), consumed_d) | _ -> None) tg input2
      with
      | Some (d, consumed_d) ->
        Some ((nd, d), U32.add consumed_tg (U32.add consumed_nd consumed_d))
      | _ -> None
    end
    | _ -> None
    end
  | _ -> None

inline_for_extraction
let parse32_sum_with_nondep_aux_correct
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#knd: parser_kind)
  (#nondep_t: Type0)
  (#pnd: parser knd nondep_t)
  (pnd32: parser32 pnd)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (pc x))))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (destr: enum_destr_t (bytes32 -> Tot (option (sum_type t * U32.t))) (feq bytes32 _ (eq2 #(option (sum_type t * U32.t)))) (sum_enum t))
  (input: bytes32)
: Lemma
  (parser32_correct (parse_sum_with_nondep t p pnd pc) input (parse32_sum_with_nondep_aux t p pnd32 pc32 p32 destr input))
= let res = parse32_sum_with_nondep_aux t p pnd32 pc32 p32 destr input in
  let gp = parse_sum_with_nondep_aux t p pnd pc (B32.reveal input) in
  assert (match res with
  | None -> gp == None
  | Some (hres, consumed) ->
    Some? gp /\ (
    let (Some (hres', consumed')) = gp in
    hres == hres' /\
    U32.v consumed == (consumed' <: nat)
  ));
  parse_sum_with_nondep_aux_correct t p pnd pc (B32.reveal input)

#reset-options

inline_for_extraction
let parse32_sum_gen
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (pc x))))
  (#k' : parser_kind)
  (#t' : Type0)
  (p' : parser k' t')
  (u: unit {
    k' == and_then_kind (parse_filter_kind kt) k /\
    t' == sum_type t /\
    p' == parse_sum t p pc
  })
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (destr: enum_destr_t (bytes32 -> Tot (option (sum_type t * U32.t))) (feq bytes32 _ (eq2 #(option (sum_type t * U32.t)))) (sum_enum t))
: Tot (parser32 p')
= parse32_sum_gen' t p pc32 p32 destr
