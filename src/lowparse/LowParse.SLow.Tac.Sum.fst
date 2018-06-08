module LowParse.SLow.Tac.Sum
include LowParse.SLow.Tac.Enum
include LowParse.SLow.Sum

module T = FStar.Tactics
module U32 = FStar.UInt32

(* Universal destructor *)

noextract
let rec enum_destr_tac
  (t: Type)
  (eq: (t -> t -> GTot Type0))
  (ifc: if_combinator t eq)
  (u_refl: r_reflexive_t _ eq)
  (u_trans: r_transitive_t _ eq)
  (#key #repr: eqtype)
  (e: enum key repr)
  (eu: unit { Cons? e } )
: T.Tac unit
= match e with
  | [_] ->
    let fu = quote (enum_destr_cons_nil' #key #repr #t eq u_refl) in
    T.apply fu;
    T.iseq [
      solve_vc;
      solve_vc;
    ]
  | _ :: e' ->
    let fu = quote (enum_destr_cons' #key #repr #t eq ifc u_refl u_trans) in
    T.apply fu;
    T.iseq [
      solve_vc;
      (fun () -> enum_destr_tac t eq ifc u_refl u_trans e' ());
    ]

(* Parser *)

let parse32_sum_eq (t: sum) : Tot (_ -> _ -> GTot Type0) =
  feq bytes32 (option (sum_type t * U32.t)) (eq2 #_)

abstract
let parse32_sum_eq_refl (t: sum) : Tot (r_reflexive_t _ (parse32_sum_eq t)) =
  fun _ -> ()

abstract
let parse32_sum_eq_trans (t: sum) : Tot (r_transitive_t _ (parse32_sum_eq t)) =
  fun _ _ _ -> ()

noextract
let parse32_sum_tac
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (p32: parser32 p)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (pc x))))
  (#k' : parser_kind)
  (#t' : Type0)
  (p' : parser k' t')
  (u: unit {
    Cons? (sum_enum t) /\
    k' == and_then_kind (parse_filter_kind kt) k /\
    t' == sum_type t /\
    p' == parse_sum t p pc
  })
  ()
: T.Tac unit
= let fu : T.term = quote (
    parse32_sum_gen
      #kt
      t
      p
      #k
      #pc
      pc32
  )
  in
  T.apply fu;
  T.iseq [
    solve_vc;
    solve_vc;
    solve_vc;
    (fun () -> parse32_enum_key_tac p32 (sum_enum t) (parse_enum_key p (sum_enum t)) () ());
    (fun () -> enum_destr_tac (bytes32 -> Tot (option (sum_type t * U32.t))) (parse32_sum_eq t) (fif _ _ (eq2 #_) (default_if _)) (parse32_sum_eq_refl t) (parse32_sum_eq_trans t) (sum_enum t) ());
  ];
  T.dump "parse32_sum_tac"

noextract
let rec sum_destr_tac
  (v: Type)
  (s: sum)
  (su: unit { Cons? (sum_enum s) } )
: T.Tac unit
  (decreases (sum_enum s))
= let open T in
  match sum_enum s with
  | [_] ->
    let fu = quote (sum_destr_cons_nil' v) in
    T.apply fu;
    T.iseq [
      solve_vc;
      solve_vc;
    ]
  | _ ->
    let fu = quote (sum_destr_cons' v) in
    T.apply fu;
    T.iseq [
      solve_vc;
      (fun () -> sum_destr_tac v (sum_tail s) ());
    ]

let serialize32_sum_tac_precond
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p )
  (s32: serializer32 s)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (#k' : parser_kind)
  (#t' : Type0)
  (#p' : parser k' t')
  (s' : serializer p')
: GTot Type0
=   Cons? (sum_enum t) /\
    k' == and_then_kind (parse_filter_kind kt) k /\
    t' == sum_type t /\
    p' == parse_sum t p pc /\
    s' == serialize_sum t s sc

noextract
let serialize32_sum_tac
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p )
  (s32: serializer32 s)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == (sum_tag_of_data t x <: sum_key_type t)} )))
  (#k' : parser_kind)
  (#t' : Type0)
  (#p' : parser k' t')
  (s' : serializer p')
  (u' : unit {
    serialize32_sum_tac_precond t s32 sc32 u s'
  })
  ()
: T.Tac unit
= let fu = quote (
    serialize32_sum_gen
      #kt
      t
      #p
      s
      #k
      #pc
      #sc
      sc32
      tag_of_data
      #k'
      #t'
      #p'
      s'
  )
  in
  T.apply fu;
  T.iseq [
    solve_vc;
    solve_vc;
    solve_vc;
    solve_vc;
    solve_vc;
    solve_vc;
    (fun () -> serialize32_enum_key_gen_tac #kt #(sum_key_type t) #(sum_repr_type t) #p #s s32 (sum_enum t) #(parse_filter_kind kt) #(parse_enum_key p (sum_enum t)) (serialize_enum_key p s (sum_enum t)) () ());
    (fun () -> sum_destr_tac bytes32 t ());
  ]

(*
noextract
let size32_sum_tac'
  (#kt: parser_kind)
  (t: sum)
  (tu: unit { Cons? (sum_enum t) } )
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p )
  (s32: size32 (serialize_enum_key _ s (sum_enum t)))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (size32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == (sum_tag_of_data t x <: sum_key_type t)} )))
  (#k' : parser_kind)
  (#t' : Type0)
  (#p' : parser k' t')
  (s' : serializer p')
  (u' : unit {
    k' == and_then_kind (parse_filter_kind kt) k /\
    t' == sum_type t /\
    p' == parse_sum t p pc /\
    s' == serialize_sum t s sc
  })
: T.Tac T.term
= let st = quote t in
  let ar2 = sum_destr_tac U32.t t tu st in
  let fu = quote (
    size32_sum_gen
      #kt
      t
      #p
      #s
      s32
      #k
      #pc
      #sc
      sc32
      u
      tag_of_data
      #k'
      #t'
      #p'
      s'
      u'
  )
  in
  T.mk_app fu [
    ar2, T.Q_Explicit;
  ]
