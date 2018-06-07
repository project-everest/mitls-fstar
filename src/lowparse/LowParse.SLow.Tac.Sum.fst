module LowParse.SLow.Tac.Sum
include LowParse.SLow.Tac.Enum
include LowParse.SLow.Sum

module T = FStar.Tactics
module U32 = FStar.UInt32

(* Universal destructor *)

noextract
let rec enum_destr_tac'
  (t: Type)
  (eq: (t -> t -> GTot Type0))
  (ifc: if_combinator t eq)
  (u: unit { r_reflexive _ eq /\ r_transitive _ eq } )
  (#key #repr: eqtype)
  (e: enum key repr)
  (eu: unit { Cons? e } )
  (et: T.term) // implicit invariant: et represents e
: T.Tac T.term
= match e with
  | [_] ->
    let fu = quote (enum_destr_cons_nil #key #repr #t eq) in
    T.mk_app fu [et, T.Q_Explicit]
  | _ ->
    assert (Cons? e /\ Cons? (enum_tail' e));
    (fun (e_: enum key repr { Cons? e_ /\ Cons? (enum_tail' e_) /\ e_ == e } ) ->
      let (e' : enum key repr { Cons? e' } ) = enum_tail' e_ in
      let et'_fu = quote (enum_tail' #key #repr) in
      let et' = T.mk_app et'_fu [et, T.Q_Explicit] in
      let ar2 = enum_destr_tac' t eq ifc u e' () et' in
      let fu = quote (enum_destr_cons #key #repr #t eq ifc) in
      T.mk_app fu [
        et, T.Q_Explicit;
        ar2, T.Q_Explicit;
      ]
    ) e

noextract
let rec enum_destr_tac_new
  (t: Type)
  (eq: (t -> t -> GTot Type0))
  (ifc: if_combinator t eq)
  (u: unit { r_reflexive _ eq /\ r_transitive _ eq } )
  (#key #repr: eqtype)
  (e: enum key repr)
  (eu: unit { Cons? e } )
: T.Tac unit
= match e with
  | [_] ->
    let fu = quote (enum_destr_cons_nil' #key #repr #t eq ()) in
    T.apply fu;
    T.iseq [
      (fun () -> T.exact_guard (quote ()); conclude ());
    ]
  | _ :: e' ->
    let fu = quote (enum_destr_cons' #key #repr #t eq ifc ()) in
    T.apply fu;
    T.iseq [
      (fun () -> enum_destr_tac_new t eq ifc u e' ());
      (fun () -> T.exact_guard (quote ()); conclude ());
    ]

(* Parser *)

noextract
let parse32_sum_tac_ar2
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
: T.Tac T.term
= let eq = feq bytes32 (option (sum_type t * U32.t)) (eq2 #_) in
  let (eq_refl : unit { r_reflexive _ eq /\ r_transitive _ eq } ) = () in
  let et = quote (sum_enum t) in
  enum_destr_tac'
      (bytes32 -> Tot (option (sum_type t * U32.t)))
      (feq bytes32 (option (sum_type t * U32.t)) (eq2 #_))
      (fif _ _ (eq2 #_) (default_if _))
      eq_refl
      (sum_enum t)
      ()
      et

noextract
let parse32_sum_tac_ar1
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
: T.Tac T.term
= parse32_enum_key_tac' p32 (sum_enum t) () (parse_enum_key p (sum_enum t)) ()

noextract
let parse32_sum_tac'
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
: T.Tac T.term
= let ar1 : T.term = parse32_sum_tac_ar1 t p32 pc32 p' u in
  let ar2 : T.term = parse32_sum_tac_ar2 t p32 pc32 p' u in
  let fu : T.term = quote (
    parse32_sum_gen
      #kt
      t
      p
      #k
      #pc
      pc32
      #k'
      #t'
      p'
      u
  )
  in
  let res : T.term = 
    T.mk_app fu [
      ar1, T.Q_Explicit;
      ar2, T.Q_Explicit;
    ]
  in
  res

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
= let f = parse32_sum_tac' t p32 pc32 p' u in
  T.print (T.term_to_string f);
  T.exact_guard f

noextract
let parse32_sum_tac_new
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
      #k'
      #t'
      p'
      u
  )
  in
  let eq = feq bytes32 (option (sum_type t * U32.t)) (eq2 #_) in
  let (eq_refl : unit { r_reflexive _ eq /\ r_transitive _ eq } ) = () in   
  T.apply fu;
  T.iseq [
    (fun () -> parse32_enum_key_tac_new p32 (sum_enum t) (parse_enum_key p (sum_enum t)) () ());
    (fun () -> enum_destr_tac_new (bytes32 -> Tot (option (sum_type t * U32.t))) eq (fif _ _ (eq2 #_) (default_if _)) eq_refl (sum_enum t) ());
  ]

noextract
let rec sum_destr_tac
  (v: Type)
  (s: sum)
  (su: unit { Cons? (sum_enum s) } )
  (st: T.term) // implicit invariant: st represents s
: T.Tac T.term
  (decreases (sum_enum s))
= let open T in
  match sum_enum s with
  | [_] ->
    let fu = quote (sum_destr_cons_nil v) in
    T.mk_app fu [st, T.Q_Explicit]
  | _ ->
    let s' : sum = sum_tail s in
    assert (Cons? (sum_enum s')) ;
    let (s' : sum { Cons? (sum_enum s') } ) = s' in
    let st'_fu = quote sum_tail in
    let st' = T.mk_app st'_fu [st, T.Q_Explicit] in
    let fu = quote (sum_destr_cons v) in
    let ar2 = sum_destr_tac v s' () st' in
    T.mk_app fu [
      st, T.Q_Explicit;
      ar2, T.Q_Explicit;
    ]

noextract
let rec sum_destr_tac_new
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
      (fun () -> T.exact (quote ()); conclude ());
    ]
  | _ ->
    let fu = quote (sum_destr_cons' v) in
    T.apply fu;
    T.iseq [
      (fun () -> sum_destr_tac_new v (sum_tail s) ());
      (fun () -> T.exact_guard (quote ()); conclude ());
    ]

noextract
let serialize32_sum_tac_ar1
  (#kt: parser_kind)
  (t: sum)
  (e: enum (sum_key_type t) (sum_repr_type t))
//  (bidon: unit)
  (tu: unit   { e == sum_enum t /\ Cons? e } )
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
    k' == and_then_kind (parse_filter_kind kt) k /\
    t' == sum_type t /\
    p' == parse_sum t p pc /\
    s' == serialize_sum t s sc
  })
: T.Tac T.term
= let te = quote e in
  T.print (T.term_to_string te);
//  let tbidon = quote bidon in
//  T.print (T.term_to_string tbidon);
  serialize32_enum_key_gen_tac'
    #kt
    #(sum_key_type t)
    #(sum_repr_type t)
    #p
    #s
    s32
    e
    tu
    #(parse_filter_kind kt)
    #(parse_enum_key p e)
    (serialize_enum_key p s e)
    ()

noextract
let serialize32_sum_tac'
  (#kt: parser_kind)
  (t: sum)
  (tu: unit   { Cons? (sum_enum t) } )
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
    k' == and_then_kind (parse_filter_kind kt) k /\
    t' == sum_type t /\
    p' == parse_sum t p pc /\
    s' == serialize_sum t s sc
  })
: T.Tac T.term
= let st = quote t in
  let ar1 = serialize32_sum_tac_ar1 #kt t (sum_enum t) (* bidon_f (sum_enum t) *) () #p #s s32 #k #pc #sc sc32 u tag_of_data #k'  #t'  #p' s' u' in
  let ar2 = sum_destr_tac bytes32 t tu st in
  let fu = quote (
    serialize32_sum_gen
      #kt
      t
      #p
      s
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
  let res = T.mk_app fu [
    ar1, T.Q_Explicit;
    ar2, T.Q_Explicit;
  ]
  in
  res

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
= let f = serialize32_sum_tac' #kt t () #p #s s32 #k #pc #sc sc32 u tag_of_data s' u' in
  T.print (T.term_to_string f);
  T.exact_guard f

noextract
let serialize32_sum_tac_new
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
      u
      tag_of_data
      #k'
      #t'
      #p'
      s'
      u'
  )
  in
  T.apply fu;
  T.iseq [
    (fun () -> serialize32_enum_key_gen_tac_new #kt #(sum_key_type t) #(sum_repr_type t) #p #s s32 (sum_enum t) #(parse_filter_kind kt) #(parse_enum_key p (sum_enum t)) (serialize_enum_key p s (sum_enum t)) () ());
    (fun () -> sum_destr_tac_new bytes32 t ());
  ]

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
