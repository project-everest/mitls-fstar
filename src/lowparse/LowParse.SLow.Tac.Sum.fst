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
  (e: enum key repr { Cons? e } )
: Tot (T.tactic T.term)
= let open T in
  match e with
  | [_] ->
    q <-- quote (enum_destr_cons_nil #key #repr #t eq e ()) ;
    return q
  | _ ->
    assert (Cons? e /\ Cons? (enum_tail e));
    (fun (e_: enum key repr { Cons? e_ /\ Cons? (enum_tail e_) /\ e_ == e } ) ->
      ar <-- enum_destr_tac' t eq ifc u (enum_tail e_) ;
      fu <-- quote (enum_destr_cons #key #repr #t eq ifc e ()) ;
      return (mk_app fu [ar, Q_Explicit])
    ) e

(* Parser *)

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
: Tot (T.tactic T.term)
= let open T in
  ar1 <-- parse32_enum_key_tac' p32 (sum_enum t) (parse_enum_key p (sum_enum t)) () ;
  ar2 <--
    enum_destr_tac'
      (bytes32 -> Tot (option (sum_type t * U32.t)))
      (feq bytes32 (option (sum_type t * U32.t)) (eq2 #_))
      (fif _ _ (eq2 #_) (default_if _))
      ()
      (sum_enum t)
  ;
  fu <-- quote (
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
      ()
  ) ;
  return (mk_app fu [
    ar1, Q_Explicit;
    ar2, Q_Explicit;
  ])

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
: Tot (T.tactic unit)
= let open T in
  f <-- parse32_sum_tac' t p32 pc32 p' u ;
  exact_guard (return f)

noextract
let rec sum_destr_tac
  (v: Type)
  (s: sum { Cons? (sum_enum s) } )
: Tot (T.tactic T.term)
  (decreases (sum_enum s))
= let open T in
  match sum_enum s with
  | [_] ->
    t <-- quote (sum_destr_cons_nil v s ()) ;
    return t
  | _ ->
    let s' : sum = sum_tail s in
    assert (Cons? (sum_enum s')) ;
    let (s' : sum { Cons? (sum_enum s') } ) = s' in
    fu <-- quote (sum_destr_cons v s ()) ;
    ar <-- sum_destr_tac v s' ;
    return (mk_app fu [ar, Q_Explicit])

noextract
let serialize32_sum_tac'
  (#kt: parser_kind)
  (t: sum  { Cons? (sum_enum t) })
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p )
  (s32: serializer32 s)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == sum_tag_of_data t x} )))
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
: Tot (T.tactic T.term)
= let open T in
  let (e: enum (sum_key_type t) (sum_repr_type t) { Cons? e } ) = sum_enum t in
  ar1 <-- serialize32_enum_key_gen_tac'
    #kt
    #(sum_key_type t)
    #(sum_repr_type t)
    #p
    #s
    s32
    e
    #(parse_filter_kind kt)
    #(parse_enum_key p e)
    (serialize_enum_key p s e)
    ()
    ;
  ar2 <-- sum_destr_tac bytes32 t ;
  fu <-- quote (
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
  ) ;
  return (mk_app fu [
    ar1, Q_Explicit;
    ar2, Q_Explicit;
  ])

noextract
let serialize32_sum_tac
  (#kt: parser_kind)
  (t: sum  { Cons? (sum_enum t) })
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p )
  (s32: serializer32 s)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == sum_tag_of_data t x} )))
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
: Tot (T.tactic unit)
= let open T in
  f <-- serialize32_sum_tac' #kt t #p #s s32 #k #pc #sc sc32 u tag_of_data s' u' ;
  _ <-- print (term_to_string f) ;
  exact_guard (return f)
