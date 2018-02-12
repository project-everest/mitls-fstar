module LowParse.SLow.Tac.Enum
include LowParse.SLow.Enum

module T = FStar.Tactics

noextract
let rec maybe_enum_key_of_repr_tac'
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e } )
: Tot (T.tactic T.term)
= let open T in
  match e with
  | [_] ->
    q <-- quote (maybe_enum_key_of_repr'_t_cons_nil e ()) ;
    return q
  |  _ ->
    assert (Cons? e /\ Cons? (enum_tail e));
    (fun (e_ : enum key repr { Cons? e_ /\ Cons? (enum_tail e_) /\ e_ == e } ) ->
      ar <-- maybe_enum_key_of_repr_tac' (enum_tail e_) ;
      fu <-- quote (maybe_enum_key_of_repr'_t_cons #key #repr e_ ()) ;
      return (mk_app fu [ ar, Q_Explicit ])
    ) e

noextract
let rec maybe_enum_key_of_repr_tac
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e } )
: Tot (T.tactic unit)
= let open T in
  g <-- maybe_enum_key_of_repr_tac' e ;
  _ <-- print (term_to_string g) ;
  exact_guard (return g)

noextract
let rec enum_repr_of_key_tac'
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e } )
: Tot (T.tactic T.term)
= let open T in
  match e with
  | [_] ->
    q <-- quote (enum_repr_of_key_cons_nil e ()) ;
    return q
  | (k, r) :: e' ->
    assert (Cons? e);
    (fun (e_ : enum key repr { Cons? e_ /\ Cons? (enum_tail e_) /\ e_ == e } ) ->
      ar <-- enum_repr_of_key_tac' (enum_tail e_) ;
      fu <-- quote (enum_repr_of_key_cons #key #repr e_ ()) ;
      return (mk_app fu [ ar, Q_Explicit ] )
    ) e

noextract
let rec enum_repr_of_key_tac
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e } )
: Tot (T.tactic unit)
= let open T in
  g <-- enum_repr_of_key_tac' e ;
  exact_guard (return g)

noextract
let parse32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (p' : parser k' (maybe_enum_key e))
  (u: unit {
    k' == k /\
    p' == parse_maybe_enum_key p e
  })
: Tot (T.tactic unit)
= let open T in
  ar <-- maybe_enum_key_of_repr_tac' e ;
  fu <-- quote (parse32_maybe_enum_key_gen' #k #key #repr #p p32 e #k' p' u);
  exact_guard (return (mk_app fu [ar, Q_Explicit]))

noextract
let serialize32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (#p' : parser k' (maybe_enum_key e))
  (s' : serializer p')
  (u: unit {
    k == k' /\
    p' == parse_maybe_enum_key p e /\
    s' == serialize_maybe_enum_key p s e
  })
: Tot (T.tactic unit)
= let open T in
  ar <-- enum_repr_of_key_tac' e ;
  fu <-- quote (serialize32_maybe_enum_key_gen' #k #key #repr #p #s s32 e #k' #p' s' u) ;
  exact_guard (return (mk_app fu [ar, Q_Explicit]))
