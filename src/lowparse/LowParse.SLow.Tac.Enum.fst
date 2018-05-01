module LowParse.SLow.Tac.Enum
include LowParse.SLow.Enum

module T = FStar.Tactics

noextract
let rec maybe_enum_key_of_repr_tac'
  (#key #repr: eqtype)
  (e: enum key repr)
  (u: unit { Cons? e } )
  (et: T.term) // implicit invariant: et represents e
: T.Tac T.term
  (decreases e)
= match e with
  | [_] ->
    let fu = quote (maybe_enum_key_of_repr'_t_cons_nil #key #repr) in
    T.mk_app fu [
      et, T.Q_Explicit;
    ]
  |  _ ->
    assert (Cons? e /\ Cons? (enum_tail' e));
    (fun (e_ : enum key repr { Cons? e_ /\ Cons? (enum_tail' e_) /\ e_ == e } ) ->
      let (e' : enum key repr { Cons? e' } ) = enum_tail' e_ in
      let et'_fu = quote (enum_tail' #key #repr) in
      let et' = T.mk_app et'_fu [et, T.Q_Explicit] in
      let ar2 = maybe_enum_key_of_repr_tac' e' () et' in
      let fu = quote (maybe_enum_key_of_repr'_t_cons #key #repr) in
      (T.mk_app fu [
        et, T.Q_Explicit;
        ar2, T.Q_Explicit;
      ])
    ) e

noextract
let maybe_enum_key_of_repr_tac
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e } )
  ()
: T.Tac unit
= let et = quote e in
  let g = maybe_enum_key_of_repr_tac' e () et in
  T.print (T.term_to_string g) ;
  T.exact_guard g

noextract
let rec enum_repr_of_key_tac'
  (#key #repr: eqtype)
  (e: enum key repr)
  (u: unit  { Cons? e } )
  (et: T.term) // implicit invariant: et represents e
: T.Tac T.term
= match e with
  | [_] ->
    let fu = quote (enum_repr_of_key_cons_nil #key #repr) in
    T.mk_app fu [et, T.Q_Explicit]
  | (k, r) :: e' ->
    assert (Cons? e);
    (fun (e_ : enum key repr { Cons? e_ /\ Cons? (enum_tail' e_) /\ e_ == e } ) ->
      let (e' : enum key repr { Cons? e' } ) = enum_tail' e_ in
      let et'_fu = quote (enum_tail' #key #repr) in
      let et' = T.mk_app et'_fu [et, T.Q_Explicit] in
      let ar2 = enum_repr_of_key_tac' e' () et' in
      let fu = quote (enum_repr_of_key_cons #key #repr) in
      T.mk_app fu [
        et, T.Q_Explicit;
        ar2, T.Q_Explicit;
      ]
    ) e

noextract
let enum_repr_of_key_tac
  (#key #repr: eqtype)
  (e: enum key repr { Cons? e } )
  ()
: T.Tac unit
= let et = quote e in
  let g = enum_repr_of_key_tac' e () et in
  T.exact_guard g

noextract
let parse32_maybe_enum_key_tac'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
  (eu: unit { Cons? e } )
  (#k' : parser_kind)
  (p' : parser k' (maybe_enum_key e))
  (u: unit {
    k' == k /\
    p' == parse_maybe_enum_key p e
  })
: T.Tac T.term
= let et = quote e in
  let ar = maybe_enum_key_of_repr_tac' #key #repr e eu et in
  let fu = quote (parse32_maybe_enum_key_gen #k #key #repr #p p32 e #k' p' u) in
  T.mk_app fu [ar, T.Q_Explicit]

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
  ()
: T.Tac unit
= let f = parse32_maybe_enum_key_tac' p32 e () p' u in
  T.exact_guard f

noextract
let parse32_enum_key_tac'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
  (eu: unit { Cons? e } )
  (#k' : parser_kind)
  (p' : parser k' (enum_key e))
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e
  })
: T.Tac T.term
= let ar = parse32_maybe_enum_key_tac' p32 e eu (parse_maybe_enum_key p e) () in
  let fu = quote (parse32_enum_key_gen #k #key #repr p e #k' p' u) in
  T.mk_app fu [ar, T.Q_Explicit]

noextract
let parse32_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (p' : parser k' (enum_key e))
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e
  })
  ()
: T.Tac unit
= let f = parse32_enum_key_tac' p32 e () p' u in
  T.exact_guard f

noextract
let serialize32_enum_key_gen_tac'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (eu: unit { Cons? e })
  (#k' : parser_kind)
  (#p' : parser k' (enum_key e))
  (s' : serializer p')
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e /\
    s' == serialize_enum_key p s e
  })
: T.Tac T.term
= let et = quote e in
  T.print (T.term_to_string et);
  let ar = enum_repr_of_key_tac' e eu et in
  let fu = quote (serialize32_enum_key_gen #k #key #repr #p #s s32 e #k' #p' s' u) in
  T.mk_app fu [ar, T.Q_Explicit]

noextract
let serialize32_enum_key_gen_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (#p' : parser k' (enum_key e))
  (s' : serializer p')
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e /\
    s' == serialize_enum_key p s e
  })
  ()
: T.Tac unit
= let f = serialize32_enum_key_gen_tac' s32 e () s' u in
  T.exact_guard f

noextract
let serialize32_maybe_enum_key_tac'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (eu: unit { Cons? e } )
  (#k' : parser_kind)
  (#p' : parser k' (maybe_enum_key e))
  (s' : serializer p')
  (u: unit {
    k == k' /\
    p' == parse_maybe_enum_key p e /\
    s' == serialize_maybe_enum_key p s e
  })
: T.Tac T.term
= let et = quote e in
  let ar = enum_repr_of_key_tac' e eu et in
  let fu = quote (serialize32_maybe_enum_key_gen #k #key #repr #p #s s32 e #k' #p' s' u) in
  T.mk_app fu [ar, T.Q_Explicit]

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
  ()
: T.Tac unit
= let f = serialize32_maybe_enum_key_tac' s32 e () s' u in
  T.exact_guard f
