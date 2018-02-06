module LowParse.SLow.Enum
include LowParse.Spec.Enum
include LowParse.SLow.Combinators

module L = FStar.List.Tot
module U32 = FStar.UInt32
module T = FStar.Tactics

(* Parser for enums *)

let maybe_enum_key_of_repr'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type0
= (x: repr) ->
  Tot (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )

let rec maybe_enum_key_of_repr'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (maybe_enum_key_of_repr'_t e)
= match e with
  | [] -> (fun x -> ((Unknown x) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )))
  | (k, r) :: e' ->
    let f = maybe_enum_key_of_repr' e' in
    (fun x -> ((
      if x = r
      then Known k
      else match f x with
      | Known k' -> Known (k' <: key)
      | Unknown _ -> Unknown x
    ) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )))

#set-options "--z3rlimit 32"

let enum_tail
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum key repr)
  (requires (Cons? e))
  (ensures (fun y -> Cons? e /\ (let (_ :: y') = e in y == y')))
= let (_ :: y) = e in
  y

let rec maybe_enum_key_of_repr_tac'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (T.tactic (maybe_enum_key_of_repr'_t e))
= let open T in
  match e with
  | [] ->
    return (fun x -> ((Unknown x) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )))
  | (k, r) :: _ ->
    assert (Cons? e);
    let e' = enum_tail #key #repr e in
    g <-- maybe_enum_key_of_repr_tac' e' ;
    return
      (fun x -> ((
        if x = r
        then Known k
        else match g x with
        | Known k' -> Known (k' <: key)
        | Unknown _ -> Unknown x
      ) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )))

#reset-options

inline_for_extraction
let parse32_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (parser32 (parse_maybe_enum_key p e))
= parse32_synth p (maybe_enum_key_of_repr e) (maybe_enum_key_of_repr' e) p32 ()

let parse32_maybe_enum_key_tac'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (T.tactic (parser32 (parse_maybe_enum_key p e)))
= let open T in
  f <-- maybe_enum_key_of_repr_tac' e ;
  return (parse32_synth p (maybe_enum_key_of_repr e) f p32 ())

let parse32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (T.tactic unit)
= let open T in
  f <-- parse32_maybe_enum_key_tac' p32 e ;
  g <-- quote f ;
  exact (return g)

#set-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8"

inline_for_extraction
let parse32_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (e: enum key repr)
  (pe: parser32 (parse_maybe_enum_key p e))
: Tot (parser32 (parse_enum_key p e))
= (fun (input: bytes32) -> ((
    match pe input with
    | Some (k, consumed) ->
      begin match k with
      | Known k' -> Some (k', consumed)
      | _ -> None
      end
    | _ -> None
  ) <: (res: option (enum_key e * U32.t) { parser32_correct (parse_enum_key p e) input res } )))

inline_for_extraction
let parse32_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (parser32 (parse_enum_key p e))
= parse32_enum_key_gen e (parse32_maybe_enum_key p32 e)

let parse32_enum_key_tac'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (T.tactic (parser32 (parse_enum_key p e)))
= let open T in
  f <-- parse32_maybe_enum_key_tac' p32 e ;
  return (parse32_enum_key_gen e f)

let parse32_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (T.tactic unit)
= let open T in
  f <-- parse32_enum_key_tac' p32 e ;
  g <-- quote f ;
  exact (return g)

#reset-options

let enum_repr_of_key'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type0
= (x: enum_key e) ->
  Tot (r: enum_repr e { r == enum_repr_of_key e x } )

let rec enum_repr_of_key'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (enum_repr_of_key'_t e)
= match e with
  | [] -> (fun (x: enum_key e) -> ((false_elim ()) <: (r: enum_repr e { enum_repr_of_key e x == r } )))
  | (k, r) :: _ ->
    let f = enum_repr_of_key' (enum_tail e) in
    (fun (x: enum_key e) -> (
      if x = k
      then r
      else (f (x <: key) <: repr)
    ) <: (r: enum_repr e { enum_repr_of_key e x == r } ))

inline_for_extraction
let serialize32_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (f: enum_repr_of_key'_t e)
: Tot (serializer32 (serialize_enum_key p s e))
= fun (input: enum_key e) -> ((s32 (f input)) <: (r: bytes32 { serializer32_correct (serialize_enum_key p s e) input r } ))

inline_for_extraction
let serialize32_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (f: enum_repr_of_key'_t e)
: Tot (serializer32 (serialize_enum_key p s e))
= serialize32_enum_key_gen s32 e (enum_repr_of_key' e)

inline_for_extraction
let enum_repr_of_key_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: key)
  (r: repr)
  (e' : enum key repr { e == (k, r) :: e' } )
  (f : enum_repr_of_key'_t e')
: Tot (enum_repr_of_key'_t e)
= (fun (x: enum_key e) -> (
      if x = k
      then (r <: repr)
      else (f (x <: key) <: repr)
  ) <: (r: enum_repr e { enum_repr_of_key e x == r } ))

let rec enum_repr_of_key_tac'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (T.tactic (enum_repr_of_key'_t e))
= let open T in
  match e with
  | [] -> return (fun (x: enum_key e) -> ((false_elim ()) <: (r: enum_repr e { enum_repr_of_key e x == r } )))
  | (k, r) :: _ ->
    let e' = enum_tail e in
    f <-- enum_repr_of_key_tac' e' ;
    return (enum_repr_of_key_cons e k r e' f )

let serialize32_enum_key_tac'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
: Tot (T.tactic (serializer32 (serialize_enum_key p s e)))
= let open T in
  f <-- enum_repr_of_key_tac' e ;
  return (serialize32_enum_key_gen s32 e f)

let serialize32_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
: Tot (T.tactic unit)
= let open T in
  f <-- serialize32_enum_key_tac' s32 e ;
  g <-- quote f ;
  exact (return g)


(*
inline_for_extraction
let maybe_enum_repr_of_key'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot


  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  
