module LowParse.Spec.Enum
include LowParse.Spec.Combinators

module L = FStar.List.Tot

noeq
type norm_t : Type0 = | Norm

[@Norm]
let rec list_map
  (#a #b: Type)
  (f: (a -> Tot b))
  (l: list a)
: Tot (l' : list b { l' == L.map f l } )
= match l with
  | [] -> []
  | a :: q -> f a :: list_map f q

type enum (key: eqtype) (repr: eqtype) = (l: list (key * repr) {
  L.noRepeats (list_map fst l) /\
  L.noRepeats (list_map snd l)
})

[@Norm]
let rec list_mem
  (#t: eqtype)
  (x: t)
  (l: list t)
: Tot (y: bool { y == true <==> L.mem x l == true } )
= match l with
  | [] -> false
  | a :: q -> (x = a || list_mem x q)

let norm_spec
  (#t: Type)
  (x: t)
: Lemma
  (norm [delta_attr [`%Norm]; iota; zeta; primops] x == x)
= norm_spec [delta_attr [`%Norm]; iota; zeta; primops] x

inline_for_extraction
let enum_key (#key #repr: eqtype) (e: enum key repr) : Tot eqtype = (s: key { list_mem s (list_map fst e) } )

inline_for_extraction
let make_enum_key (#key #repr: eqtype) (e: enum key repr) (k: key) : Pure (enum_key e)
  (requires (list_mem k (list_map fst e)))
  (ensures (fun k' -> k == (k' <: key)))
= k

inline_for_extraction
let enum_repr (#key #repr: eqtype) (e: enum key repr) : Tot eqtype = (r: repr { list_mem r (list_map snd e) } )

let flip (#a #b: Type) (c: (a * b)) : Tot (b * a) = let (ca, cb) = c in (cb, ca)

let rec map_flip_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map flip (list_map flip l) == l)
= match l with
  | [] -> ()
  | _ :: q -> map_flip_flip q

let rec map_fst_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map fst (list_map flip l) == list_map snd l)
= match l with
  | [] -> ()
  | _ :: q -> map_fst_flip q

let rec map_snd_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map snd (list_map flip l) == list_map fst l)
= match l with
  | [] -> ()
  | _ :: q -> map_snd_flip q

let rec assoc_mem_snd
  (#a #b: eqtype)
  (l: list (a * b))
  (x: a)
  (y: b)
: Lemma
  (requires (L.assoc x l == Some y))
  (ensures (list_mem y (list_map snd l) == true))
  (decreases l)
= let ((x', y') :: l') = l in
  if x' = x
  then ()
  else assoc_mem_snd l' x y

let rec assoc_flip_elim
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (list_map fst l) /\
    L.noRepeats (list_map snd l) /\
    L.assoc y (list_map flip l) == Some x
  ))
  (ensures (
    L.assoc x l == Some y
  ))
  (decreases l)
= let ((x', y') :: l') = l in
  if y' = y
  then ()
  else begin
    if x' = x
    then begin
      assert (list_mem x' (list_map fst l') == false);
      assoc_mem_snd (list_map flip l') y x;
      map_snd_flip l';
      assert False
    end
    else
      assoc_flip_elim l' y x
  end

let rec assoc_flip_intro
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (list_map fst l) /\
    L.noRepeats (list_map snd l) /\
    L.assoc x l == Some y
  ))
  (ensures (
    L.assoc y (list_map flip l) == Some x
  ))
= map_fst_flip l;
  map_snd_flip l;
  map_flip_flip l;
  assoc_flip_elim (list_map flip l) x y

let enum_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Pure (enum_key e)
  (requires True)
  (ensures (fun y -> L.assoc y e == Some r))
= map_fst_flip e;
  let e' = list_map #(key * repr) #(repr * key) flip e in
  L.assoc_mem r e';
  let k = Some?.v (L.assoc r e') in
  assoc_flip_elim e r k;
  L.assoc_mem k e;
  (k <: enum_key e)

let parse_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
: Tot (parser (parse_filter_kind k) (enum_key e))
= (p
    `parse_filter`
    (fun (r: repr) -> list_mem r (list_map snd e))
  )
  `parse_synth`
  (fun (x: repr {list_mem x (list_map snd e) == true})  -> enum_key_of_repr e x)

let enum_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Pure (enum_repr e)
  (requires True)
  (ensures (fun r -> L.assoc k e == Some r))
= L.assoc_mem k e;
  let r = Some?.v (L.assoc k e) in
  assoc_flip_intro e r k;
  L.assoc_mem r (list_map flip e);
  map_fst_flip e;
  (r <: enum_repr e)

let enum_repr_of_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Lemma
  (enum_repr_of_key e (enum_key_of_repr e r) == r)
= ()

let enum_key_of_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Lemma
  (enum_key_of_repr e (enum_repr_of_key e k) == k)
= assoc_flip_intro e (enum_repr_of_key e k) k

let bare_serialize_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (bare_serializer (enum_key e))
= fun (k: enum_key e) -> s (enum_repr_of_key e k)

#set-options "--z3rlimit 32"

let bare_serialize_enum_key_correct
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Lemma
  (serializer_correct (parse_enum_key p e) (bare_serialize_enum_key p s e))
= Classical.forall_intro (enum_key_of_repr_of_key e)

#reset-options

let serialize_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (serializer (parse_enum_key p e))
= bare_serialize_enum_key_correct p s e;
  bare_serialize_enum_key p s e

inline_for_extraction
let unknown_enum_repr (#key #repr: eqtype) (e: enum key repr) : Tot Type0 =
  (r: repr { list_mem r (list_map snd e) == false } )

type maybe_enum_key (#key #repr: eqtype) (e: enum key repr) =
| Known of (enum_key e)
| Unknown of (unknown_enum_repr e)

let maybe_enum_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: repr)
: Tot (maybe_enum_key e)
= if list_mem r (list_map snd e)
  then Known (enum_key_of_repr e r)
  else Unknown r

let parse_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
: Tot (parser k (maybe_enum_key e))
= p `parse_synth` (maybe_enum_key_of_repr e)

let parse_maybe_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
  (input: bytes)
: Lemma
  (parse (parse_maybe_enum_key p e) input == (match parse p input with
  | Some (x, consumed) -> Some (maybe_enum_key_of_repr e x, consumed)
  | _ -> None
  ))
= ()

let parse_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
  (input: bytes)
: Lemma
  (parse (parse_enum_key p e) input == (match parse p input with
  | Some (x, consumed) ->
    begin match maybe_enum_key_of_repr e x with
    | Known k -> Some (k, consumed)
    | _ -> None
    end
  | _ -> None
  ))
= parse_filter_eq p (fun (r: repr) -> list_mem r (list_map snd e)) input;
  parse_synth_eq (p `parse_filter` (fun (r: repr) -> list_mem r (list_map snd e))) (fun (x: repr { list_mem x (list_map snd e) == true } ) -> enum_key_of_repr e x) input

let repr_of_maybe_enum_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (x: maybe_enum_key e)
: Tot (r: repr { maybe_enum_key_of_repr e r == x } )
= match x with
  | Known k' ->
    enum_key_of_repr_of_key e k' ;
    enum_repr_of_key e k'
  | Unknown r -> r

let serialize_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (serializer (parse_maybe_enum_key p e))
= serialize_synth p (maybe_enum_key_of_repr e) s (repr_of_maybe_enum_key e) ()

let is_total_enum (#key: eqtype) (#repr: eqtype) (l: list (key * repr)) : GTot Type0 =
  forall (k: key) . list_mem k (list_map fst l)

let total_enum (key: eqtype) (repr: eqtype) : Tot eqtype =
  (l: enum key repr { is_total_enum l } )

let synth_total_enum_key
  (#key: eqtype)
  (#repr: eqtype)
  (l: total_enum key repr)
  (k: enum_key l)
: Tot key
= let k' : key = k in
  k'

let parse_total_enum_key
  (#k: parser_kind)
  (#key: eqtype)
  (#repr: eqtype)
  (p: parser k repr)
  (l: total_enum key repr)
: Tot (parser (parse_filter_kind k) key)
= parse_enum_key p l `parse_synth` (synth_total_enum_key l)

let synth_total_enum_key_recip
  (#key: eqtype)
  (#repr: eqtype)
  (l: total_enum key repr)
  (k: key)
: Tot (k' : enum_key l { synth_total_enum_key l k' == k } )
= k

let serialize_total_enum_key
  (#k: parser_kind)
  (#key: eqtype)
  (#repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (l: total_enum key repr)
: Tot (serializer (parse_total_enum_key p l))
= serialize_synth (parse_enum_key p l) (synth_total_enum_key l) (serialize_enum_key p s l) (synth_total_enum_key_recip l) ()

type maybe_total_enum_key (#key #repr: eqtype) (e: total_enum key repr) =
| TotalKnown of key
| TotalUnknown of (unknown_enum_repr e)

let maybe_total_enum_key_of_repr
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (r: repr)
: Tot (maybe_total_enum_key e)
= if list_mem r (list_map snd e)
  then TotalKnown (enum_key_of_repr e r)
  else TotalUnknown r

let parse_maybe_total_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: total_enum key repr)
: Tot (parser k (maybe_total_enum_key e))
= p `parse_synth` (maybe_total_enum_key_of_repr e)

let repr_of_maybe_total_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_total_enum_key e)
: Tot (r: repr { maybe_total_enum_key_of_repr e r == k } )
= match k with
  | TotalKnown k' ->
    enum_key_of_repr_of_key e k' ;
    enum_repr_of_key e k'
  | TotalUnknown r -> r

let serialize_maybe_total_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: total_enum key repr)
: Tot (serializer (parse_maybe_total_enum_key p e))
= serialize_synth p (maybe_total_enum_key_of_repr e) s (repr_of_maybe_total_enum_key e) ()

inline_for_extraction
let maybe_enum_key_of_total
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_total_enum_key e)
: Tot (maybe_enum_key e)
= match k with
  | TotalKnown ek -> Known (ek <: key)
  | TotalUnknown r -> Unknown r

inline_for_extraction
let total_of_maybe_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_enum_key e)
: Tot (maybe_total_enum_key e)
= match k with
  | Known ek -> TotalKnown (ek <: key)
  | Unknown r -> TotalUnknown r

let maybe_total_enum_key_of_repr_eq
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (r: repr)
: Lemma
  (maybe_total_enum_key_of_repr e r == total_of_maybe_enum_key e (maybe_enum_key_of_repr e r))
= ()

let parse_maybe_total_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: total_enum key repr)
  (input: bytes)
: Lemma
  (parse (parse_maybe_total_enum_key p e) input == (parse (parse_maybe_enum_key p e `parse_synth` total_of_maybe_enum_key e) input))
= parse_synth_eq p (maybe_total_enum_key_of_repr e) input;
  parse_synth_eq (parse_maybe_enum_key p e) (total_of_maybe_enum_key e) input;
  parse_synth_eq p (maybe_enum_key_of_repr e) input

(* Destructors *)


(* Universal destructor *)

let r_reflexive_prop
  (t: Type)
  (r: (t -> t -> GTot Type0))
: GTot Type0
= forall (x: t) . r x x

inline_for_extraction
let r_reflexive_t
  (t: Type)
  (r: (t -> t -> GTot Type0))
: Tot Type0
= (x: t) -> Lemma (r x x)

let r_reflexive_t_elim
  (t: Type)
  (r: (t -> t -> GTot Type0))
  (phi: r_reflexive_t t r)
: Lemma
  (r_reflexive_prop t r)
= Classical.forall_intro phi

let r_transitive_prop
  (t: Type)
  (r: (t -> t -> GTot Type0))
: GTot Type0
= forall (x y z: t) . (r x y /\ r y z) ==> r x z

inline_for_extraction
let r_transitive_t
  (t: Type)
  (r: (t -> t -> GTot Type0))
: Tot Type0
= (x: t) -> (y: t) -> (z: t) -> Lemma ((r x y /\ r y z) ==> r x z)

let r_transitive_t_elim
  (t: Type)
  (r: (t -> t -> GTot Type0))
  (phi: r_transitive_t t r)
: Lemma
  (r_transitive_prop t r)
= Classical.forall_intro_3 phi

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
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
: Tot Type
= (eq: (t -> t -> GTot Type0)) ->
  (ift: if_combinator t eq) ->
  (eq_refl: r_reflexive_t _ eq) ->
  (eq_trans: r_transitive_t _ eq) ->
  (f: ((x: enum_key e) -> Tot t)) ->
  (x: enum_key e) ->
  Tot (y: t { eq y (f x) } )

inline_for_extraction
let enum_tail'
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum key repr)
  (requires True)
  (ensures (fun y -> Cons? e ==> (let (_ :: y') = e in y == y')))
= match e with _ :: y -> y | _ -> []

inline_for_extraction
let enum_tail
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (enum key repr)
= enum_tail' e

inline_for_extraction
let enum_destr_cons
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (g: enum_destr_t t (enum_tail' e))
: Pure (enum_destr_t t e)
  (requires (Cons? e))
  (ensures (fun _ -> True))
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  [@inline_let]
  let _ = r_transitive_t_elim _ _ eq_trans in
  (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, _) :: _ ->
     (fun (f: (enum_key e -> Tot t)) (x: enum_key e) -> ((
       [@inline_let]
       let f' : (enum_key (enum_tail' e) -> Tot t) =
         (fun (x' : enum_key (enum_tail' e)) ->
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
           let x' : enum_key (enum_tail' e) = (x <: key) in
           (g eq ift eq_refl eq_trans f' x' <: t))
       in
       y
     ) <: (y: t { eq y (f x) } )))
  ) e

inline_for_extraction
let enum_destr_cons'
  (t: Type)
  (key repr: eqtype)
  (e: enum key repr)
  (u: unit { Cons? e } )
  (g: enum_destr_t t (enum_tail e))
: Tot (enum_destr_t t e)
= enum_destr_cons t e g

inline_for_extraction
let enum_destr_cons_nil
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum_destr_t t e)
  (requires (Cons? e /\ Nil? (enum_tail' e)))
  (ensures (fun _ -> True))
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, _) :: _ ->
     (fun (f: (enum_key e -> Tot t)) (x: enum_key e) -> ((
       f k
     ) <: (y: t { eq y (f x) } )))
  ) e

inline_for_extraction
let enum_destr_cons_nil'
  (t: Type)
  (key repr: eqtype)
  (e: enum key repr)
  (u1: unit { Cons? e } )
  (u2: unit { Nil? (enum_tail e) } )
: Tot (enum_destr_t t e)
= enum_destr_cons_nil t e

(* Dependent destructor *)

inline_for_extraction
let dep_enum_destr
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (enum_key e -> Tot Type))
: Tot Type
= (v_eq: ((k: enum_key e) -> v k -> v k -> GTot Type0)) ->
  (v_if: ((k: enum_key e) -> Tot (if_combinator (v k) (v_eq k)))) ->
  (v_eq_refl: ((k: enum_key e) -> Tot (r_reflexive_t _ (v_eq k)))) ->
  (v_eq_trans: ((k: enum_key e) -> Tot (r_transitive_t _ (v_eq k)))) ->
  (f: ((k: enum_key e) -> Tot (v k))) ->
  (k: enum_key e) ->
  Tot (y: v k { v_eq k y (f k) } )

module L = FStar.List.Tot

inline_for_extraction
let dep_enum_destr_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (u: squash (Cons? e))
  (v: (enum_key e -> Tot Type))
  (destr: dep_enum_destr (enum_tail e) (fun (k' : enum_key (enum_tail e)) -> v (k' <: key)))
: Tot (dep_enum_destr e v)
= match e with
  | ((k, _) :: _) ->
    fun
    (v_eq: ((k: enum_key e) -> v k -> v k -> GTot Type0))
    (v_if: ((k: enum_key e) -> Tot (if_combinator (v k) (v_eq k))))
    (v_eq_refl: ((k: enum_key e) -> Tot (r_reflexive_t _ (v_eq k))))
    (v_eq_trans: ((k: enum_key e) -> Tot (r_transitive_t _ (v_eq k))))
    (f: ((k: enum_key e) -> Tot (v k)))
    (k' : enum_key e) ->
    [@inline_let]
    let _ = r_reflexive_t_elim (v k') (v_eq k') (v_eq_refl k') in
    [@inline_let]
    let _ = r_transitive_t_elim (v k') (v_eq k') (v_eq_trans k') in  
    [@inline_let]
    let y : v k' =
      v_if k' (k = k') (fun _ ->
        [@inline_let]
        let y : v k' = f k in
        y
      ) (fun _ ->
        [@inline_let]
        let v' (k: enum_key (enum_tail e)) : Tot Type = v (k <: key) in
        [@inline_let]
        let v'_eq (k: enum_key (enum_tail e)) : Tot (v' k -> v' k -> GTot Type0) = v_eq (k <: key) in
        [@inline_let]
        let v'_if (k: enum_key (enum_tail e)) : Tot (if_combinator (v' k) (v'_eq k)) = v_if (k <: key) in
        [@inline_let]
        let v'_eq_refl (k: enum_key (enum_tail e)) : Tot (r_reflexive_t _ (v'_eq k)) = v_eq_refl (k <: key) in
        [@inline_let]
        let v'_eq_trans (k: enum_key (enum_tail e)) : Tot (r_transitive_t _ (v'_eq k)) = v_eq_trans (k <: key) in
        [@inline_let]
        let f' (k: enum_key (enum_tail e)) : Tot (v' k) = f (k <: key) in
        [@inline_let]
        let k' : key = k' in
        assert (k' <> k);
        assert (L.mem k' (L.map fst (enum_tail e)));
        [@inline_let]
        let (y: v' k') =
          destr v'_eq v'_if v'_eq_refl v'_eq_trans f' k'
        in
        y
      )
    in
    (y <: (y: v k' { v_eq k' y (f k') } ))

inline_for_extraction
let dep_enum_destr_cons_nil
  (#key #repr: eqtype)
  (e: enum key repr)
  (u: squash (Cons? e /\ Nil? (enum_tail e)))
  (v: (enum_key e -> Tot Type))
: Tot (dep_enum_destr e v)
= match e with
  | ((k, _) :: _) ->
    fun
    (v_eq: ((k: enum_key e) -> v k -> v k -> GTot Type0))
    (v_if: ((k: enum_key e) -> Tot (if_combinator (v k) (v_eq k))))
    (v_eq_refl: ((k: enum_key e) -> Tot (r_reflexive_t _ (v_eq k))))
    (v_eq_trans: ((k: enum_key e) -> Tot (r_transitive_t _ (v_eq k))))
    (f: ((k: enum_key e) -> Tot (v k)))
    (k' : enum_key e) ->
    [@inline_let]
    let _ = r_reflexive_t_elim (v k') (v_eq k') (v_eq_refl k') in
    [@inline_let]
    let _ = r_transitive_t_elim (v k') (v_eq k') (v_eq_trans k') in  
    [@inline_let]
    let y : v k' = f k in
    (y <: (y: v k' { v_eq k' y (f k') } ))

(* Destructor from the representation *)


let maybe_enum_key_of_repr_not_in (#key #repr: eqtype) (e: enum key repr) (l: list (key * repr)) (x: repr) : GTot Type0 =
  (~ (L.mem x (L.map snd l)))

let list_rev_cons
  (#t: Type)
  (a: t)
  (q: list t)
: Lemma
  (L.rev (a :: q) == L.rev q `L.append` [a])
= L.rev_rev' (a :: q);
  L.rev_rev' q

let list_append_rev_cons (#t: Type) (l1: list t) (x: t) (l2: list t) : Lemma
  (L.append (L.rev l1) (x :: l2) == L.append (L.rev (x :: l1)) l2)
= list_rev_cons x l1;
  L.append_assoc (L.rev l1) [x] l2

let rec assoc_append_flip_l_intro
  (#key #repr: eqtype)
  (l1 l2: list (key * repr))
  (y: repr)
  (x: key)
: Lemma
  (requires (L.noRepeats (L.map snd (L.append l1 l2)) /\ L.assoc y (L.map flip l2) == Some x))
  (ensures (L.assoc y (L.map flip (l1 `L.append` l2)) == Some x))
= match l1 with
  | [] -> ()
  | (_, r') :: q ->
    L.assoc_mem y (L.map flip l2);
    map_fst_flip l2;
    L.map_append snd l1 l2;
    L.noRepeats_append_elim (L.map snd l1) (L.map snd l2);
    assoc_append_flip_l_intro q l2 y x

inline_for_extraction
let maybe_enum_destr_t'
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
  (l1 l2: list (key * repr))
  (u1: squash (e == L.append (L.rev l1) l2))
: Tot Type
= (eq: (t -> t -> GTot Type0)) ->
  (ift: if_combinator t eq) ->
  (eq_refl: r_reflexive_t _ eq) ->
  (eq_trans: r_transitive_t _ eq) ->
  (f: ((x: maybe_enum_key e) -> Tot t)) ->
  (x: repr { maybe_enum_key_of_repr_not_in e l1 x } ) ->
  Tot (y: t { eq y (f (maybe_enum_key_of_repr e x)) } )

inline_for_extraction
let maybe_enum_destr_t
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
: Tot Type
= (eq: (t -> t -> GTot Type0)) ->
  (ift: if_combinator t eq) ->
  (eq_refl: r_reflexive_t _ eq) ->
  (eq_trans: r_transitive_t _ eq) ->
  (f: ((x: maybe_enum_key e) -> Tot t)) ->
  (x: repr) ->
  Tot (y: t { eq y (f (maybe_enum_key_of_repr e x)) } )

inline_for_extraction
let destr_maybe_total_enum_repr
  (#t: Type)
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (destr: maybe_enum_destr_t t e)
  (eq: (t -> t -> GTot Type0))
  (ift: if_combinator t eq)
  (eq_refl: r_reflexive_t _ eq)
  (eq_trans: r_transitive_t _ eq)
  (f: ((x: maybe_total_enum_key e) -> Tot t))
  (x: repr)
: Tot (y: t { eq y (f (maybe_total_enum_key_of_repr e x)) } )
= destr eq ift eq_refl eq_trans (fun y -> f (total_of_maybe_enum_key e y)) x

inline_for_extraction
let maybe_enum_destr_t_intro
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
  (f: maybe_enum_destr_t' t e [] e ())
: Tot (maybe_enum_destr_t t e)
= f

let maybe_enum_key_of_repr_not_in_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: key)
  (r: repr)
  (l: list (key * repr))
  (x: repr)
: Lemma
  (requires (maybe_enum_key_of_repr_not_in e l x /\ x <> r))
  (ensures (maybe_enum_key_of_repr_not_in e ((k, r) :: l) x))
= ()

inline_for_extraction
let list_hd
  (#t: Type)
  (l: list t { Cons? l } )
= match l with
  | a :: _ -> a

inline_for_extraction
let list_tl
  (#t: Type)
  (l: list t { Cons? l } )
= match l with
  | _ :: q -> q

inline_for_extraction
let maybe_enum_destr_cons
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u1: squash (Cons? l2 /\ e == L.append (L.rev l1) l2))
  (g: (maybe_enum_destr_t' t e (list_hd l2 :: l1) (list_tl l2) (list_append_rev_cons l1 (list_hd l2) (list_tl l2))))
: Tot (maybe_enum_destr_t' t e l1 l2 u1)
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) (f: (maybe_enum_key e -> Tot t)) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  [@inline_let]
  let _ = r_transitive_t_elim _ _ eq_trans in
  match list_hd l2 with
  | (k, r) ->
  [@inline_let]
  let _ : squash (L.mem k (L.map fst e)) =
    L.append_mem (L.map fst (L.rev l1)) (L.map fst l2) k;
    L.map_append fst (L.rev l1) (l2);
    ()
  in
  [@inline_let]
  let (_ : squash (maybe_enum_key_of_repr e r == Known k)) =
    L.append_mem (L.map snd (L.rev l1)) (L.map snd (l2)) r;
    L.map_append snd (L.rev l1) (l2);
    assoc_append_flip_l_intro (L.rev l1) (l2) r k;
    ()
  in
  fun (x: repr { maybe_enum_key_of_repr_not_in e l1 x } ) -> ((
    ift
      (x = r)
      (fun h -> f (Known k))
      (fun h -> g eq ift eq_refl eq_trans f x)
  ) <: (y: t { eq y (f (maybe_enum_key_of_repr e x)) } ))

let rec list_rev_map
  (#t1 #t2: Type)
  (f: t1 -> Tot t2)
  (l: list t1)
: Lemma
  (L.rev (L.map f l) == L.map f (L.rev l))
= match l with
  | [] -> ()
  | a :: q ->
    list_rev_cons a q;
    list_rev_cons (f a) (L.map f q);
    list_rev_map f q;
    L.map_append f (L.rev q) [a]

inline_for_extraction
let maybe_enum_destr_nil
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u1: squash (Nil? l2 /\ e == L.append (L.rev l1) []))
: Tot (maybe_enum_destr_t' t e l1 l2 u1)
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) (f: (maybe_enum_key e -> Tot t)) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  [@inline_let]
  let _ = r_transitive_t_elim _ _ eq_trans in
  fun (x: repr { maybe_enum_key_of_repr_not_in e l1 x } ) -> ((
    L.append_l_nil (L.rev l1);
    list_rev_map snd l1;
    L.rev_mem (L.map snd l1) x;
    f (Unknown x)
  ) <: (y: t { eq y (f (maybe_enum_key_of_repr e x)) } ))
