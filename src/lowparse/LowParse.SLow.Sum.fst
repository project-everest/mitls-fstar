module LowParse.SLow.Sum
include LowParse.Spec.Sum
include LowParse.SLow.Enum

module B32 = LowParse.Bytes32
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

inline_for_extraction
let parse32_sum_t (t: sum) : Tot Type =
  bytes32 -> Tot (option (sum_type t * U32.t))

let parse32_sum_eq (t: sum) : Tot (parse32_sum_t t -> parse32_sum_t t -> GTot Type0) =
  feq _ _ (eq2 #_)

inline_for_extraction
let parse32_sum_if (t: sum) : Tot (if_combinator _ (parse32_sum_eq t)) =
  fif _ _ _ (default_if _)

let parse32_sum_eq_refl (t: sum) : Tot (r_reflexive_t _ (parse32_sum_eq t)) =
  fun _ -> ()

let parse32_sum_eq_trans (t: sum) : Tot (r_transitive_t _ (parse32_sum_eq t)) =
  fun _ _ _ -> ()

let parse32_sum_aux
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (dsnd (pc x)))))
: GTot (parser32 (parse_sum t p pc))
= fun input ->
  parse_sum_eq' t p pc (B32.reveal input);
  [@inline_let]
  let res : option (sum_type t * U32.t) =
    match p32 input with
    | None -> None
    | Some (k, consumed_k) ->
      begin
        let input_k = B32.b32slice input consumed_k (B32.len input) in
        synth_sum_case_injective t k;
        match
          parse32_synth'
            (dsnd (pc k))
            (synth_sum_case t k)
            (pc32 k)
            ()
            input_k
        with
        | None -> None
        | Some (x, consumed_x) -> Some ((x <: sum_type t), consumed_k `U32.add` consumed_x)
      end
  in
  (res <: (res: option (sum_type t * U32.t) { parser32_correct (parse_sum t p pc) input res } ))

#set-options "--z3rlimit 32"

inline_for_extraction
let parse32_sum'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (dsnd (pc x)))))
  (destr: enum_destr_t (option (sum_type t * U32.t)) (sum_enum t))
  (input: B32.bytes)
: Pure (option (sum_type t * U32.t))
  (requires True)
  (ensures (fun res -> res == parse32_sum_aux t p p32 pc pc32 input))
= [@inline_let]
  let res : option (sum_type t * U32.t) =
    match p32 input with
    | None -> None
    | Some (k, consumed_k) ->
      let input_k = B32.b32slice input consumed_k (B32.len input) in
      synth_sum_case_injective t k;
      [@inline_let]
      let f
        (k: sum_key t)
      : Tot (option (sum_type t * U32.t))
      = synth_sum_case_injective t k;
        parse32_synth'
          (dsnd (pc k))
          (synth_sum_case t k)
          (pc32 k)
          ()
          input_k
      in
      [@inline_let]
      let f_prop
        (k: sum_key t)
      : Lemma
        (match f k with
          | None -> True
          | Some (_, consumed_x) ->
            FStar.UInt.size (U32.v consumed_k + U32.v consumed_x) 32
        )
      = match f k with
        | None -> ()
        | Some (_, consumed_x) ->
          assert (U32.v consumed_k + U32.v consumed_x <= B32.length input)
      in
      [@inline_let]
      let j : option (sum_type t * U32.t) = destr (eq2 #(option (sum_type t * U32.t))) (default_if _) (fun _ -> ()) (fun _ _ _ -> ()) (fun k -> f k) k in
      [@inline_let]
      let _ : squash (j == f k) = assert (j == f k) in
      [@inline_let]
      let _ = f_prop k in
      begin match j with
      | None -> None
      | Some (x, consumed_x) ->
        Some (x, consumed_k `U32.add` consumed_x)
      end
  in
  res

#reset-options

inline_for_extraction
let parse32_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (dsnd (pc x)))))
  (destr: enum_destr_t (option (sum_type t * U32.t)) (sum_enum t))
: Tot (parser32 (parse_sum t p pc))
= fun input ->
  (parse32_sum' t p p32 pc pc32 destr input <: (res: option (sum_type t * U32.t) { parser32_correct (parse_sum t p pc) input res } ))

(*
inline_for_extraction
let enum_head_key
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum_key e)
  (requires (Cons? e))
  (ensures (fun y -> Cons? e /\ (let ((k, _) :: _) = e in (y <: key) == k)))
= match e with ((k, _) :: _) -> k

inline_for_extraction
unfold
let sum_tail_type
  (t: sum)
: Tot Type0
= (x: sum_type t { Cons? (sum_enum t) /\ sum_tag_of_data t x <> enum_head_key (sum_enum t) } )

let sum_tail_tag_of_data
  (t: sum)
  (x: sum_tail_type t)
: Ghost (enum_key (enum_tail' (sum_enum t)))
  (requires (Cons? (sum_enum t)))
  (ensures (fun _ -> True))
= let y : sum_key_type t = sum_tag_of_data t x in
  y

inline_for_extraction
let sum_tail
  (t: sum)
: Pure sum
  (requires True)
  (ensures (fun t' ->
    Cons? (sum_enum t) ==> (
    sum_key_type t' == sum_key_type t /\
    sum_repr_type t' == sum_repr_type t /\
    (sum_enum t' <: enum (sum_key_type t) (sum_repr_type t)) == enum_tail' (sum_enum t) /\
    sum_type t' == sum_tail_type t /\
    (forall (x : sum_tail_type t) . (sum_tag_of_data t' (coerce' (sum_type t') x) <: sum_key_type t) == (sum_tag_of_data t (x <: sum_type t) <: sum_key_type t))
  )))
= Sum
    (sum_key_type t)
    (sum_repr_type t)
    (enum_tail' (sum_enum t))
    (sum_tail_type t)
    (sum_tail_tag_of_data t)

inline_for_extraction
let sum_destr
  (t: sum)
: Tot Type
= (v: Type) ->
  (f: ((k: sum_key t) -> (x: refine_with_tag (sum_tag_of_data t) k) -> Tot v)) ->
  (k: sum_key t) ->
  (x: refine_with_tag (sum_tag_of_data t) k) ->
  Tot (y: v { y == f k x } )

inline_for_extraction
let sum_destr_cons
  (t: sum)
  (destr: sum_destr (sum_tail t))
: Pure (sum_destr t)
  (requires (Cons? (sum_enum t)))
  (ensures (fun _ -> True))
= fun v ->
  match sum_enum t with
  | ((k, _) :: _) ->
    fun 
      (f: ((k: sum_key t) -> (x: refine_with_tag (sum_tag_of_data t) k) -> Tot v))
      (k' : sum_key t)
      (x' : refine_with_tag (sum_tag_of_data t) k')
    -> ((
      if (k <: sum_key_type t) = (k' <: sum_key_type t)
      then (f k x' <: v)
      else
        [@inline_let]
        let x_ : sum_type t = x' in
        (destr _ (fun k x -> f (k <: sum_key_type t) (x <: sum_type t)) (k' <: sum_key_type t) x_ <: v)
    ) <: (y: v {y == f k' x' } ))

inline_for_extraction
let sum_destr_cons'
  (t: sum)
  (u: unit { Cons? (sum_enum t)} )
  (destr: sum_destr (sum_tail t))
: Tot (sum_destr t)
= sum_destr_cons t destr

inline_for_extraction
let sum_destr_cons_nil
  (t: sum)
: Pure (sum_destr t)
  (requires (Cons? (sum_enum t) /\ Nil? (enum_tail' (sum_enum t))))
  (ensures (fun _ -> True))
= fun v ->
  match sum_enum t with
  | ((k, _) :: _) ->
    fun 
      (f: ((k: sum_key t) -> (x: refine_with_tag (sum_tag_of_data t) k) -> Tot v))
      (k' : sum_key t)
      (x' : refine_with_tag (sum_tag_of_data t) k')
    ->
      (f k x' <: (y: v { y == f k' x' } ))

inline_for_extraction
let sum_destr_cons_nil'
  (t: sum)
  (u1: unit { Cons? (sum_enum t) } )
  (u2: unit { Nil? (enum_tail' (sum_enum t)) } )
: Tot (sum_destr t)
= sum_destr_cons_nil t

inline_for_extraction
let serialize32_sum_gen
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (serializer32 (sc x))))
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == (sum_tag_of_data t x <: sum_key_type t)} )))
  (k' : parser_kind)
  (t' : Type0)
  (p' : parser k' t')
  (s' : serializer p')
  (u1: unit {
    kt.parser_kind_subkind == Some ParserStrong
  })
  (u2: unit {
    match kt.parser_kind_high, k.parser_kind_high with
    | Some vt, Some v -> vt + v < 4294967296
    | _ -> False
  })
  (u3: unit {
    k' == and_then_kind (parse_filter_kind kt) k
  })
  (u4: unit {
    t' == sum_type t
  })
  (u5: unit {
    p' == parse_sum t p pc
  })
  (u6: unit {
    s' == serialize_sum t s sc
  })
  (s32: serializer32 (serialize_enum_key _ s (sum_enum t)))
  (destr: sum_destr t)
: Tot (serializer32 s')
= [@inline_let]
  let sc32' (k: sum_key t) : Tot (serializer32 (sc k)) =
    (fun (x: refine_with_tag (sum_tag_of_data t) k) -> destr bytes32 sc32 k x)
  in
  (serialize32_sum_gen' t s32 sc32' () tag_of_data <: serializer32 s')

inline_for_extraction
let parse32_sum_cases
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (dsnd (pc x)))))
  (x: sum_key t)
: Tot (parser32 (parse_sum_cases t pc x))
= (fun input -> pc32 x input)

inline_for_extraction
let serialize32_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_cases s x)))
  (sr: (x: sum_key s) -> Tot (serializer (dsnd (f x))))
  (sr32: (x: sum_key s) -> Tot (serializer32 (sr x)))
  (x: sum_key s)
: Tot (serializer32 (serialize_sum_cases s f sr x))
= (fun input -> sr32 x input)

inline_for_extraction
let size32_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_cases s x)))
  (sr: (x: sum_key s) -> Tot (serializer (dsnd (f x))))
  (sr32: (x: sum_key s) -> Tot (size32 (sr x)))
  (x: sum_key s)
: Tot (size32 (serialize_sum_cases s f sr x))
= (fun input -> sr32 x input)

#set-options "--z3rlimit 16"

inline_for_extraction
let size32_sum_gen'
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p)
  (s32: size32 (serialize_enum_key _ s (sum_enum t)))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (size32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == (sum_tag_of_data t x <: sum_key_type t) } )))
: Tot (size32 (serialize_sum t s sc))
= fun (input: sum_type t) -> ((
    let tg = tag_of_data input in
    let stg = s32 tg in
    let s = sc32 tg input in
    U32.add stg s
  ) <: (res: U32.t { size32_postcond (serialize_sum t s sc) input res } ))

#reset-options

inline_for_extraction
let size32_sum_gen
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (#s: serializer p)
  (s32: size32 (serialize_enum_key _ s (sum_enum t)))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (#sc: ((x: sum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: sum_key t) -> Tot (size32 (sc x))))
  (u0: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: sum_type t) -> Tot (y: sum_key_type t { y == (sum_tag_of_data t x <: sum_key_type t) } )))
  (k' : parser_kind)
  (t' : Type0)
  (p' : parser k' t')
  (s' : serializer p')
  (u1: unit {
    k' == and_then_kind (parse_filter_kind kt) k /\
    t' == sum_type t /\
    p' == parse_sum t p pc /\
    s' == serialize_sum t s sc
  })
  (destr: sum_destr t)
: Tot (size32 s')
= [@inline_let]
  let sc32' (k: sum_key t) : Tot (size32 (sc k)) =
    (fun (x: refine_with_tag (sum_tag_of_data t) k) -> destr U32.t sc32 k x)
  in
  (size32_sum_gen' t s32 sc32' () tag_of_data <: size32 s')

(* Sum with default case *)
*)

module L = FStar.List.Tot

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
let maybe_enum_destr_cons
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (l1: list (key * repr))
  (x: key * repr)
  (l2: list (key * repr))
  (u1: squash (e == L.append (L.rev l1) (x :: l2)))
  (g: (maybe_enum_destr_t' t e (x :: l1) (l2) (list_append_rev_cons l1 (x) (l2))))
: Tot (maybe_enum_destr_t' t e l1 (x :: l2) u1)
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) (f: (maybe_enum_key e -> Tot t)) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  [@inline_let]
  let _ = r_transitive_t_elim _ _ eq_trans in
  match x with
  | (k, r) ->
  [@inline_let]
  let _ : squash (L.mem k (L.map fst e)) =
    L.append_mem (L.map fst (L.rev l1)) (L.map fst (x :: l2)) k;
    L.map_append fst (L.rev l1) (x :: l2);
    ()
  in
  [@inline_let]
  let (_ : squash (maybe_enum_key_of_repr e r == Known k)) =
    L.append_mem (L.map snd (L.rev l1)) (L.map snd (x :: l2)) r;
    L.map_append snd (L.rev l1) (x :: l2);
    assoc_append_flip_l_intro (L.rev l1) (x :: l2) r k;
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
  (u1: squash (e == L.append (L.rev l1) []))
: Tot (maybe_enum_destr_t' t e l1 [] u1)
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

(*
inline_for_extraction
let parse32_dsum_t (t: dsum) : Tot Type =
  bytes32 -> Tot (option (dsum_type t * U32.t))

let parse32_dsum_eq (t: dsum) : Tot (parse32_dsum_t t -> parse32_dsum_t t -> GTot Type0) =
  feq _ _ (eq2 #_)

inline_for_extraction
let parse32_dsum_if (t: dsum) : Tot (if_combinator _ (parse32_dsum_eq t)) =
  fif _ _ _ (default_if _)

let parse32_dsum_eq_refl (t: dsum) : Tot (r_reflexive_t _ (parse32_dsum_eq t)) =
  fun _ -> ()

let parse32_dsum_eq_trans (t: dsum) : Tot (r_transitive_t _ (parse32_dsum_eq t)) =
  fun _ _ _ -> ()

#set-options "--z3rlimit 64"

inline_for_extraction
let parse32_dsum_gen
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (p32: parser32 p)
  (#k: parser_kind)
  (pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (pc32: ((x: dsum_key t) -> Tot (parser32 (pc x))))
  (destr: maybe_enum_destr_t (B32.bytes -> Tot (option (dsum_type t * U32.t)) ) (dsum_enum t))
: Tot (parser32 (parse_dsum t p pc))
= fun input -> ((
  parse_dsum_eq t p pc (B32.reveal input);
  parse_maybe_enum_key_eq p (dsum_enum t) (B32.reveal input);
  match p32 input with
  | None -> None
  | Some (r, consumed_k) ->
    let input_k = B32.slice input consumed_k (B32.len input) in
    begin match destr _ (parse32_dsum_if t) (parse32_dsum_eq_refl t) (parse32_dsum_eq_trans t) (fun (x: dsum_key t) (input: bytes32) -> match pc32 x input with | Some (d, consumed_d) -> Some ((d <: dsum_type t), consumed_d) | _ -> None) r input_k with
    | Some (d, consumed_d) ->
      Some (d, U32.add consumed_k consumed_d)
    | _ -> None
    end
  ) <: (res: option (dsum_type t * U32.t) { parser32_correct (parse_dsum t p pc) input res }))

#reset-options


inline_for_extraction
let serialize32_dsum_gen
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (#s: serializer p)
  (s32: serializer32 (serialize_maybe_enum_key _ s (dsum_enum t)))
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (#sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (sc32: ((x: dsum_key t) -> Tot (serializer32 (sc x))))
  (u: unit { serializer32_sum_gen_precond kt k } )
  (tag_of_data: ((x: dsum_type t) -> Tot (y: dsum_key t  { y == (dsum_tag_of_data t x <: dsum_key t)}  )))
: Tot (serializer32 (serialize_dsum t s sc))
= fun (input: dsum_type t) -> ((
    let tg = tag_of_data input in
    let stg = s32 tg in
    let s = sc32 tg input in
    B32.b32append stg s
  ) <: (res: bytes32 { serializer32_correct (serialize_dsum t s sc) input res } ))

inline_for_extraction
let parse32_dsum_cases
  (t: dsum)
  (pc: ((x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_cases t (Known x)))))
  (pc32: ((x: dsum_known_key t) -> Tot (parser32 (dsnd (pc x)))))
  (#k: parser_kind)
  (pd: ((x: dsum_unknown_key t) -> Tot (parser k (dsum_cases t (Unknown x)))))
  (pd32: ((x: dsum_unknown_key t) -> Tot (parser32 (pd x))))
  (x: dsum_key t)
: Tot (parser32 (parse_dsum_cases t pc pd x))
= match x with
  | Known x -> (fun input -> pc32 x input)
  | Unknown x -> (fun input -> pd32 x input)

(* TODO: swap match and fun as above *)

inline_for_extraction
let size32_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_cases s (Known x))))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (sr32: (x: dsum_known_key s) -> Tot (size32 (sr x)))
  (#k: parser_kind)
  (g: (x: dsum_unknown_key s) -> Tot (parser k (dsum_cases s (Unknown x))))
  (sg: (x: dsum_unknown_key s) -> Tot (serializer (g x)))
  (sg32: (x: dsum_unknown_key s) -> Tot (size32 (sg x)))
  (x: dsum_key s)
: Tot (size32 (serialize_dsum_cases s f sr g sg x))
= match x with
  | Known x ->
    (fun input -> sr32 x input)
  | Unknown x ->
    (fun input -> sg32 x input)

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

inline_for_extraction
let serialize32_dsum_t
  (s: dsum)
  (x: enum_key (dsum_enum s))
: Tot Type
= dsum_cases s (Known x) -> Tot bytes32

inline_for_extraction
let serialize32_dsum_eq
  (s: dsum)
  (x: enum_key (dsum_enum s))
: Tot (serialize32_dsum_t s x -> serialize32_dsum_t s x -> GTot Type0)
= feq _ _ eq2

let serialize32_dsum_eq_refl
  (s: dsum)
  (x: enum_key (dsum_enum s))
: Tot (r_reflexive_t _ (serialize32_dsum_eq s x))
= fun _ -> ()

let serialize32_dsum_eq_trans
  (s: dsum)
  (x: enum_key (dsum_enum s))
: Tot (r_transitive_t _ (serialize32_dsum_eq s x))
= fun _ _ _ -> ()

inline_for_extraction
let serialize32_dsum_if
  (s: dsum)
  (x: enum_key (dsum_enum s))
: Tot (if_combinator _ (serialize32_dsum_eq s x))
= fif _ _ _ (default_if _)

(* FIXME: WHY WHY WHY do I need this CONTRIVED aux definition? *)

inline_for_extraction
let serialize32_dsum_cases_aux
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_cases s (Known x))))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (sr32: (x: dsum_known_key s) -> Tot (serializer32 (sr x)))
  (#k: parser_kind)
  (g: (x: dsum_unknown_key s) -> Tot (parser k (dsum_cases s (Unknown x))))
  (sg: (x: dsum_unknown_key s) -> Tot (serializer (g x)))
  (sg32: (x: dsum_unknown_key s) -> Tot (serializer32 (sg x)))
  (destr: dep_enum_destr (dsum_enum s) (serialize32_dsum_t s))
  (x: dsum_key s)
: Tot ((input: dsum_cases s x) -> (y: bytes32 { serializer32_correct (serialize_dsum_cases s f sr g  sg x) input y } ))
= fun (input: dsum_cases s x) ->
  match x with
  | Known x ->
    destr _ (serialize32_dsum_if s) (serialize32_dsum_eq_refl s) (serialize32_dsum_eq_trans s) sr32 x input
  | Unknown x ->
    sg32 x input

inline_for_extraction
let serialize32_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_cases s (Known x))))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (sr32: (x: dsum_known_key s) -> Tot (serializer32 (sr x)))
  (#k: parser_kind)
  (g: (x: dsum_unknown_key s) -> Tot (parser k (dsum_cases s (Unknown x))))
  (sg: (x: dsum_unknown_key s) -> Tot (serializer (g x)))
  (sg32: (x: dsum_unknown_key s) -> Tot (serializer32 (sg x)))
  (destr: dep_enum_destr (dsum_enum s) (serialize32_dsum_t s))
  (x: dsum_key s)
: Tot (serializer32 (serialize_dsum_cases s f sr g sg x))
= serialize32_dsum_cases_aux s f sr sr32 g sg sg32 destr x
