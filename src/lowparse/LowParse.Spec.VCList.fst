(* Variable-count lists *)

module LowParse.Spec.VCList
include LowParse.Spec.Combinators // for seq_slice_append_l

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Classical = FStar.Classical
module L = FStar.List.Tot

inline_for_extraction
type nlist (n: nat) (t: Type) = (l: list t { L.length l == n } )

// abstract
inline_for_extraction
let nlist_nil (#t: Type) : Tot (nlist 0 t) = []

// abstract
let nlist_nil_unique (t: Type) (l: nlist 0 t) : Lemma (l == nlist_nil) = ()

// abstract
inline_for_extraction
let nlist_cons (#t: Type) (#n: nat) (a: t) (q: nlist n t) : Tot (nlist (n + 1) t) =
  a :: q

// abstract
inline_for_extraction
let nlist_destruct (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Tot (t * nlist n t) =
  match x with (a :: q) -> a, q

// abstract
let nlist_cons_unique (#t: Type) (#n: nat) (x: nlist (n + 1) t) : Lemma
  (let (a, q) = nlist_destruct x in x == nlist_cons a q)
= ()

unfold let mul = Prims.op_Multiply

inline_for_extraction
let synth_nlist (#t: Type) (n: nat) (xy: t * nlist n t) : Tot (nlist (n + 1) t) =
  match xy with (x, y) ->
  nlist_cons x y

inline_for_extraction
let synth_nlist_recip (#t: Type) (n: nat) (xy: nlist (n + 1) t) : Tot (t * nlist n t) =
  nlist_destruct xy

// abstract
let synth_inverse_1 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist #t n) (synth_nlist_recip n))
= ()

// abstract
let synth_inverse_2 (t: Type) (n: nat) : Lemma
  (synth_inverse (synth_nlist_recip #t n) (synth_nlist n))
= ()

let rec parse_nlist_kind
  (n: nat)
  (k: parser_kind)
: Tot parser_kind
  (decreases n)
= if n = 0
  then parse_ret_kind
  else k `and_then_kind` parse_nlist_kind (n - 1) k

let rec parse_nlist_kind_low
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind n k).parser_kind_low == n `mul` k.parser_kind_low)
= if n = 0
  then ()
  else parse_nlist_kind_low (n - 1) k

let rec parse_nlist_kind_high
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind n k).parser_kind_high == (match k.parser_kind_high with
    | None -> if n = 0 then Some 0 else None
    | Some b -> Some (n `mul` b)
  ))
= if n = 0
  then ()
  else parse_nlist_kind_high (n - 1) k

let rec parse_nlist_kind_metadata
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind n k).parser_kind_metadata == (if n = 0 then Some ParserKindMetadataTotal else k.parser_kind_metadata))
= if n = 0
  then ()
  else parse_nlist_kind_metadata (n - 1) k

let rec parse_nlist_kind_subkind
  (n: nat)
  (k: parser_kind)
: Lemma
  ((parse_nlist_kind n k).parser_kind_subkind == (
    if n = 0 then Some ParserStrong else k.parser_kind_subkind
  ))
= if n = 0
  then ()
  else parse_nlist_kind_subkind (n - 1) k

let rec parse_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser (parse_nlist_kind n k) (nlist n t))
= if n = 0
  then parse_ret nlist_nil
  else begin
    parse_synth
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
  end

abstract
let parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (y: parser (parse_nlist_kind n k) (nlist n t) { y == parse_nlist' n p } )
= parse_nlist' n p

let parse_nlist_eq
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma (
  parse (parse_nlist n p) b == (
    if n = 0
    then Some ([], 0)
    else match parse p b with
    | Some (elem, consumed) ->
      let b' = Seq.slice b consumed (Seq.length b) in
      begin match parse (parse_nlist (n - 1) p) b' with
      | Some (q, consumed') -> Some (elem :: q, consumed + consumed')
      | _ -> None
      end
    | _ -> None
  ))
= if n = 0
  then ()
  else begin
    parse_synth_eq
      (p `nondep_then` parse_nlist' (n - 1) p)
      (synth_nlist (n - 1))
      b;
    nondep_then_eq p (parse_nlist' (n - 1) p) b
  end

let rec serialize_nlist'
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (serializer (parse_nlist n p))
= if n = 0
  then begin
    Classical.forall_intro (nlist_nil_unique t);
    (fun _ -> Seq.empty)
  end
  else begin
    synth_inverse_1 t (n - 1);
    synth_inverse_2 t (n - 1);
    serialize_synth _ (synth_nlist (n - 1)) (serialize_nondep_then _ s () _ (serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ()
  end

abstract
let serialize_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Tot (y: serializer (parse_nlist n p) { y == serialize_nlist' n s })
= serialize_nlist' n s

let serialize_nlist_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
: Lemma
  (ensures (serialize (serialize_nlist 0 s) [] == Seq.empty))
= ()

let serialize_nlist_cons
  (#k: parser_kind)
  (#t: Type0)
  (n: nat)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (a: t)
  (q: nlist n t)
: Lemma
  (ensures (
    serialize (serialize_nlist (n + 1) s) (a :: q) == Seq.append (serialize s a) (serialize (serialize_nlist n s) q)
  ))
= serialize_synth_eq _ (synth_nlist n) (serialize_nondep_then _ s () _ (serialize_nlist' n s)) (synth_nlist_recip n) () (a :: q);
  serialize_nondep_then_eq _ s () _ (serialize_nlist' n s) (a, q)
