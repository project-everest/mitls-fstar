module LowParseWrappers

include TLS.Result // for AD_decode_error
include Parse // for pinverse, lemma_(p?)inverse_*, etc.
open LowParse.SLow.Base
include FStar.Bytes // for bytes, lbytes, length, equal

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

let wrap_serializer32_constant_length_precond
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (len: nat)
: GTot Type0
= k.parser_kind_high == Some k.parser_kind_low /\
  k.parser_kind_low == len

private
let le_antisym
  (x y: int)
: Lemma
  (requires (x <= y /\ y <= x))
  (ensures (x == y))
= ()

inline_for_extraction
let wrap_serializer32_constant_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (len: nat)
  (u: unit { wrap_serializer32_constant_length_precond s32 len } )
  (x: t)
: Tot (lbytes len)
= [@inline_let]
  let y = s32 x in
  [@inline_let]
  let _ =
    serialize_length s x;
    le_antisym (length y) len
  in
  y

inline_for_extraction
let wrap_parser32_constant_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (len: nat)
  (u: unit { wrap_serializer32_constant_length_precond s32 len } )
  (p32: parser32 p)
  (msg: _)
: Tot (pinverse_t (wrap_serializer32_constant_length s32 len u))
= fun (x: lbytes len) ->
  match p32 x with
  | Some (y, _) -> Correct y
  | _ -> fatal Decode_error msg

let bytes_equal_intro
  (b1 b2: bytes)
: Lemma
  (requires (reveal b1 == reveal b2))
  (ensures (equal b1 b2))
= ()

let wrap_parser32_total_constant_length_precond
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (len: nat)
: GTot Type0
= k.parser_kind_high == Some k.parser_kind_low /\
  k.parser_kind_low == len /\
  k.parser_kind_metadata == Some ParserKindMetadataTotal

inline_for_extraction
let wrap_parser32_total_constant_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (p32: parser32 p)
  (len: nat)
  (u: unit { wrap_parser32_total_constant_length_precond p32 len } )
  (x: lbytes len)
: Tot (y: t { s32 y == x } )
= [@inline_let] let _ = parser_kind_prop_equiv k p in
  match p32 x with
  | Some (y, consumed) ->
    [@inline_let]
    let _ = parser32_then_serializer32' p32 s32 x y consumed in
    y

let lemma_pinverse_serializer32_parser32_constant_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (len: nat)
  (u: unit { wrap_serializer32_constant_length_precond s32 len } )
  (p32: parser32 p)
  (msg: _)
  (x: lbytes len)
: Lemma
  (lemma_pinverse_f_g #t #(lbytes len) eq2 (wrap_serializer32_constant_length s32 len u) (wrap_parser32_constant_length s32 len u p32 msg) x)
= if (Some? (p32 x))
  then begin
    let (Some (y, consumed)) = p32 x in
    parser32_then_serializer32' p32 s32 x y consumed
  end else ()

let lemma_inverse_serializer32_parser32_constant_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (len: nat)
  (u: unit { wrap_serializer32_constant_length_precond s32 len } )
  (p32: parser32 p)
  (msg: _)
  (x: t)
: Lemma
  (lemma_inverse_g_f (wrap_serializer32_constant_length s32 len u) (wrap_parser32_constant_length s32 len u p32 msg) x)
= serializer32_then_parser32 s p32 s32 x

inline_for_extraction
let wrap_parser32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (msg: _)
  (x: bytes32)
: Tot (result t)
= match p32 x with
  | Some (y, _) -> Correct y
  | _ -> fatal Decode_error msg

inline_for_extraction
let wrap_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (x: t)
: Tot bytes32
= s32 x

let lemma_inverse_serializer32_parser32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (p32: parser32 p)
  (msg: _)
  (x: t)
: Lemma
  (lemma_inverse_g_f (wrap_serializer32 s32) (wrap_parser32 p32 msg) x)
= serializer32_then_parser32 s p32 s32 x

module L = FStar.List.Tot

let rec list_bytesize_snoc
  (#t: Type)
  (bytesize: t -> GTot nat)
  (list_bytesize: list t -> GTot nat)
  (list_bytesize_nil: squash (list_bytesize [] == 0))
  (list_bytesize_cons: (
    (x: t) ->
    (y: list t) ->
    Lemma
    (list_bytesize (x :: y) == bytesize x + list_bytesize y)
  ))
  (l: list t)
  (x: t)
: Lemma
  (list_bytesize (L.append l [x]) == list_bytesize l + bytesize x)
= match l with
  | [] ->
    list_bytesize_cons x []
  | a :: q ->
    list_bytesize_snoc bytesize list_bytesize list_bytesize_nil list_bytesize_cons q x;
    list_bytesize_cons a (L.append q [x]);
    list_bytesize_cons a q

let rec list_bytesize_filter
  (#t: Type)
  (bytesize: t -> GTot nat)
  (list_bytesize: list t -> GTot nat)
  (list_bytesize_nil: squash (list_bytesize [] == 0))
  (list_bytesize_cons: (
    (x: t) ->
    (y: list t) ->
    Lemma
    (list_bytesize (x :: y) == bytesize x + list_bytesize y)
  ))
  (f: t -> Tot bool)
  (l: list t)
: Lemma
  (list_bytesize (L.filter f l) <= list_bytesize l)
= match l with
  | [] -> ()
  | a :: q ->
    list_bytesize_cons a q;
    list_bytesize_filter bytesize list_bytesize list_bytesize_nil list_bytesize_cons f q;
    if f a
    then list_bytesize_cons a (L.filter f q)
    else ()
