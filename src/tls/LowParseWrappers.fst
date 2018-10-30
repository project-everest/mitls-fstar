module LowParseWrappers
include TLSError // for AD_decode_error
include FStar.Error // for Correct, Error
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
  let _ = le_antisym (length y) len in
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
  (msg: string)
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
  k.parser_kind_metadata.parser_kind_metadata_total == true

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
= match p32 x with
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
  (msg: string)
  (x: lbytes len)
: Lemma
  (lemma_pinverse_f_g #t #(lbytes len) equal (wrap_serializer32_constant_length s32 len u) (wrap_parser32_constant_length s32 len u p32 msg) x)
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
  (msg: string)
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
  (msg: string)
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
  (msg: string)
  (x: t)
: Lemma
  (lemma_inverse_g_f (wrap_serializer32 s32) (wrap_parser32 p32 msg) x)
= serializer32_then_parser32 s p32 s32 x
