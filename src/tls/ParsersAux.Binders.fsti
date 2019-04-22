module ParsersAux.Binders

module LP = LowParse.Low.Base
module HS = FStar.HyperStack
module U32 = FStar.UInt32

(* ClientHello binders *)

module L = FStar.List.Tot
module CH = Parsers.ClientHello
module CHE = Parsers.ClientHelloExtension

let has_binders (c: CH.clientHello) : Tot Type0 = (* TODO: harmonize with HSL.Transcript.client_hello_has_psk *)
  Cons? (c.CH.extensions) /\
  CHE.CHE_pre_shared_key? (L.last c.CH.extensions)

module Psks = Parsers.OfferedPsks

let get_binders (c: CH.clientHello {has_binders c}) : Tot Psks.offeredPsks_binders =
  (CHE.CHE_pre_shared_key?._0 (L.last c.CH.extensions)).Psks.binders

val set_binders (c: CH.clientHello {has_binders c}) (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c)})
  : GTot (c' : CH.clientHello {
    c'.CH.version == c.CH.version /\
    c'.CH.random == c.CH.random /\
    c'.CH.session_id == c.CH.session_id /\
    c'.CH.cipher_suites == c.CH.cipher_suites /\
    c'.CH.compression_method == c.CH.compression_method /\
    Cons? c'.CH.extensions /\
    L.init c'.CH.extensions == L.init c.CH.extensions /\
    CHE.CHE_pre_shared_key? (L.last c'.CH.extensions) /\
    (CHE.CHE_pre_shared_key?._0 (L.last c'.CH.extensions)).Psks.identities == (CHE.CHE_pre_shared_key?._0 (L.last c.CH.extensions)).Psks.identities /\
    get_binders c' == b'
  })

let rec list_append_init_last (#a: Type) (l: list a { Cons? l }) : Lemma
  (l == L.append (L.init l) [L.last l])
= match l with
  | a :: q ->
    if Cons? q
    then
      list_append_init_last q
    else
      ()

let rec list_init_last_def (#a: Type) (l: list a) (x: a) : Lemma
  (let l' = L.append l [x] in
  L.init l' == l /\ L.last l' == x)
= match l with
  | [] -> ()
  | y :: q -> list_init_last_def q x

let list_init_last_inj (#a: Type) (l1: list a { Cons? l1 } ) (l2: list a { Cons? l2 } ) : Lemma
  (requires (L.init l1 == L.init l2 /\ L.last l1 == L.last l2))
  (ensures (l1 == l2))
= list_append_init_last l1;
  list_append_init_last l2

let set_binders_get_binders (c: CH.clientHello {has_binders c}) : Lemma
  (set_binders c (get_binders c) == c)
= list_init_last_inj c.CH.extensions (set_binders c (get_binders c)).CH.extensions

val set_binders_bytesize
  (c: CH.clientHello {has_binders c})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c)})
: Lemma
  (CH.clientHello_bytesize (set_binders c b') == CH.clientHello_bytesize c)

let set_binders_set_binders
  (c: CH.clientHello {has_binders c})
  (b1: Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b1 == Psks.offeredPsks_binders_bytesize (get_binders c)})
  (b2: Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b2 == Psks.offeredPsks_binders_bytesize b1})
: Lemma
  (set_binders (set_binders c b1) b2 == set_binders c b2)
= list_init_last_inj (set_binders (set_binders c b1) b2).CH.extensions (set_binders c b2).CH.extensions

val binders_offset
  (c: CH.clientHello {has_binders c})
: Tot (u: U32.t { U32.v u <= Seq.length (LP.serialize CH.clientHello_serializer c) })

val binders_offset_set_binder
  (c: CH.clientHello {has_binders c})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c) } )
: Lemma
  (binders_offset (set_binders c b') == binders_offset c)

module BY = FStar.Bytes

let truncate_clientHello_bytes
  (c: CH.clientHello {has_binders c})
: Tot BY.bytes
= BY.slice (CH.clientHello_serializer32 c) 0ul (binders_offset c)

val truncate_clientHello_bytes_correct
  (c: CH.clientHello {has_binders c})
: Lemma
  (CH.clientHello_serializer32 c == BY.append (truncate_clientHello_bytes c) (Psks.offeredPsks_binders_serializer32 (get_binders c)))

val truncate_clientHello_bytes_set_binders
  (c: CH.clientHello {has_binders c})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c) } )
: Lemma
  (truncate_clientHello_bytes (set_binders c b') == truncate_clientHello_bytes c)

val truncate_clientHello_bytes_inj_binders_bytesize
  (c1: CH.clientHello {has_binders c1})
  (c2: CH.clientHello {has_binders c2})
: Lemma
  (requires (truncate_clientHello_bytes c1 == truncate_clientHello_bytes c2))
  (ensures (
    Psks.offeredPsks_binders_bytesize (get_binders c1) == Psks.offeredPsks_binders_bytesize (get_binders c2)
  ))

module LPS = LowParse.SLow.Base

let truncate_clientHello_bytes_inj
  (c1: CH.clientHello {has_binders c1})
  (c2: CH.clientHello {has_binders c2})
  (b' : Psks.offeredPsks_binders)
: Lemma
  (requires (
    truncate_clientHello_bytes c1 == truncate_clientHello_bytes c2 /\
    (Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c1) \/ Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c2))
  ))
  (ensures (
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c1) /\
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders c2) /\
    set_binders c1 b' == set_binders c2 b'
  ))
= truncate_clientHello_bytes_inj_binders_bytesize c1 c2;
  truncate_clientHello_bytes_correct c1;
  truncate_clientHello_bytes_correct c2;
  Psks.offeredPsks_binders_bytesize_eq b';
  Psks.offeredPsks_binders_bytesize_eq (get_binders c1);
  Psks.offeredPsks_binders_bytesize_eq (get_binders c2);
  truncate_clientHello_bytes_correct (set_binders c1 b');
  truncate_clientHello_bytes_correct (set_binders c2 b');
  truncate_clientHello_bytes_set_binders c1 b' ;
  truncate_clientHello_bytes_set_binders c2 b' ;
  LPS.serializer32_injective _ CH.clientHello_serializer32 (set_binders c1 b') (set_binders c2 b')

(* TODO: replace with accessors once we introduce accessors to elements of variable-length lists *)

let valid_truncate_clientHello
  (#rrel #rel: _)
  (h: HS.mem)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    LP.valid CH.clientHello_parser h sl pos /\
    has_binders (LP.contents CH.clientHello_parser h sl pos)
  ))
  (ensures (
    let c = LP.contents CH.clientHello_parser h sl pos in
    let pos' = LP.get_valid_pos CH.clientHello_parser h sl pos in
    U32.v pos + U32.v (binders_offset c) + Psks.offeredPsks_binders_bytesize (get_binders c) == U32.v pos' /\
    LP.bytes_of_slice_from_to h sl pos (pos `U32.add` binders_offset c) == BY.reveal (truncate_clientHello_bytes c) /\
    LP.valid_content_pos Psks.offeredPsks_binders_parser h sl (pos `U32.add` binders_offset c) (get_binders c) pos'
  ))
= let c = LP.contents CH.clientHello_parser h sl pos in
  LP.serialized_length_eq CH.clientHello_serializer c;
  truncate_clientHello_bytes_correct c;
  let b = get_binders c in
  Psks.offeredPsks_binders_bytesize_eq b;
  LP.serialized_length_eq Psks.offeredPsks_binders_serializer b;
  LP.valid_valid_exact CH.clientHello_parser h sl pos;
  let pos' = LP.get_valid_pos CH.clientHello_parser h sl pos in
  LP.valid_exact_serialize CH.clientHello_serializer h sl pos pos' ;
  let pos1 = pos `U32.add` binders_offset c in
  assert (LP.bytes_of_slice_from_to h sl pos1 pos' == Seq.slice (LP.bytes_of_slice_from_to h sl pos pos') (U32.v pos1 - U32.v pos) (U32.v pos' - U32.v pos));
  LP.serialize_valid_exact Psks.offeredPsks_binders_serializer h sl b pos1 pos' ;
  LP.valid_exact_valid Psks.offeredPsks_binders_parser h sl pos1 pos'

let truncate_clientHello_valid
  (#rrel #rel: _)
  (h: HS.mem)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (pos1: U32.t)
  (pos' : U32.t)
  (c: CH.clientHello {has_binders c})
: Lemma
  (requires (
    LP.live_slice h sl /\
    U32.v pos <= U32.v pos1 /\
    LP.valid_content_pos Psks.offeredPsks_binders_parser h sl pos1 (get_binders c) pos' /\
    LP.bytes_of_slice_from_to h sl pos pos1 `Seq.equal` BY.reveal (truncate_clientHello_bytes c)
  ))
  (ensures (
    LP.valid_content_pos CH.clientHello_parser h sl pos c pos'
  ))
= let b = get_binders c in
  LP.valid_valid_exact Psks.offeredPsks_binders_parser h sl pos1 ;
  LP.valid_exact_serialize Psks.offeredPsks_binders_serializer h sl pos1 pos' ;
  truncate_clientHello_bytes_correct c;
  LP.serialize_valid_exact CH.clientHello_serializer h sl c pos pos' ;
  LP.valid_exact_valid CH.clientHello_parser h sl pos pos'

module B = LowStar.Monotonic.Buffer
module HST = FStar.HyperStack.ST

val binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    LP.valid CH.clientHello_parser h sl pos /\
    has_binders (LP.contents CH.clientHello_parser h sl pos)
  ))
  (ensures (fun h res h' ->
    let c = LP.contents CH.clientHello_parser h sl pos in
    B.modifies B.loc_none h h' /\
    U32.v res <= U32.v pos /\
    U32.v pos + U32.v (binders_offset c) == U32.v res /\
    LP.valid_content_pos Psks.offeredPsks_binders_parser h sl res (get_binders c) (LP.get_valid_pos CH.clientHello_parser h sl pos)
  ))

let valid_binders_mutate
  (#rrel #rel: _)
  (h1: HS.mem)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (pos1: U32.t)
  (l: B.loc)
  (h2: HS.mem)
: Lemma
  (requires (
    LP.valid CH.clientHello_parser h1 sl pos /\ (
    let c = LP.contents CH.clientHello_parser h1 sl pos in
    let pos' = LP.get_valid_pos CH.clientHello_parser h1 sl pos in
    has_binders c /\
    U32.v pos + U32.v (binders_offset c) == U32.v pos1 /\
    LP.valid_pos Psks.offeredPsks_binders_parser h2 sl pos1 pos' /\
    B.modifies (l `B.loc_union` LP.loc_slice_from_to sl pos1 pos') h1 h2 /\
    B.loc_disjoint l (LP.loc_slice_from_to sl pos pos')
  )))
  (ensures (
    let c = LP.contents CH.clientHello_parser h1 sl pos in
    let pos' = LP.get_valid_pos CH.clientHello_parser h1 sl pos in
    U32.v pos + U32.v (binders_offset c) <= U32.v pos' /\ (
    let b1 = get_binders c in
    let b2 = LP.contents Psks.offeredPsks_binders_parser h2 sl pos1 in
    Psks.offeredPsks_binders_bytesize b1 == Psks.offeredPsks_binders_bytesize b2 /\
    LP.valid_content_pos CH.clientHello_parser h2 sl pos (set_binders c b2) pos'
  )))
= valid_truncate_clientHello h1 sl pos;
  let pos' = LP.get_valid_pos CH.clientHello_parser h1 sl pos in
  let c = LP.contents CH.clientHello_parser h1 sl pos in
  let b2 = LP.contents Psks.offeredPsks_binders_parser h2 sl pos1 in
  LP.content_length_eq Psks.offeredPsks_binders_serializer h2 sl pos1 ;
  LP.serialized_length_eq Psks.offeredPsks_binders_serializer b2;
  Psks.offeredPsks_binders_bytesize_eq b2;
  truncate_clientHello_bytes_set_binders c b2;
  B.modifies_buffer_from_to_elim sl.LP.base pos pos1 (l `B.loc_union` LP.loc_slice_from_to sl pos1 pos') h1 h2;
  truncate_clientHello_valid h2 sl pos pos1 pos' (set_binders c b2)
