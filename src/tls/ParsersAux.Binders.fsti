module ParsersAux.Binders

/// This is the only API for the ParsersAux files, used in Transcript etc.
///
/// Their purpose is to specify ClientHello messages with truncated
/// binders, and implement the overwriting of the binders in a
/// previously-serialized message, once its prefix has been hashed to
/// compute the binders.
///
/// For convenience, we include this interface in HandshakeMessages,
/// although it only uses its first definitions.
///
module Seq = FStar.Seq
module LP = LowParse.Low.Base
module HS = FStar.HyperStack
module U32 = FStar.UInt32

(* ClientHello binders *)

module L = FStar.List.Tot
module H = Parsers.Handshake
module CH = Parsers.ClientHello
module CHE = Parsers.ClientHelloExtension
module Psks = Parsers.OfferedPsks

module List = FStar.List.Tot

type binders = Psks.offeredPsks_binders

/// First dealing with binders as a ClientHello property

let ch_bound (ch:CH.clientHello): bool =
  let es = ch.CH.extensions in
  es <> [] && CHE.CHE_pre_shared_key? (List.last es)

let clientHello_with_binders = ch: CH.clientHello{ ch_bound ch }

let ch_psks (ch: clientHello_with_binders): Psks.offeredPsks  =
  let es = ch.CH.extensions in
  let CHE.CHE_pre_shared_key psks = List.last es in
  psks

let ch_binders (ch: clientHello_with_binders): binders =
  (ch_psks ch).Psks.binders

val ch_set_binders
  (ch0: clientHello_with_binders)
  (b1 : binders { Psks.offeredPsks_binders_bytesize b1 == Psks.offeredPsks_binders_bytesize (ch_binders ch0)})
  : Tot (ch1: clientHello_with_binders {
    let open CH in
    ch1.version == ch0.version /\
    ch1.random == ch0.random /\
    ch1.session_id == ch0.session_id /\
    ch1.cipher_suites == ch0.cipher_suites /\
    ch1.compression_methods == ch0.compression_methods /\
    List.init ch1.extensions == List.init ch0.extensions /\
    (ch_psks ch1).Psks.identities == (ch_psks ch0).Psks.identities /\
    ch_binders ch1 = b1 })


/// Adding the M_client_hello message constructor

let has_binders (m: H.handshake) : Tot bool = (* TODO: harmonize with HSL.Transcript.client_hello_has_psk *)
  H.M_client_hello? m &&
  ch_bound (H.M_client_hello?._0 m)

let get_binders (m: H.handshake {has_binders m}) : Tot binders =
  let c = H.M_client_hello?._0 m in ch_binders c

val set_binders (m: H.handshake {has_binders m}) (b' : binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m)})
  : Tot (m' : H.handshake {
    has_binders m' /\ (
    let c = H.M_client_hello?._0 m in
    let c' = H.M_client_hello?._0 m' in
    c' = ch_set_binders c b' /\
    get_binders m' == b'
  )})

let set_binders_get_binders (m: H.handshake {has_binders m}) : Lemma
  (set_binders m (get_binders m) == m)
= L.init_last_inj (H.M_client_hello?._0 m).CH.extensions (H.M_client_hello?._0 (set_binders m (get_binders m))).CH.extensions

val set_binders_bytesize
  (m: H.handshake {has_binders m})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m)})
: Lemma
  (H.handshake_bytesize (set_binders m b') == H.handshake_bytesize m)

let set_binders_set_binders
  (m: H.handshake {has_binders m})
  (b1: Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b1 == Psks.offeredPsks_binders_bytesize (get_binders m)})
  (b2: Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b2 == Psks.offeredPsks_binders_bytesize b1})
: Lemma
  (set_binders (set_binders m b1) b2 == set_binders m b2)
= L.init_last_inj (H.M_client_hello?._0 (set_binders (set_binders m b1) b2)).CH.extensions (H.M_client_hello?._0 (set_binders m b2)).CH.extensions

val binders_offset
  (m: H.handshake {has_binders m})
: Tot (u: U32.t { 0 < U32.v u /\ U32.v u < Seq.length (LP.serialize H.handshake_serializer m) })

val binders_offset_set_binder
  (m: H.handshake {has_binders m})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m) } )
: Lemma
  (binders_offset (set_binders m b') == binders_offset m)

module BY = FStar.Bytes

let truncate_clientHello_bytes
  (m: H.handshake {has_binders m})
: Tot BY.bytes
= BY.slice (H.handshake_serializer32 m) 0ul (binders_offset m)

val parse_truncate_clientHello_bytes
  (m: H.handshake {has_binders m})
: Lemma
  (H.handshake_parser32 (truncate_clientHello_bytes m) == None)

val truncate_clientHello_bytes_correct
  (m: H.handshake {has_binders m})
: Lemma
  (H.handshake_serializer32 m == BY.append (truncate_clientHello_bytes m) (Psks.offeredPsks_binders_serializer32 (get_binders m)))

val truncate_clientHello_bytes_set_binders
  (m: H.handshake {has_binders m})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m) } )
: Lemma
  (truncate_clientHello_bytes (set_binders m b') == truncate_clientHello_bytes m)

val truncate_clientHello_bytes_inj_binders_bytesize
  (m1: H.handshake {has_binders m1})
  (m2: H.handshake {has_binders m2})
: Lemma
  (requires (truncate_clientHello_bytes m1 == truncate_clientHello_bytes m2))
  (ensures (
    Psks.offeredPsks_binders_bytesize (get_binders m1) == Psks.offeredPsks_binders_bytesize (get_binders m2)
  ))

module LPS = LowParse.SLow.Base

let truncate_clientHello_bytes_inj
  (m1: H.handshake {has_binders m1})
  (m2: H.handshake {has_binders m2})
  (b' : Psks.offeredPsks_binders)
: Lemma
  (requires (
    truncate_clientHello_bytes m1 == truncate_clientHello_bytes m2 /\
    (Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m1) \/ Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m2))
  ))
  (ensures (
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m1) /\
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders m2) /\
    set_binders m1 b' == set_binders m2 b'
  ))
= truncate_clientHello_bytes_inj_binders_bytesize m1 m2;
  truncate_clientHello_bytes_correct m1;
  truncate_clientHello_bytes_correct m2;
  Psks.offeredPsks_binders_bytesize_eq b';
  Psks.offeredPsks_binders_bytesize_eq (get_binders m1);
  Psks.offeredPsks_binders_bytesize_eq (get_binders m2);
  truncate_clientHello_bytes_correct (set_binders m1 b');
  truncate_clientHello_bytes_correct (set_binders m2 b');
  truncate_clientHello_bytes_set_binders m1 b' ;
  truncate_clientHello_bytes_set_binders m2 b' ;
  LPS.serializer32_injective _ H.handshake_serializer32 (set_binders m1 b') (set_binders m2 b')

(* TODO: replace with accessors once we introduce accessors to elements of variable-length lists *)

let valid_truncate_clientHello
  (#rrel #rel: _)
  (h: HS.mem)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    LP.valid H.handshake_parser h sl pos /\
    has_binders (LP.contents H.handshake_parser h sl pos)
  ))
  (ensures (
    LP.valid H.handshake_parser h sl pos /\
    has_binders (LP.contents H.handshake_parser h sl pos) /\ (
    let m = LP.contents H.handshake_parser h sl pos in
    let pos' = LP.get_valid_pos H.handshake_parser h sl pos in
    U32.v pos + U32.v (binders_offset m) + Psks.offeredPsks_binders_bytesize (get_binders m) == U32.v pos' /\
    LP.bytes_of_slice_from_to h sl pos (pos `U32.add` binders_offset m) == BY.reveal (truncate_clientHello_bytes m) /\
    LP.valid_content_pos Psks.offeredPsks_binders_parser h sl (pos `U32.add` binders_offset m) (get_binders m) pos'
  )))
= let m = LP.contents H.handshake_parser h sl pos in
  LP.serialized_length_eq H.handshake_serializer m;
  truncate_clientHello_bytes_correct m;
  let b = get_binders m in
  Psks.offeredPsks_binders_bytesize_eq b;
  LP.serialized_length_eq Psks.offeredPsks_binders_serializer b;
  LP.valid_valid_exact H.handshake_parser h sl pos;
  let pos' = LP.get_valid_pos H.handshake_parser h sl pos in
  LP.valid_exact_serialize H.handshake_serializer h sl pos pos' ;
  let pos1 = pos `U32.add` binders_offset m in
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
  (m: H.handshake {has_binders m})
: Lemma
  (requires (
    LP.live_slice h sl /\
    U32.v pos <= U32.v pos1 /\
    LP.valid_content_pos Psks.offeredPsks_binders_parser h sl pos1 (get_binders m) pos' /\
    LP.bytes_of_slice_from_to h sl pos pos1 `Seq.equal` BY.reveal (truncate_clientHello_bytes m)
  ))
  (ensures (
    LP.valid_content_pos H.handshake_parser h sl pos m pos'
  ))
= let b = get_binders m in
  LP.valid_valid_exact Psks.offeredPsks_binders_parser h sl pos1 ;
  LP.valid_exact_serialize Psks.offeredPsks_binders_serializer h sl pos1 pos' ;
  truncate_clientHello_bytes_correct m;
  LP.serialize_valid_exact H.handshake_serializer h sl m pos pos' ;
  LP.valid_exact_valid H.handshake_parser h sl pos pos'

module B = LowStar.Monotonic.Buffer
module HST = FStar.HyperStack.ST

val binders_pos
  (#rrel #rel: _)
  (sl: B.mbuffer LP.byte rrel rel)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    LP.bvalid H.handshake_parser h sl pos /\
    has_binders (LP.bcontents H.handshake_parser h sl pos)
  ))
  (ensures (fun h res h' ->
    let m = LP.bcontents H.handshake_parser h sl pos in
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (binders_offset m) == U32.v res /\
    LP.bvalid_content_pos Psks.offeredPsks_binders_parser h sl res (get_binders m) (LP.bget_valid_pos H.handshake_parser h sl pos)
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
    LP.valid H.handshake_parser h1 sl pos /\ (
    let m = LP.contents H.handshake_parser h1 sl pos in
    let pos' = LP.get_valid_pos H.handshake_parser h1 sl pos in
    has_binders m /\
    U32.v pos + U32.v (binders_offset m) == U32.v pos1 /\
    LP.valid_pos Psks.offeredPsks_binders_parser h2 sl pos1 pos' /\
    B.modifies l h1 h2 /\
    B.loc_disjoint l (LP.loc_slice_from_to sl pos pos1)
  )))
  (ensures (
    let m = LP.contents H.handshake_parser h1 sl pos in
    let pos' = LP.get_valid_pos H.handshake_parser h1 sl pos in
    U32.v pos + U32.v (binders_offset m) <= U32.v pos' /\ (
    let b1 = get_binders m in
    let b2 = LP.contents Psks.offeredPsks_binders_parser h2 sl pos1 in
    Psks.offeredPsks_binders_bytesize b1 == Psks.offeredPsks_binders_bytesize b2 /\
    LP.valid_content_pos H.handshake_parser h2 sl pos (set_binders m b2) pos'
  )))
= valid_truncate_clientHello h1 sl pos;
  let pos' = LP.get_valid_pos H.handshake_parser h1 sl pos in
  let m = LP.contents H.handshake_parser h1 sl pos in
  let b2 = LP.contents Psks.offeredPsks_binders_parser h2 sl pos1 in
  LP.content_length_eq Psks.offeredPsks_binders_serializer h2 sl pos1 ;
  LP.serialized_length_eq Psks.offeredPsks_binders_serializer b2;
  Psks.offeredPsks_binders_bytesize_eq b2;
  truncate_clientHello_bytes_set_binders m b2;
  B.modifies_buffer_from_to_elim sl.LP.base pos pos1 (l `B.loc_union` LP.loc_slice_from_to sl pos1 pos') h1 h2;
  truncate_clientHello_valid h2 sl pos pos1 pos' (set_binders m b2)

(* Build a (dummy, but) canonical list of binders, for a given size *)

type binders_len = len:UInt32.t {
  35 <= UInt32.v len /\
  UInt32.v len <= 65537
}

/// The length of the binders in a clientHello
let ch_binders_len (ch:clientHello_with_binders)
  : Tot (b:binders_len {
           UInt32.v b =
           Psks.offeredPsks_binders_bytesize (ch_binders ch) /\
           UInt32.v b =
           Seq.length
             (LP.serialize
               Psks.offeredPsks_binders_serializer (ch_binders ch))
         })
  = Psks.offeredPsks_binders_bytesize_eq (ch_binders ch);
    Psks.offeredPsks_binders_size32 (ch_binders ch)
    // An alternative way to compute it in GTot
    // UInt32.uint_to_t (Psks.offeredPsks_binders_bytesize (PB.get_binders ch))

val build_canonical_binders (len: binders_len): Pure binders
  (requires True)
  (ensures (fun y -> Psks.offeredPsks_binders_bytesize y == U32.v len))
