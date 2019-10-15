module QUIC.API

module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Error

module SAEAD = Spec.Agile.AEAD
module SH = Spec.Hash
module SHD = Spec.Hash.Definitions
module SQUIC = Spec.QUIC

module U64 = FStar.UInt64
module I32 = FStar.Int32
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(**** Current API of mitlsffi.h ****)

[@CAbstractStruct]
val quic_state: Type0
let pquic_state = B.pointer quic_state

noeq type quic_process_ctx = {
  (* Inputs *)
  input: IB.ibuffer U8.t;
  input_len: U32.t;
  ouput: B.buffer U8.t;
  output_len: U32.t;
  (* Outputs *)
  tls_error: U16.t;
  consumed: U32.t; // Bytes read from input buffer
  written: U32.t; // Bytes written to output buffer
  to_be_written: U32.t; // Bytes left to write
  reader_epoch: I32.t;
  writer_epoch: I32.t;
  flags: U16.t;
}

val flag_complete: U16.t // Handshake "complete"
val flag_rejected_0rtt: U16.t // 0-RTT rejected
val flag_writeable: U16.t // OK to send application data
val flag_post_hs: U16.t // Output is post-handshake data

type rw =
| Writer
| Reader

noeq type quic_secret = {
  hash_alg: SHD.hash_alg;
  secret: B.buffer U8.t;
}

val quic_create:
  config: B.pointer TLSConstants.config ->
  St pquic_state

val quic_process:
  st: pquic_state ->
  ctx: B.pointer quic_process_ctx ->
  St U32.t

val quic_get_traffic_secret:
  st:pquic_state ->
  secret: B.pointer quic_secret ->
  epoch: Int32.t ->
  rw: rw ->
  St U32.t

val quic_send_ticket:
  st:pquic_state ->
  ticket_data: B.buffer U8.t ->
  ticket_data_len: U32.t ->
  St U32.t

val quic_free:
  st:pquic_state ->
  St U32.t

[@CAbstractStruct]
val quic_key: Type0
let pquic_key = B.pointer quic_key

val quic_derive_initial_secrets:
  con_id: B.buffer U8.t ->
  con_id_len: U32.t ->
  salt: B.buffer U8.t ->
  salt_len: U32.t ->
  St (cli:quic_secret * srv:quic_secret)
  
val quic_crypto_tls_derive_secret:
  s: quic_secret ->
  label: B.buffer U8.t ->
  len: U32.t ->
  St quic_secret

val quic_crypto_derive_key:
  s:quic_secret ->
  St pquic_key

val quic_crypto_create:
  alg: SQUIC.ea ->
  ae_key: B.buffer U8.t ->
  iv: B.buffer U8.t ->
  pne_key: B.buffer U8.t ->
  St pquic_key

val quic_crypto_encrypt:
  st: pquic_key ->
  nonce: U64.t ->
  aad: B.buffer U8.t ->
  aad_len: U32.t ->
  plain: B.buffer U8.t ->
  plain_len: U32.t ->
  cipher: B.buffer U8.t ->
  St unit

val quic_crypto_decrypt:
  st: pquic_key ->
  nonce: U64.t ->
  aad: B.buffer U8.t ->
  aad_len: U32.t ->
  cipher: B.buffer U8.t ->
  cipher_len: U32.t ->
  plain: B.buffer U8.t ->
  St bool

val quic_crypto_hp_mask:
  st: pquic_key ->
  sample: B.buffer U8.t{B.length sample == 16} ->
  mask: B.buffer U8.t{B.length mask == 5} ->
  St unit

val quic_crypto_free_key:
  pquic_key ->
  St unit

val quic_crypto_free_secret:
  quic_secret ->
  St unit

(**** Integration of QuicCrypto.fsti ****)

type u2 = n:U8.t{U8.v n < 4}
type u4 = n:U8.t{U8.v n < 16}
type u62 = n:UInt64.t{UInt64.v n < pow2 62}
let add3 (k:u4) : n:U8.t{U8.v n <= 18} = if k = 0uy then 0uy else U8.(k +^ 3uy)
type vlsize = n:U8.t{U8.v n == 1 \/ U8.v n == 2 \/ U8.v n == 4 \/ U8.v n == 8}

let vlen (k:u62) : vlsize =
  let open FStar.UInt64 in
  if k <^ 64uL then 1uy
  else if k <^ 16384uL then 2uy
  else if k <^ 1073741824uL then 4uy
  else 8uy

noeq type quic_header =
  | Short:
    spin: U8.t ->
    phase: U8.t ->
    cid_len: U8.t{let l = U8.v cid_len in l == 0 \/ (4 <= l /\ l <= 18)} ->
    cid: B.lbuffer U8.t (U8.v cid_len) ->
    quic_header
  | Long:
    typ: u2 ->
    version: U32.t ->
    dcil: u4 ->
    scil: u4 ->
    dcid: B.lbuffer U8.t (U8.v (add3 dcil)) ->
    scid: B.lbuffer U8.t (U8.v (add3 scil)) ->
    plain_len: U32.t{U32.v plain_len < SQUIC.max_cipher_length} -> // Short due to limitations of AEAD spec
    quic_header

noeq type quic_ctx = {
  (* Inputs *)
  input: IB.ibuffer U8.t;
  input_len: U32.t;
  ouput: B.buffer U8.t;
  output_len: U32.t;
  
  (* Outputs *)
  tls_error: U16.t;
  consumed: U32.t; // Bytes read from input buffer
  written: U32.t; // Bytes written to output buffer
  to_be_written: U32.t; // Bytes left to write
  flags: U16.t;
}

val process:
  st: pquic_state ->
  ctx: B.pointer quic_ctx ->
  St U32.t

// Crypto indexes
val qid: eqtype
val safe: qid -> Type
val is_safe: i:qid -> ST bool
  (requires fun h0 -> True) (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> safe i))
val alg: qid -> GTot SQUIC.ea

val quic_next_pn: st: pquic_state -> rw: rw -> St u62
val invariant: w:pquic_state -> h:HS.mem -> Type0

let ivlen (alg:SQUIC.ea) = 12ul
let taglen = 16ul
type plainLen = l:nat{l + U32.v taglen < pow2 32}
type plainLenMin (lmin:plainLen) = l:plainLen{l >= lmin}

module U128 = FStar.UInt128

let iv (alg:SQUIC.ea) =
  let open FStar.Mul in
  n:U128.t { U128.v n < pow2 (8 * U32.v (ivlen alg)) }

module BY = FStar.Bytes

noeq type plain_pkg =
  | PlainPkg:
    min_len: plainLen ->
    plain: (i:qid -> plainLenMin min_len -> eqtype) ->
    as_bytes: (i:qid -> l:plainLenMin min_len -> plain i l -> GTot (BY.lbytes l)) ->
    repr: (i:qid{~(safe i)} -> l:plainLenMin min_len -> p:plain i l -> Tot (b:BY.lbytes l{b == as_bytes i l p})) ->
    plain_pkg
    
noeq type info' = {
  alg: SQUIC.ea;
  plain: plain_pkg;
}

type info (i:qid) = info:info'{alg i == info.alg}
let nonce (#i:qid) (u:info i) : eqtype = U128.t

let aadmax =
  assert_norm (2000 <= pow2 32 - 1);
  2000ul // arbitrary; enough for TLS
type adata = b:BY.bytes{BY.length b <= U32.v aadmax}
let plainLenM (#i:qid) (u:info i) = plainLenMin (PlainPkg?.min_len u.plain)
let plain (#i:qid) (u:info i) (l:plainLenM u) =
  (PlainPkg?.plain u.plain) i l
type cipher (i:qid) (u:info i) (l:plainLenM u) =
  BY.lbytes (l + (UInt32.v taglen))
  
type entry (i:qid) (u:info i) =
  | Entry:
    n: nonce u ->
    ad: adata ->
    #l: plainLenM u ->
    p: plain u l ->
    c: cipher i u l ->
    entry i u

val get_writer_id: pquic_state -> HS.mem -> GTot qid
val wgetinfo: st:pquic_state -> i:qid -> h:HS.mem -> info i
val next_nonce: i:qid -> st:pquic_state -> pn_en:u2 -> h:HS.mem -> GTot (nonce (wgetinfo st i h))

val wlog: st:pquic_state -> i:qid -> h:HS.mem ->
  GTot (Seq.seq (entry i (wgetinfo st i h)))

module M = LowStar.Modifies

let wentry_for_nonce (h:HS.mem) (#i:qid) (st:pquic_state) (n:nonce (wgetinfo st i h))
  : Ghost (option (entry i (wgetinfo st i h)))
  (requires safe i) (ensures fun _ -> True) =
  Seq.find_l (fun e -> Entry?.n e = n) (wlog st i h)

let spec_header (h:quic_header) (m:HS.mem) : GTot SQUIC.header =
  match h with
  | Short spin phase cid_len cid ->
    SQUIC.Short (spin<>0uy) (phase<>0uy) (B.as_seq m cid)
  | Long typ version dcil scil dcid scid plain_len ->
    SQUIC.Long (U8.v typ) (U32.v version) (U8.v dcil) (U8.v scil)
    (B.as_seq m dcid) (B.as_seq m scid) (U32.v plain_len)

val quic_encrypt_packet:
  st: pquic_state ->
  pn_len: u2 ->
  h: quic_header ->
  plain: IB.ibuffer U8.t ->
  plain_len: U32.t{Long? h ==> Long?.plain_len h == plain_len} ->
  out: B.buffer U8.t ->
  out_len: U32.t ->
  ST U32.t
  (requires fun h0 -> invariant st h0)
  (ensures fun h0 r h1 ->
    M.modifies (M.loc_buffer out) h0 h1 /\
    invariant st h1 /\
    (if r <> 0ul then
     let i = get_writer_id st h0 in
     let n = next_nonce i st pn_len h0 in
     let SQUIC.
     safe i ==> begin
      wlog st i h1 == Seq.snoc (wlog st i h0) (Entry n aad p c)
     end
    else True)
  )

noeq type quic_packet_r =
| Incoming_packet:
  pn_len: u2 ->
  pn: u62 ->
  h: quic_header ->
  plain_len: U32.t ->
  plain: B.lbuffer U8.t (U32.v plain_len) ->
  quic_packet_r

val quic_decrypt_packet:
  st: pquic_state ->
  cid_len: u4 -> // Stupid, but required for short headers
  packet_len: U32.t ->
  packet: B.lbuffer U8.t (U32.v packet_len) ->
  output: B.pointer quic_packet_r ->
  ST U32.t
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True
  )

(**** QUIC API ****)

[@CAbstractStruct]
val quic_con: Type0
let pquic_con = B.pointer quic_con

type quic_result = U32.t

val quic_set_param:
  con: pquic_con ->
  param: U32.t ->
  value: B.buffer U8.t ->
  len: U32.t ->
  St quic_result
  
val quic_get_param:
  con: pquic_con ->
  param: U32.t ->
  len: B.pointer U32.t ->
  out: B.buffer U8.t ->
  St quic_result

[@CAbstractStruct]
val quic_stream: Type0
let pquic_stream = B.pointer quic_stream

noeq type quic_slice =
| Slice:
  length: U32.t ->
  buffer: B.lbuffer U8.t (U32.v length) ->
  quic_slice

noeq type quic_stream_event =
  | Stream_recv:
    offset: U64.t ->
    total_buffers_len: U32.t ->
    buffers_len: U32.t ->
    buffers: B.lbuffer quic_slice (U32.v buffers_len) ->
    flags: U8.t ->
    quic_stream_event
  | Stream_send_complete:
    cancelled: bool ->
    ctx: FStar.Dyn.dyn ->
    quic_stream_event
(*
  | Stream_send_abort:
    error: U16.t ->
    quic_stream_event
  | Stream_recv_abort:
    error: U16.t ->
    quic_stream_event
*)
  | Stream_closed:
    graceful: bool ->
    quic_stream_event

type quic_stream_cb =
  (s:pquic_stream ->
  ctx: FStar.Dyn.dyn ->
  event: quic_stream_event ->
  St quic_result)

val quic_stream_create:
  con: pquic_con ->
  flags: U32.t ->
  handler: quic_stream_cb ->
  context: FStar.Dyn.dyn ->
  St pquic_stream

val quic_stream_send:
  stream: pquic_stream ->
  inputs: B.buffer quic_slice ->
  inputs_len: U32.t ->
  flags: U32.t ->
  send_ctx: FStar.Dyn.dyn ->
  St quic_result

val quic_stream_close:
  st: pquic_stream ->
  flags: U32.t ->
  error_code: U16.t ->
  St quic_result

val quic_stream_free:
  pquic_stream ->
  St unit

