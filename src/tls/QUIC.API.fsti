module QUIC.API

module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Error

module SAEAD = Spec.AEAD
module SH = Spec.Hash
module SQUIC = Spec.QUIC

module I32 = FStar.Int32
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(**** Current API of mitlsffi.h ****)

[@CAbstractStruct]
val quic_state: Type0
let pquic_state = B.pointer quic_state

type quic_process_ctx = {
  (* Inputs *)
  input: IB.buffer U8.t;
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

type quic_secret = {
  hash_alg: SH.alg;
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
  alg: aead_alg ->
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

type u2 = n:U16.t{U8.v n < 4}
type u4 = n:U16.t{U8.v n < 16}
type u62 = n:UInt64.t{UInt64.v n < pow2 62}
let add3 (n:u4) : n:U8.t{U8.v n <= 18} = if n = 0uy then 0uy else U8.(3uy +^ n)
type vlsize = n:U8.t{U8.v n == 1 \/ U8.v n == 2 \/ U8.v n == 4 \/ U8.v n == 8}

let vlen (n:u62) : vlsize =
  let open FStar.UInt64 in
  if n <^ 64ull then 1uy
  else if n <^ 16384ull then 2uy
  else if n <^ 1073741824ull then 4uy
  else 8uy

type quic_header =
  | Short:
    spin: U8.t ->
    phase: U8.t ->
    cid: B.buffer U8.t{B.length cid in l == 0 \/ (4 <= l /\ l <= 18)} ->
    header
  | Long:
    typ: u2 ->
    version: U32.t ->
    dcil: u4 ->
    scil: u4 ->
    dcid: B.lbuffer U8.t (U8.v (add3 dcil)) ->
    scid: B.lbuffer U8.t (U8.v (add3 scil)) ->
    plain_len: U16.t -> // Short due to limitations of AEAD spec
    header

type quic_process_ctx = {
  (* Inputs *)
  input: IB.buffer U8.t;
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

val quic_process:
  st: pquic_state ->
  ctx: B.pointer quic_process_ctx ->
  St U32.t

val quic_next_pn: st: pquic_state -> rw: rw -> St u62

val quic_encrypt_packet:
  pn_len: u2 ->
  h: B.pointer header ->
  plain: IB.buffer U8.t ->
  plain_len: U32.t{Long? h ==> Long?.plain_len h == plain_len}
  out: B.buffer U8.t ->
  out_len: U32.t ->
  St U32.t

type quic_packet_r = {
  pn_len:u2;
  pn: u62;
  h: header;
  plain: B.buffer U8.t;
  plain_len: U16.t;
}

val quic_decrypt_packet:
  cid_len: u4 -> // Stupid, but required for short headers
  packet: B.buffer U8.t ->
  packet_len: U32.t ->
  output: B.pointer quic_packet_r ->
  St U32.t

(**** QUIC API ****)

[@CAbstractStruct]
val quic_con: Type0
let pquic_con = B.pointer quic_con

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

type quic_slice = {
  buffer: B.buffer U8.t;
  length: U32.t
}

type quic_stream_event =
  | Stream_recv:
    offset: U64.t ->
    total_buffers_len: U32.t ->
    buffers: B.buffer quic_slice ->
    buffers_len: U32.t ->
    flags: U8.t ->
    quic_stream_event
  | Stream_send_complete:
    cancelled: bool ->
    ctx: nullptr ->
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
  ctx: nullptr ->
  event: quic_stream_event ->
  St quic_result)

val quic_stream_create:
  con: pquic_con ->
  flags: U32.t ->
  handler: quic_stream_cb ->
  context: nullptr ->
  St pquic_stream

val quic_stream_send:
  stream: pquic_stream ->
  inputs: B.buffer quic_slice ->
  inputs_len: U32.t ->
  flags: U32.t ->
  send_ctx: nullptr ->
  St quic_result

val quic_stream_close:
  st: pquic_stream ->
  flags: U32.t ->
  error_code: U16.t ->
  St quic_result

val quic_stream_free:
  pquic_stream ->
  St unit

