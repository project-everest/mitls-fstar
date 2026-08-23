module TLS13.Trace

#lang-pulse

open Pulse.Lib.Pervasives

module U32 = FStar.UInt32
module U64 = FStar.UInt64

(** Stable ATLAS trace event identifiers. The C header provides matching macro
    definitions because this external module is implemented by the embedding
    runtime. Trace arguments are metadata only; callers must never pass secret
    material, plaintext, or values derived from payload contents. Public and
    control-flow metadata such as lengths, tags, and sequence numbers are
    permitted. **)

inline_for_extraction let record_state_new : U32.t = 1000ul
inline_for_extraction let record_state_free : U32.t = 1001ul
inline_for_extraction let record_sequence_advance : U32.t = 1010ul
inline_for_extraction let record_sequence_restore : U32.t = 1011ul
inline_for_extraction let record_install_handshake_keys : U32.t = 1020ul
inline_for_extraction let record_install_application_keys : U32.t = 1021ul
inline_for_extraction let record_seal_begin : U32.t = 1030ul
inline_for_extraction let record_seal_success : U32.t = 1031ul
inline_for_extraction let record_seal_failure : U32.t = 1032ul
inline_for_extraction let record_open_begin : U32.t = 1040ul
inline_for_extraction let record_open_success : U32.t = 1041ul
inline_for_extraction let record_open_failure : U32.t = 1042ul

inline_for_extraction let client_new : U32.t = 2000ul
inline_for_extraction let client_free : U32.t = 2001ul
inline_for_extraction let client_local_event_begin : U32.t = 2010ul
inline_for_extraction let client_local_event_end : U32.t = 2011ul
inline_for_extraction let client_network_begin : U32.t = 2020ul
inline_for_extraction let client_network_need_more : U32.t = 2021ul
inline_for_extraction let client_network_decode_error : U32.t = 2022ul
inline_for_extraction let client_network_record : U32.t = 2023ul
inline_for_extraction let client_network_end : U32.t = 2024ul
inline_for_extraction let client_protected_head : U32.t = 2030ul
inline_for_extraction let client_protected_drain : U32.t = 2031ul
inline_for_extraction let client_protected_empty : U32.t = 2032ul
inline_for_extraction let client_protected_error : U32.t = 2033ul
inline_for_extraction let client_protected_buffer : U32.t = 2034ul
inline_for_extraction let client_cleartext_buffer : U32.t = 2035ul
inline_for_extraction let client_handshake_message : U32.t = 2040ul

inline_for_extraction let engine_new : U32.t = 2100ul
inline_for_extraction let engine_poll_begin : U32.t = 2110ul
inline_for_extraction let engine_poll_end : U32.t = 2111ul
inline_for_extraction let engine_feed_begin : U32.t = 2120ul
inline_for_extraction let engine_feed_end : U32.t = 2121ul
inline_for_extraction let engine_certificate_chain : U32.t = 2130ul
inline_for_extraction let engine_certificate_verified : U32.t = 2131ul
inline_for_extraction let engine_certificate_signature_verified : U32.t = 2132ul
inline_for_extraction let engine_send_application : U32.t = 2140ul
inline_for_extraction let engine_send_close : U32.t = 2141ul
inline_for_extraction let engine_free : U32.t = 2150ul

inline_for_extraction let server_new : U32.t = 3000ul
inline_for_extraction let server_free : U32.t = 3001ul
inline_for_extraction let server_local_event_begin : U32.t = 3010ul
inline_for_extraction let server_local_event_end : U32.t = 3011ul
inline_for_extraction let server_network_begin : U32.t = 3020ul
inline_for_extraction let server_network_need_more : U32.t = 3021ul
inline_for_extraction let server_network_decode_error : U32.t = 3022ul
inline_for_extraction let server_network_record : U32.t = 3023ul
inline_for_extraction let server_network_end : U32.t = 3024ul
inline_for_extraction let server_cleartext_buffer : U32.t = 3025ul
inline_for_extraction let server_handshake_message : U32.t = 3040ul

(** Runtime-only observational effect. Its empty separation-logic contract makes
    tracing irrelevant to TLS memory ownership and protocol proofs. **)
fn emit (event:U32.t) (arg0:U64.t) (arg1:U64.t) (arg2:U64.t)
  requires emp
  ensures emp
