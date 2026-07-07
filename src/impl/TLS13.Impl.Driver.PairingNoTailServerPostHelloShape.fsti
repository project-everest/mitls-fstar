module TLS13.Impl.Driver.PairingNoTailServerPostHelloShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation

(**
  Server-side no-tail post-[ServerHello] milestone packaged from the clean16
  paired byte-trace hypotheses.

  This deliberately states only the cleartext-prefix/suffix split that is
  already derivable from the normalized clean16 stack: the server event log has
  the five-event cleartext prefix ending in [Sent ServerHello], followed by two
  named post-[ServerHello] slots and a nine-event residual suffix (eleven
  post-[ServerHello] events total) required by the corrected length-16 server
  no-tail boundary.  The stronger two-handshake-install predicate remains
  [PNTSS.server_no_tail_next_two_events_handshake_installs].
**)
noextract
let server_no_tail_post_server_hello_suffix_shape
  (server:CS.connection_state)
  : prop =
  exists ch selection server_shared sh e5 e6 rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    FStar.List.Tot.length rest == 9

noextract
let server_no_tail_post_server_hello_suffix_shape_with_start_spine16
  (server:CS.connection_state)
  : prop =
  server_no_tail_post_server_hello_suffix_shape server /\
  PNTSS.server_no_tail_start_spine16 server

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_no_tail_post_server_hello_suffix_shape server)

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape_with_start_spine16
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        server_no_tail_post_server_hello_suffix_shape_with_start_spine16
          server)
