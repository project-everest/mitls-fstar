module TLS13.Impl.Driver.PairingNoTailServerPostHelloShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTSFShape = TLS13.Impl.Driver.PairingNoTailServerFlightShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module SD = TLS13.Impl.Server.Driver

noextract
let conn_event_is_ccs
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnNetworkEvent m -> m.CL.message_value == M.TlsChangeCipherSpec
  | _ -> False

noextract
let trace_no_ccs
  (trace:list CS.conn_event)
  : prop =
  forall ev. FStar.List.Tot.mem ev trace ==> ~ (conn_event_is_ccs ev)

noextract
let server_no_tail_no_ccs_application_ready_boundary
  (server:CS.connection_state)
  : prop =
  SD.server_driver_application_ready server /\
  FStar.List.Tot.length server.CS.cs_event_log == 16 /\
  trace_no_ccs server.CS.cs_event_log

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

noextract
let server_no_tail_post_two_handshake_installs_tail_order
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
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    PNTSFShape.server_post_two_handshake_installs_tail_order rest

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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

val lemma_server_no_tail_no_ccs_post_server_hello_suffix_shape
  (server:CS.connection_state)
  : Lemma
      (requires server_no_tail_no_ccs_application_ready_boundary server)
      (ensures server_no_tail_post_server_hello_suffix_shape server)

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape_with_start_spine16
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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

val lemma_server_no_tail_post_two_handshake_installs_tail_order_for_split
  (server:CS.connection_state)
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  (rest:list CS.conn_event)
  : Lemma
      (requires
        server_no_tail_post_two_handshake_installs_tail_order server /\
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            (e5 :: e6 :: rest))
      (ensures
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
        PNTSFShape.server_post_two_handshake_installs_tail_order rest)

val lemma_clean16_no_tail_valid_byte_traces_server_next_two_events_handshake_installs
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        PNTSS.server_no_tail_next_two_events_handshake_installs server)

val lemma_clean16_no_tail_valid_byte_traces_server_next_two_events_handshake_install_cover
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        PNTSS.server_no_tail_next_two_events_handshake_install_cover server)

val lemma_server_no_tail_no_ccs_post_two_handshake_installs_tail_order
  (server:CS.connection_state)
  : Lemma
      (requires server_no_tail_no_ccs_application_ready_boundary server)
      (ensures server_no_tail_post_two_handshake_installs_tail_order server)

val lemma_clean16_no_tail_valid_byte_traces_server_post_two_handshake_installs_tail_order
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        server_no_tail_post_two_handshake_installs_tail_order server)
