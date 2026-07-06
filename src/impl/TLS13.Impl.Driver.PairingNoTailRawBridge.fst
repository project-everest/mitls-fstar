module TLS13.Impl.Driver.PairingNoTailRawBridge

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWS = TLS13.ConnectionState.ProtectedWireStream
module Seq = FStar.Seq
module Tac = FStar.Tactics
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

let lemma_parse_record_wire_of_sent_supported_client_hello
  (ch:M.client_hello)
  (raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_client_hello_wire_profile ch /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          raw)
      (ensures
        exists fragment.
          W.parse_record_wire raw ==
            Some (T.Handshake, fragment, B.length raw))
=
  let fragment = W.serialize_handshake (M.ClientHello ch) in
  W.lemma_serialize_tls_message_handshake (M.ClientHello ch);
  WFL.lemma_serialize_handshake_client_hello_record_bound ch;
  WFL.lemma_parse_record_wire_serialize_record T.Handshake fragment;
  assert (CS.serialized_cleartext_tls_message
    (M.TlsHandshake (M.ClientHello ch)) ==
    W.serialize_record T.Handshake fragment);
  assert (Seq.equal raw (W.serialize_record T.Handshake fragment));
  Seq.lemma_eq_elim raw (W.serialize_record T.Handshake fragment);
  assert (W.parse_record_wire raw ==
    Some (T.Handshake, fragment, B.length raw));
  assert (exists fragment'.
    W.parse_record_wire raw ==
      Some (T.Handshake, fragment', B.length raw))

let lemma_parse_record_wire_of_received_client_hello
  (ch:M.client_hello)
  (raw:B.bytes)
  : Lemma
      (requires
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          raw)
      (ensures
        exists fragment.
          W.parse_record_wire raw ==
            Some (T.Handshake, fragment, B.length raw))
=
  eliminate exists (fragment:B.bytes).
    W.parse_record_wire raw ==
      Some (T.Handshake, fragment, B.length raw) /\
    W.parse_tls_message T.Handshake fragment ==
      Some (M.TlsHandshake (M.ClientHello ch))
  returns
    exists fragment'.
      W.parse_record_wire raw ==
        Some (T.Handshake, fragment', B.length raw)
  with _.
  ( assert (exists fragment'.
      W.parse_record_wire raw ==
        Some (T.Handshake, fragment', B.length raw)) )

let lemma_parse_record_wire_of_cleartext_server_hello
  (sh:M.server_hello)
  (raw:B.bytes)
  : Lemma
      (requires
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          raw)
      (ensures
        exists fragment.
          W.parse_record_wire raw ==
            Some (T.Handshake, fragment, B.length raw))
=
  let fragment = W.serialize_handshake (M.ServerHello sh) in
  W.lemma_serialize_server_hello_len sh;
  W.lemma_serialize_tls_message_handshake (M.ServerHello sh);
  assert (M.server_hello_max_len <= 16640);
  assert (B.length fragment <= 16640);
  WFL.lemma_parse_record_wire_serialize_record T.Handshake fragment;
  assert (CS.serialized_cleartext_tls_message
    (M.TlsHandshake (M.ServerHello sh)) ==
    W.serialize_record T.Handshake fragment);
  assert (Seq.equal raw (W.serialize_record T.Handshake fragment));
  Seq.lemma_eq_elim raw (W.serialize_record T.Handshake fragment);
  assert (W.parse_record_wire raw ==
    Some (T.Handshake, fragment, B.length raw));
  assert (exists fragment'.
    W.parse_record_wire raw ==
      Some (T.Handshake, fragment', B.length raw))

let lemma_parse_record_wire_of_received_server_hello
  (sh:M.server_hello)
  (raw:B.bytes)
  : Lemma
      (requires
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          raw)
      (ensures
        exists fragment.
          W.parse_record_wire raw ==
            Some (T.Handshake, fragment, B.length raw))
=
  assert (CS.cleartext_tls_message_raw
    (M.TlsHandshake (M.ServerHello sh))
    raw);
  lemma_parse_record_wire_of_cleartext_server_hello sh raw

let lemma_event_raw_delta_legal_local
  (model:CS.connection_model)
  (ev:CS.local_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnLocalEvent ev)
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        Seq.equal delta_received B.empty)
=
  ()

let lemma_event_raw_delta_legal_sent_client_hello
  (model:CS.connection_model)
  (ch:M.client_hello)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }))
          delta_sent
          delta_received)
      (ensures
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          delta_sent /\
        Seq.equal delta_received B.empty)
=
  ()

let lemma_event_raw_delta_legal_received_client_hello
  (model:CS.connection_model)
  (ch:M.client_hello)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }))
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          delta_received)
=
  ()

let lemma_event_raw_delta_legal_received_server_hello
  (model:CS.connection_model)
  (sh:M.server_hello)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }))
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          delta_received)
=
  ()

let lemma_event_raw_delta_legal_sent_server_hello
  (model:CS.connection_model)
  (sh:M.server_hello)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }))
          delta_sent
          delta_received)
      (ensures
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          delta_sent /\
        Seq.equal delta_received B.empty)
=
  ()

let lemma_client_prefix_raw_slices
  (model0:CS.connection_model)
  (client_start:CS.handshake_start)
  (client_ch:M.client_hello)
  (client_sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
           }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           client_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists client_ch_raw client_sh_raw sent_tail received_tail.
          Seq.equal raw_sent (B.append client_ch_raw sent_tail) /\
          Seq.equal raw_received (B.append client_sh_raw received_tail) /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello client_ch))
            client_ch_raw /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello client_sh))
            client_sh_raw)
=
  let ev0 = CS.ConnLocalEvent (CS.LocalStartHandshake client_start) in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
  }) in
  let ev2 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
  }) in
  let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: ev3 :: client_rest)
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
    CS.legal_event model0 ev0 /\
    CS.step_model model0 ev0 == Some model1 /\
    CS.event_raw_delta_legal model0 ev0 delta0_sent delta0_received /\
    Seq.equal raw_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal raw_received (B.append delta0_received tail0_received) /\
    CS.conn_events_raw_replay
      model1
      (ev1 :: ev2 :: ev3 :: client_rest)
      tail0_sent
      tail0_received
      final_model
  returns
    exists client_ch_raw client_sh_raw sent_tail received_tail.
      Seq.equal raw_sent (B.append client_ch_raw sent_tail) /\
      Seq.equal raw_received (B.append client_sh_raw received_tail) /\
      CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello client_ch))
        client_ch_raw /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ServerHello client_sh))
        client_sh_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: ev3 :: client_rest)
      tail0_sent
      tail0_received
      final_model;
    eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
      CS.legal_event model1 ev1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_raw_replay
        model2
        (ev2 :: ev3 :: client_rest)
        tail1_sent
        tail1_received
        final_model
    returns
      exists client_ch_raw client_sh_raw sent_tail received_tail.
        Seq.equal raw_sent (B.append client_ch_raw sent_tail) /\
        Seq.equal raw_received (B.append client_sh_raw received_tail) /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        (ev3 :: client_rest)
        tail1_sent
        tail1_received
        final_model;
      eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
        CS.legal_event model2 ev2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_raw_replay
          model3
          (ev3 :: client_rest)
          tail2_sent
          tail2_received
          final_model
      returns
        exists client_ch_raw client_sh_raw sent_tail received_tail.
          Seq.equal raw_sent (B.append client_ch_raw sent_tail) /\
          Seq.equal raw_received (B.append client_sh_raw received_tail) /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello client_ch))
            client_ch_raw /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello client_sh))
            client_sh_raw
      with _.
      (
        lemma_event_raw_delta_legal_local
          model0
          (CS.LocalStartHandshake client_start)
          delta0_sent
          delta0_received;
        lemma_event_raw_delta_legal_sent_client_hello
          model1
          client_ch
          delta1_sent
          delta1_received;
        lemma_event_raw_delta_legal_received_server_hello
          model2
          client_sh
          delta2_sent
          delta2_received;
        assert (Seq.equal delta0_sent B.empty);
        assert (Seq.equal delta0_received B.empty);
        assert (CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          delta1_sent);
        assert (Seq.equal delta1_received B.empty);
        assert (Seq.equal delta2_sent B.empty);
        assert (CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          delta2_received);
        Seq.lemma_eq_elim delta0_sent B.empty;
        Seq.lemma_eq_elim delta0_received B.empty;
        Seq.lemma_eq_elim delta1_received B.empty;
        Seq.lemma_eq_elim delta2_sent B.empty;
        CL.lemma_append_empty_left tail0_sent;
        CL.lemma_append_empty_left tail0_received;
        CL.lemma_append_empty_left tail1_received;
        assert (Seq.equal raw_sent tail0_sent);
        assert (Seq.equal raw_received tail0_received);
        assert (Seq.equal tail0_received tail1_received);
        Seq.lemma_eq_elim raw_sent tail0_sent;
        Seq.lemma_eq_elim raw_received tail0_received;
        Seq.lemma_eq_elim tail0_received tail1_received;
        assert (Seq.equal raw_sent (B.append delta1_sent tail1_sent));
        assert (Seq.equal raw_received (B.append delta2_received tail2_received));
        assert (exists client_ch_raw client_sh_raw sent_tail received_tail.
          Seq.equal raw_sent (B.append client_ch_raw sent_tail) /\
          Seq.equal raw_received (B.append client_sh_raw received_tail) /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello client_ch))
            client_ch_raw /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello client_sh))
            client_sh_raw)
      )
    )
  )

let lemma_sent_server_hello_head_raw_slice
  (model:CS.connection_model)
  (server_sh:M.server_hello)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
          }) :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_sh_raw sent_tail.
          Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello server_sh))
            server_sh_raw)
=
  let ev = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model
    ev
    rest
    raw_sent
    raw_received
    final_model;
  eliminate exists
    (model1:CS.connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    CS.legal_event model ev /\
    CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay
      model1
      rest
      tail_sent
      tail_received
      final_model
  returns
    exists server_sh_raw sent_tail.
      Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
      CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ServerHello server_sh))
        server_sh_raw
  with _.
  (
    lemma_event_raw_delta_legal_sent_server_hello
      model
      server_sh
      delta_sent
      delta_received;
    assert (CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello server_sh))
      delta_sent);
    assert (exists server_sh_raw sent_tail.
      Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
      CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ServerHello server_sh))
        server_sh_raw)
  )

let lemma_server_prefix_raw_slices
  (model0:CS.connection_model)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:M.server_hello)
  (server_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
           }) ::
           server_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw server_sh_raw sent_tail received_tail.
          Seq.equal raw_received (B.append server_ch_raw received_tail) /\
          Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello server_sh))
            server_sh_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
  }) in
  let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let ev4 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: ev3 :: ev4 :: server_rest)
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
    CS.legal_event model0 ev0 /\
    CS.step_model model0 ev0 == Some model1 /\
    CS.event_raw_delta_legal model0 ev0 delta0_sent delta0_received /\
    Seq.equal raw_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal raw_received (B.append delta0_received tail0_received) /\
    CS.conn_events_raw_replay
      model1
      (ev1 :: ev2 :: ev3 :: ev4 :: server_rest)
      tail0_sent
      tail0_received
      final_model
  returns
    exists server_ch_raw server_sh_raw sent_tail received_tail.
      Seq.equal raw_received (B.append server_ch_raw received_tail) /\
      Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello server_ch))
        server_ch_raw /\
      CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ServerHello server_sh))
        server_sh_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: ev3 :: ev4 :: server_rest)
      tail0_sent
      tail0_received
      final_model;
    eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
      CS.legal_event model1 ev1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_raw_replay
        model2
        (ev2 :: ev3 :: ev4 :: server_rest)
        tail1_sent
        tail1_received
        final_model
    returns
      exists server_ch_raw server_sh_raw sent_tail received_tail.
        Seq.equal raw_received (B.append server_ch_raw received_tail) /\
        Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        (ev3 :: ev4 :: server_rest)
        tail1_sent
        tail1_received
        final_model;
      eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
        CS.legal_event model2 ev2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_raw_replay
          model3
          (ev3 :: ev4 :: server_rest)
          tail2_sent
          tail2_received
          final_model
      returns
        exists server_ch_raw server_sh_raw sent_tail received_tail.
          Seq.equal raw_received (B.append server_ch_raw received_tail) /\
          Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello server_sh))
            server_sh_raw
      with _.
      (
        PWR.lemma_conn_events_raw_replay_head
          model3
          ev3
          (ev4 :: server_rest)
          tail2_sent
          tail2_received
          final_model;
        eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
          CS.legal_event model3 ev3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.event_raw_delta_legal model3 ev3 delta3_sent delta3_received /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_raw_replay
            model4
            (ev4 :: server_rest)
            tail3_sent
            tail3_received
            final_model
        returns
          exists server_ch_raw server_sh_raw sent_tail received_tail.
            Seq.equal raw_received (B.append server_ch_raw received_tail) /\
            Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
            CS.received_cleartext_tls_message_raw
              (M.TlsHandshake (M.ClientHello server_ch))
              server_ch_raw /\
            CS.cleartext_tls_message_raw
              (M.TlsHandshake (M.ServerHello server_sh))
              server_sh_raw
        with _.
        (
          lemma_sent_server_hello_head_raw_slice
            model4
            server_sh
            server_rest
            tail3_sent
            tail3_received
            final_model;
          lemma_event_raw_delta_legal_local
            model0
            CS.LocalStartServer
            delta0_sent
            delta0_received;
          lemma_event_raw_delta_legal_received_client_hello
            model1
            server_ch
            delta1_sent
            delta1_received;
          lemma_event_raw_delta_legal_local
            model2
            (CS.LocalSelectServerParameters selection)
            delta2_sent
            delta2_received;
          lemma_event_raw_delta_legal_local
            model3
            (CS.LocalDeriveSharedSecret server_shared)
            delta3_sent
            delta3_received;
          assert (Seq.equal delta0_sent B.empty);
          assert (Seq.equal delta0_received B.empty);
          assert (Seq.equal delta1_sent B.empty);
          assert (CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            delta1_received);
          assert (Seq.equal delta2_sent B.empty);
          assert (Seq.equal delta2_received B.empty);
          assert (Seq.equal delta3_sent B.empty);
          assert (Seq.equal delta3_received B.empty);
          Seq.lemma_eq_elim delta0_sent B.empty;
          Seq.lemma_eq_elim delta0_received B.empty;
          Seq.lemma_eq_elim delta1_sent B.empty;
          Seq.lemma_eq_elim delta2_sent B.empty;
          Seq.lemma_eq_elim delta2_received B.empty;
          Seq.lemma_eq_elim delta3_sent B.empty;
          Seq.lemma_eq_elim delta3_received B.empty;
          CL.lemma_append_empty_left tail0_sent;
          CL.lemma_append_empty_left tail0_received;
          CL.lemma_append_empty_left tail1_sent;
          CL.lemma_append_empty_left tail2_sent;
          CL.lemma_append_empty_left tail2_received;
          CL.lemma_append_empty_left tail3_sent;
          CL.lemma_append_empty_left tail3_received;
          assert (Seq.equal raw_sent tail0_sent);
          assert (Seq.equal raw_received tail0_received);
          assert (Seq.equal tail0_sent tail1_sent);
          assert (Seq.equal tail1_sent tail2_sent);
          assert (Seq.equal tail2_sent tail3_sent);
          Seq.lemma_eq_elim raw_sent tail0_sent;
          Seq.lemma_eq_elim raw_received tail0_received;
          Seq.lemma_eq_elim tail0_sent tail1_sent;
          Seq.lemma_eq_elim tail1_sent tail2_sent;
          Seq.lemma_eq_elim tail2_sent tail3_sent;
          assert (Seq.equal raw_received
            (B.append delta1_received tail1_received));
          eliminate exists
            (server_sh_raw:B.bytes)
            (server_sent_tail:B.bytes).
            Seq.equal tail3_sent (B.append server_sh_raw server_sent_tail) /\
            CS.cleartext_tls_message_raw
              (M.TlsHandshake (M.ServerHello server_sh))
              server_sh_raw
          returns
            exists server_ch_raw server_sh_raw' sent_tail received_tail.
              Seq.equal raw_received (B.append server_ch_raw received_tail) /\
              Seq.equal raw_sent (B.append server_sh_raw' sent_tail) /\
              CS.received_cleartext_tls_message_raw
                (M.TlsHandshake (M.ClientHello server_ch))
                server_ch_raw /\
              CS.cleartext_tls_message_raw
                (M.TlsHandshake (M.ServerHello server_sh))
                server_sh_raw'
          with _.
          (
            assert (Seq.equal raw_sent
              (B.append server_sh_raw server_sent_tail));
            assert (exists server_ch_raw server_sh_raw' sent_tail received_tail.
              Seq.equal raw_received (B.append server_ch_raw received_tail) /\
              Seq.equal raw_sent (B.append server_sh_raw' sent_tail) /\
              CS.received_cleartext_tls_message_raw
                (M.TlsHandshake (M.ClientHello server_ch))
                server_ch_raw /\
              CS.cleartext_tls_message_raw
                (M.TlsHandshake (M.ServerHello server_sh))
                server_sh_raw')
          )
        )
      )
    )
  )

let lemma_normalized_cleartext_raw_wire_bridge_from_role_local_prefixes
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:M.client_hello)
  (client_sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:M.server_hello)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        role_local_cleartext_prefix_shape
          client
          server
          client_start
          client_ch
          client_sh
          client_shared
          client_rest
          server_ch
          selection
          server_shared
          server_sh
          server_rest /\
        WFL.supported_client_hello_wire_profile client_ch /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        CS.paired_wire_logs client server)
      (ensures
        normalized_cleartext_raw_wire_bridge
          client_ch
          server_ch
          client_sh
          server_sh)
=
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  assert (CS.conn_events_raw_replay
    client_model0
    (CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
     CS.ConnNetworkEvent ({
       CL.message_direction = CL.Sent;
       CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
     }) ::
     CS.ConnNetworkEvent ({
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
     }) ::
     CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
     client_rest)
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
  assert (CS.conn_events_raw_replay
    server_model0
    (CS.ConnLocalEvent CS.LocalStartServer ::
     CS.ConnNetworkEvent ({
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
     }) ::
     CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
     CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
     CS.ConnNetworkEvent ({
       CL.message_direction = CL.Sent;
       CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
     }) ::
     server_rest)
    server.CS.cs_wire_log.CL.raw_sent
    server.CS.cs_wire_log.CL.raw_received
    server.CS.cs_model);
  lemma_client_prefix_raw_slices
    client_model0
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  eliminate exists client_ch_raw client_sh_raw client_sent_tail client_received_tail.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_sent_tail) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append client_sh_raw client_received_tail) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello client_sh))
      client_sh_raw
  returns
    normalized_cleartext_raw_wire_bridge
      client_ch
      server_ch
      client_sh
      server_sh
  with _.
  (
    lemma_server_prefix_raw_slices
      server_model0
      server_ch
      selection
      server_shared
      server_sh
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists server_ch_raw server_sh_raw server_sent_tail server_received_tail.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append server_ch_raw server_received_tail) /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append server_sh_raw server_sent_tail) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello server_ch))
        server_ch_raw /\
      CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ServerHello server_sh))
        server_sh_raw
    returns
      normalized_cleartext_raw_wire_bridge
        client_ch
        server_ch
        client_sh
        server_sh
    with _.
    (
      lemma_parse_record_wire_of_sent_supported_client_hello
        client_ch
        client_ch_raw;
      lemma_parse_record_wire_of_received_client_hello
        server_ch
        server_ch_raw;
      eliminate exists (client_ch_fragment:B.bytes).
        W.parse_record_wire client_ch_raw ==
          Some (T.Handshake, client_ch_fragment, B.length client_ch_raw)
      returns
        normalized_cleartext_raw_wire_bridge
          client_ch
          server_ch
          client_sh
          server_sh
      with _.
      (
        eliminate exists (server_ch_fragment:B.bytes).
          W.parse_record_wire server_ch_raw ==
            Some (T.Handshake, server_ch_fragment, B.length server_ch_raw)
        returns
          normalized_cleartext_raw_wire_bridge
            client_ch
            server_ch
            client_sh
            server_sh
        with _.
        (
          PWS.lemma_equal_stream_record_head_lengths
            client.CS.cs_wire_log.CL.raw_sent
            server.CS.cs_wire_log.CL.raw_received
            client_ch_raw
            client_sent_tail
            server_ch_raw
            server_received_tail
            T.Handshake
            client_ch_fragment
            T.Handshake
            server_ch_fragment;
          PWS.lemma_append_heads_equal_same_len
            client_ch_raw
            client_sent_tail
            server_ch_raw
            server_received_tail;
          assert (Seq.equal client_ch_raw server_ch_raw);
          lemma_parse_record_wire_of_cleartext_server_hello
            server_sh
            server_sh_raw;
          lemma_parse_record_wire_of_received_server_hello
            client_sh
            client_sh_raw;
          eliminate exists (server_sh_fragment:B.bytes).
            W.parse_record_wire server_sh_raw ==
              Some (T.Handshake, server_sh_fragment, B.length server_sh_raw)
          returns
            normalized_cleartext_raw_wire_bridge
              client_ch
              server_ch
              client_sh
              server_sh
          with _.
          (
            eliminate exists (client_sh_fragment:B.bytes).
              W.parse_record_wire client_sh_raw ==
                Some (T.Handshake, client_sh_fragment, B.length client_sh_raw)
            returns
              normalized_cleartext_raw_wire_bridge
                client_ch
                server_ch
                client_sh
                server_sh
            with _.
            (
              PWS.lemma_equal_stream_record_head_lengths
                server.CS.cs_wire_log.CL.raw_sent
                client.CS.cs_wire_log.CL.raw_received
                server_sh_raw
                server_sent_tail
                client_sh_raw
                client_received_tail
                T.Handshake
                server_sh_fragment
                T.Handshake
                client_sh_fragment;
              PWS.lemma_append_heads_equal_same_len
                server_sh_raw
                server_sent_tail
                client_sh_raw
                client_received_tail;
              assert (Seq.equal server_sh_raw client_sh_raw);
              assert (normalized_cleartext_raw_wire_bridge
                client_ch
                server_ch
                client_sh
                server_sh)
            )
          )
        )
      )
    )
  )
