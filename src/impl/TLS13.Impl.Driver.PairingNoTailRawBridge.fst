module TLS13.Impl.Driver.PairingNoTailRawBridge

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CSL = TLS13.ConnectionState.Lemmas
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module M = TLS13.Messages
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWS = TLS13.ConnectionState.ProtectedWireStream
module Seq = FStar.Seq
module Tac = FStar.Tactics
module T = TLS13.Types
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module SHPB = TLS13.Wire.Spec.Reveal.ServerHello.Parseback

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

let lemma_server_hello_key_share_from_sent_supported_and_received_projection
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (client_sh:M.server_hello)
  (server_sh:M.server_hello)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  : Lemma
      (requires
        CT.network_input_message_projection
          st0
          content_type
          fragment
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        Seq.equal server_sh_raw client_sh_raw /\
        W.parse_supported_server_hello
          (W.serialize_handshake (M.ServerHello server_sh)) == Some server_sh)
      (ensures
        CS.server_hello_key_share client_sh ==
        CS.server_hello_key_share server_sh)
=
  eliminate exists (ct:T.content_type).
    TLS13.Impl.Messages.content_type_matches content_type ct /\
    W.parse_tls_message ct fragment ==
      Some (M.TlsHandshake (M.ServerHello client_sh))
  returns
    CS.server_hello_key_share client_sh ==
    CS.server_hello_key_share server_sh
  with _.
  (
    eliminate exists (outer_ct:T.content_type) (outer_fragment:B.bytes).
      W.parse_record_wire client_sh_raw ==
        Some (outer_ct, outer_fragment, B.length client_sh_raw) /\
      (if outer_ct == T.Application_data
       then CT.protected_decoder_fragment_relation st0 content_type fragment client_sh_raw
       else
         TLS13.Impl.Messages.content_type_matches content_type outer_ct /\
         Seq.equal fragment outer_fragment)
    returns
      CS.server_hello_key_share client_sh ==
      CS.server_hello_key_share server_sh
    with _.
    (
      let sent_fragment = W.serialize_handshake (M.ServerHello server_sh) in
      lemma_parse_record_wire_of_cleartext_server_hello server_sh server_sh_raw;
      W.lemma_serialize_server_hello_len server_sh;
      assert (M.server_hello_max_len <= 16640);
      assert (B.length sent_fragment <= 16640);
      W.lemma_serialize_tls_message_handshake (M.ServerHello server_sh);
      assert (CS.serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello server_sh)) ==
        W.serialize_record T.Handshake sent_fragment);
      assert (Seq.equal
        server_sh_raw
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ServerHello server_sh))));
      WFL.lemma_parse_record_wire_serialize_record T.Handshake sent_fragment;
      assert (Seq.equal
        server_sh_raw
        (W.serialize_record T.Handshake sent_fragment));
      Seq.lemma_eq_elim server_sh_raw client_sh_raw;
      assert (W.parse_record_wire client_sh_raw ==
        Some (T.Handshake, sent_fragment, B.length client_sh_raw));
      assert (outer_ct == T.Handshake);
      assert (Seq.equal fragment sent_fragment);
      Seq.lemma_eq_elim fragment sent_fragment;
      match ct with
      | T.Handshake ->
        assert (W.parse_tls_message T.Handshake sent_fragment ==
          Some (M.TlsHandshake (M.ServerHello client_sh)));
        W.lemma_parse_supported_server_hello_ok sent_fragment;
        W.lemma_parse_supported_server_hello_fields sent_fragment;
        assert (B.length server_sh.M.body == 0);
        assert (server_sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256);
        SHPB.lemma_parse_tls_message_serialize_server_hello_key_share
          server_sh
          client_sh;
        assert (Seq.equal client_sh.M.key_share server_sh.M.key_share)
      | _ ->
        assert False
    )
  )

let lemma_cleartext_change_cipher_spec_parse_record
  (raw:B.bytes)
  : Lemma
      (requires
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          raw)
      (ensures
        W.parse_record_wire raw ==
          Some (T.Change_cipher_spec, B.singleton 1uy, B.length raw))
=
  let fragment = B.singleton 1uy in
  W.lemma_serialize_tls_message_change_cipher_spec();
  assert (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec ==
    W.serialize_record T.Change_cipher_spec fragment);
  assert (B.length fragment <= 16640);
  WFL.lemma_parse_record_wire_serialize_record T.Change_cipher_spec fragment;
  assert (Seq.equal raw (W.serialize_record T.Change_cipher_spec fragment));
  Seq.lemma_eq_elim raw (W.serialize_record T.Change_cipher_spec fragment);
  assert (W.parse_record_wire raw ==
    Some (T.Change_cipher_spec, fragment, B.length raw))

let lemma_sent_supported_client_hello_raw_not_change_cipher_spec
  (ch:M.client_hello)
  (client_hello_raw:B.bytes)
  (ccs_raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_client_hello_wire_profile ch /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          client_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw /\
        Seq.equal client_hello_raw ccs_raw)
      (ensures False)
=
  lemma_parse_record_wire_of_sent_supported_client_hello ch client_hello_raw;
  lemma_cleartext_change_cipher_spec_parse_record ccs_raw;
  eliminate exists (fragment:B.bytes).
    W.parse_record_wire client_hello_raw ==
      Some (T.Handshake, fragment, B.length client_hello_raw)
  returns False
  with _.
  (
    Seq.lemma_eq_elim client_hello_raw ccs_raw;
    assert (W.parse_record_wire client_hello_raw ==
      Some (T.Change_cipher_spec, B.singleton 1uy, B.length ccs_raw));
    assert (
      Some (T.Handshake, fragment, B.length client_hello_raw) ==
      Some (T.Change_cipher_spec, B.singleton 1uy, B.length ccs_raw));
    assert False
  )

let lemma_received_server_hello_raw_not_change_cipher_spec
  (sh:M.server_hello)
  (server_hello_raw:B.bytes)
  (ccs_raw:B.bytes)
  : Lemma
      (requires
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          server_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw /\
        Seq.equal server_hello_raw ccs_raw)
      (ensures False)
=
  lemma_parse_record_wire_of_received_server_hello sh server_hello_raw;
  lemma_cleartext_change_cipher_spec_parse_record ccs_raw;
  eliminate exists (fragment:B.bytes).
    W.parse_record_wire server_hello_raw ==
      Some (T.Handshake, fragment, B.length server_hello_raw)
  returns False
  with _.
  (
    Seq.lemma_eq_elim server_hello_raw ccs_raw;
    assert (W.parse_record_wire server_hello_raw ==
      Some (T.Change_cipher_spec, B.singleton 1uy, B.length ccs_raw));
    assert (
      Some (T.Handshake, fragment, B.length server_hello_raw) ==
      Some (T.Change_cipher_spec, B.singleton 1uy, B.length ccs_raw));
    assert False
  )

let lemma_application_data_raw_not_change_cipher_spec
  (application_raw:B.bytes)
  (ccs_raw:B.bytes)
  : Lemma
      (requires
        CS.raw_records_exactly application_raw T.Application_data 1 /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw /\
        Seq.equal application_raw ccs_raw)
      (ensures False)
=
  CSL.lemma_raw_records_exactly_one_parse_record
    application_raw
    T.Application_data;
  lemma_cleartext_change_cipher_spec_parse_record ccs_raw;
  eliminate exists (fragment:B.bytes).
    W.parse_record application_raw ==
      Some (T.Application_data, fragment, B.length application_raw)
  returns False
  with _.
  (
    W.lemma_parse_record_implies_parse_record_wire application_raw;
    assert (W.parse_record_wire application_raw ==
      Some (T.Application_data, fragment, B.length application_raw));
    Seq.lemma_eq_elim application_raw ccs_raw;
    assert (W.parse_record_wire application_raw ==
      Some (T.Change_cipher_spec, B.singleton 1uy, B.length ccs_raw));
    assert (
      Some (T.Application_data, fragment, B.length application_raw) ==
      Some (T.Change_cipher_spec, B.singleton 1uy, B.length ccs_raw));
    assert False
  )

let lemma_equal_stream_head_sent_supported_client_hello_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (ch:M.client_hello)
  (client_hello_raw:B.bytes)
  (client_tail:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append client_hello_raw client_tail) /\
        Seq.equal right_stream (B.append ccs_raw ccs_tail) /\
        WFL.supported_client_hello_wire_profile ch /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          client_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)
=
  lemma_parse_record_wire_of_sent_supported_client_hello ch client_hello_raw;
  lemma_cleartext_change_cipher_spec_parse_record ccs_raw;
  eliminate exists (client_fragment:B.bytes).
    W.parse_record_wire client_hello_raw ==
      Some (T.Handshake, client_fragment, B.length client_hello_raw)
  returns False
  with _.
  (
    PWS.lemma_equal_stream_record_head_lengths
      left_stream
      right_stream
      client_hello_raw
      client_tail
      ccs_raw
      ccs_tail
      T.Handshake
      client_fragment
      T.Change_cipher_spec
      (B.singleton 1uy);
    assert (B.length client_hello_raw == B.length ccs_raw);
    Seq.lemma_eq_elim left_stream right_stream;
    Seq.lemma_eq_elim left_stream (B.append client_hello_raw client_tail);
    Seq.lemma_eq_elim right_stream (B.append ccs_raw ccs_tail);
    assert (Seq.equal
      (B.append client_hello_raw client_tail)
      (B.append ccs_raw ccs_tail));
    PWS.lemma_append_heads_equal_same_len
      client_hello_raw
      client_tail
      ccs_raw
      ccs_tail;
    assert (Seq.equal client_hello_raw ccs_raw);
    lemma_sent_supported_client_hello_raw_not_change_cipher_spec
      ch
      client_hello_raw
      ccs_raw
  )

let lemma_equal_stream_head_application_data_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (application_raw:B.bytes)
  (application_tail:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append application_raw application_tail) /\
        Seq.equal right_stream (B.append ccs_raw ccs_tail) /\
        CS.raw_records_exactly application_raw T.Application_data 1 /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)
=
  CSL.lemma_raw_records_exactly_one_parse_record
    application_raw
    T.Application_data;
  lemma_cleartext_change_cipher_spec_parse_record ccs_raw;
  eliminate exists (application_fragment:B.bytes).
    W.parse_record application_raw ==
      Some (T.Application_data, application_fragment, B.length application_raw)
  returns False
  with _.
  (
    W.lemma_parse_record_implies_parse_record_wire application_raw;
    assert (W.parse_record_wire application_raw ==
      Some (T.Application_data, application_fragment, B.length application_raw));
    PWS.lemma_equal_stream_record_head_lengths
      left_stream
      right_stream
      application_raw
      application_tail
      ccs_raw
      ccs_tail
      T.Application_data
      application_fragment
      T.Change_cipher_spec
      (B.singleton 1uy);
    assert (B.length application_raw == B.length ccs_raw);
    Seq.lemma_eq_elim left_stream right_stream;
    Seq.lemma_eq_elim left_stream (B.append application_raw application_tail);
    Seq.lemma_eq_elim right_stream (B.append ccs_raw ccs_tail);
    assert (Seq.equal
      (B.append application_raw application_tail)
      (B.append ccs_raw ccs_tail));
    PWS.lemma_append_heads_equal_same_len
      application_raw
      application_tail
      ccs_raw
      ccs_tail;
    assert (Seq.equal application_raw ccs_raw);
    lemma_application_data_raw_not_change_cipher_spec
      application_raw
      ccs_raw
  )

let lemma_equal_stream_after_client_hello_application_data_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (sent_ch:M.client_hello)
  (received_ch:M.client_hello)
  (sent_ch_raw:B.bytes)
  (application_raw:B.bytes)
  (received_ch_raw:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append sent_ch_raw application_raw) /\
        Seq.equal
          right_stream
          (B.append received_ch_raw (B.append ccs_raw ccs_tail)) /\
        WFL.supported_client_hello_wire_profile sent_ch /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello sent_ch))
          sent_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello received_ch))
          received_ch_raw /\
        CS.raw_records_exactly application_raw T.Application_data 1 /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)
=
  lemma_parse_record_wire_of_sent_supported_client_hello sent_ch sent_ch_raw;
  lemma_parse_record_wire_of_received_client_hello received_ch received_ch_raw;
  eliminate exists sent_fragment.
    W.parse_record_wire sent_ch_raw ==
      Some (T.Handshake, sent_fragment, B.length sent_ch_raw)
  returns False
  with _.
  (
    eliminate exists received_fragment.
      W.parse_record_wire received_ch_raw ==
        Some (T.Handshake, received_fragment, B.length received_ch_raw)
    returns False
    with _.
    (
      PWS.lemma_equal_stream_record_head_lengths
        left_stream
        right_stream
        sent_ch_raw
        application_raw
        received_ch_raw
        (B.append ccs_raw ccs_tail)
        T.Handshake
        sent_fragment
        T.Handshake
        received_fragment;
      assert (B.length sent_ch_raw == B.length received_ch_raw);
      Seq.lemma_eq_elim left_stream right_stream;
      Seq.lemma_eq_elim left_stream (B.append sent_ch_raw application_raw);
      Seq.lemma_eq_elim
        right_stream
        (B.append received_ch_raw (B.append ccs_raw ccs_tail));
      assert (Seq.equal
        (B.append sent_ch_raw application_raw)
        (B.append received_ch_raw (B.append ccs_raw ccs_tail)));
      PWS.lemma_append_tails_equal_same_len
        sent_ch_raw
        application_raw
        received_ch_raw
        (B.append ccs_raw ccs_tail);
      assert (Seq.equal application_raw (B.append ccs_raw ccs_tail));
      Seq.append_empty_r application_raw;
      assert (Seq.equal application_raw (B.append application_raw B.empty));
      lemma_equal_stream_head_application_data_not_change_cipher_spec
        application_raw
        application_raw
        application_raw
        B.empty
        ccs_raw
        ccs_tail
    )
  )

let lemma_equal_stream_head_received_server_hello_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (sh:M.server_hello)
  (server_hello_raw:B.bytes)
  (server_tail:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append server_hello_raw server_tail) /\
        Seq.equal right_stream (B.append ccs_raw ccs_tail) /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          server_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)
=
  lemma_parse_record_wire_of_received_server_hello sh server_hello_raw;
  lemma_cleartext_change_cipher_spec_parse_record ccs_raw;
  eliminate exists (server_fragment:B.bytes).
    W.parse_record_wire server_hello_raw ==
      Some (T.Handshake, server_fragment, B.length server_hello_raw)
  returns False
  with _.
  (
    PWS.lemma_equal_stream_record_head_lengths
      left_stream
      right_stream
      server_hello_raw
      server_tail
      ccs_raw
      ccs_tail
      T.Handshake
      server_fragment
      T.Change_cipher_spec
      (B.singleton 1uy);
    assert (B.length server_hello_raw == B.length ccs_raw);
    Seq.lemma_eq_elim left_stream right_stream;
    Seq.lemma_eq_elim left_stream (B.append server_hello_raw server_tail);
    Seq.lemma_eq_elim right_stream (B.append ccs_raw ccs_tail);
    assert (Seq.equal
      (B.append server_hello_raw server_tail)
      (B.append ccs_raw ccs_tail));
    PWS.lemma_append_heads_equal_same_len
      server_hello_raw
      server_tail
      ccs_raw
      ccs_tail;
    assert (Seq.equal server_hello_raw ccs_raw);
    lemma_received_server_hello_raw_not_change_cipher_spec
      sh
      server_hello_raw
      ccs_raw
  )

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

let lemma_event_raw_delta_legal_change_cipher_spec
  (model:CS.connection_model)
  (dir:CL.direction)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = dir;
            CL.message_value = M.TlsChangeCipherSpec;
          }))
          delta_sent
          delta_received)
      (ensures
        (dir == CL.Sent ==>
          CS.cleartext_tls_message_raw
            M.TlsChangeCipherSpec
            delta_sent /\
          Seq.equal delta_received B.empty) /\
        (dir == CL.Received ==>
          Seq.equal delta_sent B.empty /\
          CS.cleartext_tls_message_raw
            M.TlsChangeCipherSpec
            delta_received))
=
  match dir with
  | CL.Sent -> ()
  | CL.Received -> ()

let lemma_conn_events_raw_replay_received_change_cipher_spec_head
  (model:CS.connection_model)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsChangeCipherSpec;
          }) :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw received_tail.
          Seq.equal raw_received (B.append ccs_raw received_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model
    ev
    rest
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
  returns
    exists ccs_raw received_tail.
      Seq.equal raw_received (B.append ccs_raw received_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    lemma_event_raw_delta_legal_change_cipher_spec
      model
      CL.Received
      delta_sent
      delta_received;
    assert (CS.cleartext_tls_message_raw
      M.TlsChangeCipherSpec
      delta_received);
    assert (exists ccs_raw received_tail.
      Seq.equal raw_received (B.append ccs_raw received_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
  )

let lemma_conn_events_raw_replay_sent_change_cipher_spec_head
  (model:CS.connection_model)
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
            CL.message_value = M.TlsChangeCipherSpec;
          }) :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model
    ev
    rest
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
  returns
    exists ccs_raw sent_tail.
      Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    lemma_event_raw_delta_legal_change_cipher_spec
      model
      CL.Sent
      delta_sent
      delta_received;
    assert (CS.cleartext_tls_message_raw
      M.TlsChangeCipherSpec
      delta_sent);
    assert (exists ccs_raw sent_tail.
      Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
  )

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

let lemma_client_prefix_sent_client_hello_supported
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
        WFL.supported_client_config_wire_profile model0.CS.model_config /\
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
      (ensures WFL.supported_client_hello_wire_profile client_ch)
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
  returns WFL.supported_client_hello_wire_profile client_ch
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
    returns WFL.supported_client_hello_wire_profile client_ch
    with _.
    (
      assert (CS.legal_event model0 ev0);
      assert (CS.legal_event model1 ev1);
      assert (CS.legal_local_event model0 (CS.LocalStartHandshake client_start));
      assert (CS.legal_tls_message
        model1
        CL.Sent
        (M.TlsHandshake (M.ClientHello client_ch)));
      assert_norm (CS.step_model model0 ev0 ==
        CS.step_local_event model0 (CS.LocalStartHandshake client_start));
      assert_norm (CS.step_local_event model0 (CS.LocalStartHandshake client_start) ==
        Some (CS.with_handshake_stage
          model0
          { model0.CS.model_handshake with
              CS.hs_start = Some client_start
          }
          CS.HsStarted));
      assert (model1 ==
        CS.with_handshake_stage
          model0
          { model0.CS.model_handshake with
              CS.hs_start = Some client_start
          }
          CS.HsStarted);
      assert (model1.CS.model_config == model0.CS.model_config);
      assert (model1.CS.model_handshake.CS.hs_start == Some client_start);
      assert (CS.start_matches_config model0.CS.model_config client_start);
      assert (CS.client_hello_matches_start client_start client_ch);
      assert (Seq.equal
        client_start.CS.start_server_name
        model0.CS.model_config.CS.config_server_name);
      Seq.lemma_eq_elim
        client_start.CS.start_server_name
        model0.CS.model_config.CS.config_server_name;
      assert (client_ch.M.cipher_suites ==
        model0.CS.model_config.CS.config_cipher_suites);
      assert (client_ch.M.signature_schemes ==
        model0.CS.model_config.CS.config_signature_schemes);
      assert (client_ch.M.server_name ==
        Some model0.CS.model_config.CS.config_server_name);
      assert (B.length client_ch.M.body == 0);
      assert (WFL.supported_client_hello_wire_profile client_ch)
    )
  )

let lemma_server_start_then_received_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (rest:list CS.conn_event)
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
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw received_tail.
          Seq.equal raw_received (B.append ccs_raw received_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: rest)
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
    CS.legal_event model0 ev0 /\
    CS.step_model model0 ev0 == Some model1 /\
    CS.event_raw_delta_legal model0 ev0 delta0_sent delta0_received /\
    Seq.equal raw_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal raw_received (B.append delta0_received tail0_received) /\
    CS.conn_events_raw_replay model1 (ev1 :: rest) tail0_sent tail0_received final_model
  returns
    exists ccs_raw received_tail.
      Seq.equal raw_received (B.append ccs_raw received_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      rest
      tail0_sent
      tail0_received
      final_model;
    eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
      CS.legal_event model1 ev1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_raw_replay model2 rest tail1_sent tail1_received final_model
    returns
      exists ccs_raw received_tail.
        Seq.equal raw_received (B.append ccs_raw received_tail) /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      lemma_event_raw_delta_legal_local
        model0
        CS.LocalStartServer
        delta0_sent
        delta0_received;
      lemma_event_raw_delta_legal_change_cipher_spec
        model1
        CL.Received
        delta1_sent
        delta1_received;
      assert (Seq.equal delta0_sent B.empty);
      assert (Seq.equal delta0_received B.empty);
      assert (Seq.equal delta1_sent B.empty);
      assert (CS.cleartext_tls_message_raw
        M.TlsChangeCipherSpec
        delta1_received);
      Seq.lemma_eq_elim delta0_received B.empty;
      CL.lemma_append_empty_left tail0_received;
      assert (Seq.equal raw_received tail0_received);
      Seq.lemma_eq_elim raw_received tail0_received;
      assert (exists ccs_raw received_tail.
        Seq.equal raw_received (B.append ccs_raw received_tail) /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
    )
  )

let lemma_server_start_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: rest)
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
    CS.legal_event model0 ev0 /\
    CS.step_model model0 ev0 == Some model1 /\
    CS.event_raw_delta_legal model0 ev0 delta0_sent delta0_received /\
    Seq.equal raw_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal raw_received (B.append delta0_received tail0_received) /\
    CS.conn_events_raw_replay model1 (ev1 :: rest) tail0_sent tail0_received final_model
  returns
    exists ccs_raw sent_tail.
      Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      rest
      tail0_sent
      tail0_received
      final_model;
    eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
      CS.legal_event model1 ev1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_raw_replay model2 rest tail1_sent tail1_received final_model
    returns
      exists ccs_raw sent_tail.
        Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      lemma_event_raw_delta_legal_local
        model0
        CS.LocalStartServer
        delta0_sent
        delta0_received;
      lemma_event_raw_delta_legal_change_cipher_spec
        model1
        CL.Sent
        delta1_sent
        delta1_received;
      assert (Seq.equal delta0_sent B.empty);
      assert (Seq.equal delta0_received B.empty);
      assert (CS.cleartext_tls_message_raw
        M.TlsChangeCipherSpec
        delta1_sent);
      assert (Seq.equal delta1_received B.empty);
      Seq.lemma_eq_elim delta0_sent B.empty;
      CL.lemma_append_empty_left tail0_sent;
      assert (Seq.equal raw_sent tail0_sent);
      Seq.lemma_eq_elim raw_sent tail0_sent;
      assert (exists ccs_raw sent_tail.
        Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
    )
  )

let lemma_server_start_client_hello_then_received_change_cipher_spec_raw_slices
  (model0:CS.connection_model)
  (server_ch:M.client_hello)
  (rest:list CS.conn_event)
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
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
  }) in
  let ev2 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: rest)
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
    CS.legal_event model0 ev0 /\
    CS.step_model model0 ev0 == Some model1 /\
    CS.event_raw_delta_legal model0 ev0 delta0_sent delta0_received /\
    Seq.equal raw_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal raw_received (B.append delta0_received tail0_received) /\
    CS.conn_events_raw_replay model1 (ev1 :: ev2 :: rest) tail0_sent tail0_received final_model
  returns
    exists server_ch_raw ccs_raw received_tail.
      Seq.equal
        raw_received
        (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello server_ch))
        server_ch_raw /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: rest)
      tail0_sent
      tail0_received
      final_model;
    eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
      CS.legal_event model1 ev1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_raw_replay model2 (ev2 :: rest) tail1_sent tail1_received final_model
    returns
      exists server_ch_raw ccs_raw received_tail.
        Seq.equal
          raw_received
          (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        rest
        tail1_sent
        tail1_received
        final_model;
      eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
        CS.legal_event model2 ev2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_raw_replay model3 rest tail2_sent tail2_received final_model
      returns
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
      with _.
      (
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
        lemma_event_raw_delta_legal_change_cipher_spec
          model2
          CL.Received
          delta2_sent
          delta2_received;
        assert (Seq.equal delta0_received B.empty);
        assert (CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          delta1_received);
        assert (CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          delta2_received);
        Seq.lemma_eq_elim delta0_received B.empty;
        CL.lemma_append_empty_left tail0_received;
        assert (Seq.equal raw_received tail0_received);
        Seq.lemma_eq_elim raw_received tail0_received;
        Seq.lemma_eq_elim tail0_received (B.append delta1_received tail1_received);
        Seq.lemma_eq_elim tail1_received (B.append delta2_received tail2_received);
        Seq.append_assoc delta1_received delta2_received tail2_received;
        assert (Seq.equal
          raw_received
          (B.append delta1_received (B.append delta2_received tail2_received)));
        assert (exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
      )
    )
  )

let lemma_server_start_client_hello_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (server_ch:M.client_hello)
  (rest:list CS.conn_event)
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
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
  }) in
  let ev2 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: rest)
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
    CS.legal_event model0 ev0 /\
    CS.step_model model0 ev0 == Some model1 /\
    CS.event_raw_delta_legal model0 ev0 delta0_sent delta0_received /\
    Seq.equal raw_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal raw_received (B.append delta0_received tail0_received) /\
    CS.conn_events_raw_replay model1 (ev1 :: ev2 :: rest) tail0_sent tail0_received final_model
  returns
    exists ccs_raw sent_tail.
      Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: rest)
      tail0_sent
      tail0_received
      final_model;
    eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
      CS.legal_event model1 ev1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_raw_replay model2 (ev2 :: rest) tail1_sent tail1_received final_model
    returns
      exists ccs_raw sent_tail.
        Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        rest
        tail1_sent
        tail1_received
        final_model;
      eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
        CS.legal_event model2 ev2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_raw_replay model3 rest tail2_sent tail2_received final_model
      returns
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
      with _.
      (
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
        lemma_event_raw_delta_legal_change_cipher_spec
          model2
          CL.Sent
          delta2_sent
          delta2_received;
        assert (Seq.equal delta0_sent B.empty);
        assert (Seq.equal delta1_sent B.empty);
        assert (CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          delta2_sent);
        Seq.lemma_eq_elim delta0_sent B.empty;
        CL.lemma_append_empty_left tail0_sent;
        assert (Seq.equal raw_sent tail0_sent);
        Seq.lemma_eq_elim raw_sent tail0_sent;
        Seq.lemma_eq_elim tail0_sent (B.append delta1_sent tail1_sent);
        Seq.lemma_eq_elim delta1_sent B.empty;
        CL.lemma_append_empty_left tail1_sent;
        assert (Seq.equal raw_sent tail1_sent);
        Seq.lemma_eq_elim tail1_sent (B.append delta2_sent tail2_sent);
        assert (exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
      )
    )
  )

let lemma_server_start_client_hello_select_then_received_change_cipher_spec_raw_slices
  (model0:CS.connection_model)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (rest:list CS.conn_event)
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
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
  }) in
  let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let ev3 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: ev3 :: rest)
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
      (ev1 :: ev2 :: ev3 :: rest)
      tail0_sent
      tail0_received
      final_model
  returns
    exists server_ch_raw ccs_raw received_tail.
      Seq.equal
        raw_received
        (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello server_ch))
        server_ch_raw /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: ev3 :: rest)
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
        (ev2 :: ev3 :: rest)
        tail1_sent
        tail1_received
        final_model
    returns
      exists server_ch_raw ccs_raw received_tail.
        Seq.equal
          raw_received
          (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        (ev3 :: rest)
        tail1_sent
        tail1_received
        final_model;
      eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
        CS.legal_event model2 ev2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_raw_replay model3 (ev3 :: rest) tail2_sent tail2_received final_model
      returns
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
      with _.
      (
        PWR.lemma_conn_events_raw_replay_head
          model3
          ev3
          rest
          tail2_sent
          tail2_received
          final_model;
        eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
          CS.legal_event model3 ev3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.event_raw_delta_legal model3 ev3 delta3_sent delta3_received /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_raw_replay model4 rest tail3_sent tail3_received final_model
        returns
          exists server_ch_raw ccs_raw received_tail.
            Seq.equal
              raw_received
              (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
            CS.received_cleartext_tls_message_raw
              (M.TlsHandshake (M.ClientHello server_ch))
              server_ch_raw /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
        with _.
        (
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
          lemma_event_raw_delta_legal_change_cipher_spec
            model3
            CL.Received
            delta3_sent
            delta3_received;
          assert (Seq.equal delta0_received B.empty);
          assert (CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            delta1_received);
          assert (Seq.equal delta2_received B.empty);
          assert (CS.cleartext_tls_message_raw
            M.TlsChangeCipherSpec
            delta3_received);
          Seq.lemma_eq_elim delta0_received B.empty;
          CL.lemma_append_empty_left tail0_received;
          assert (Seq.equal raw_received tail0_received);
          Seq.lemma_eq_elim raw_received tail0_received;
          Seq.lemma_eq_elim tail0_received (B.append delta1_received tail1_received);
          Seq.lemma_eq_elim tail1_received (B.append delta2_received tail2_received);
          Seq.lemma_eq_elim delta2_received B.empty;
          CL.lemma_append_empty_left tail2_received;
          assert (Seq.equal tail1_received tail2_received);
          Seq.lemma_eq_elim tail1_received tail2_received;
          Seq.lemma_eq_elim tail2_received (B.append delta3_received tail3_received);
          Seq.append_assoc delta1_received delta3_received tail3_received;
          assert (Seq.equal
            raw_received
            (B.append delta1_received (B.append delta3_received tail3_received)));
          assert (exists server_ch_raw ccs_raw received_tail.
            Seq.equal
              raw_received
              (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
            CS.received_cleartext_tls_message_raw
              (M.TlsHandshake (M.ClientHello server_ch))
              server_ch_raw /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
        )
      )
    )
  )

let lemma_server_start_client_hello_select_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (rest:list CS.conn_event)
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
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
  }) in
  let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let ev3 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: ev3 :: rest)
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
      (ev1 :: ev2 :: ev3 :: rest)
      tail0_sent
      tail0_received
      final_model
  returns
    exists ccs_raw sent_tail.
      Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: ev3 :: rest)
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
        (ev2 :: ev3 :: rest)
        tail1_sent
        tail1_received
        final_model
    returns
      exists ccs_raw sent_tail.
        Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        (ev3 :: rest)
        tail1_sent
        tail1_received
        final_model;
      eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
        CS.legal_event model2 ev2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_raw_replay model3 (ev3 :: rest) tail2_sent tail2_received final_model
      returns
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
      with _.
      (
        PWR.lemma_conn_events_raw_replay_head
          model3
          ev3
          rest
          tail2_sent
          tail2_received
          final_model;
        eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
          CS.legal_event model3 ev3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.event_raw_delta_legal model3 ev3 delta3_sent delta3_received /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_raw_replay model4 rest tail3_sent tail3_received final_model
        returns
          exists ccs_raw sent_tail.
            Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
        with _.
        (
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
          lemma_event_raw_delta_legal_change_cipher_spec
            model3
            CL.Sent
            delta3_sent
            delta3_received;
          assert (Seq.equal delta0_sent B.empty);
          assert (Seq.equal delta1_sent B.empty);
          assert (Seq.equal delta2_sent B.empty);
          assert (CS.cleartext_tls_message_raw
            M.TlsChangeCipherSpec
            delta3_sent);
          Seq.lemma_eq_elim delta0_sent B.empty;
          CL.lemma_append_empty_left tail0_sent;
          assert (Seq.equal raw_sent tail0_sent);
          Seq.lemma_eq_elim raw_sent tail0_sent;
          Seq.lemma_eq_elim tail0_sent (B.append delta1_sent tail1_sent);
          Seq.lemma_eq_elim delta1_sent B.empty;
          CL.lemma_append_empty_left tail1_sent;
          assert (Seq.equal raw_sent tail1_sent);
          Seq.lemma_eq_elim tail1_sent (B.append delta2_sent tail2_sent);
          Seq.lemma_eq_elim delta2_sent B.empty;
          CL.lemma_append_empty_left tail2_sent;
          assert (Seq.equal raw_sent tail2_sent);
          Seq.lemma_eq_elim tail2_sent (B.append delta3_sent tail3_sent);
          assert (exists ccs_raw sent_tail.
            Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
        )
      )
    )
  )

let lemma_server_start_client_hello_select_shared_then_received_change_cipher_spec_raw_slices
  (model0:CS.connection_model)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (rest:list CS.conn_event)
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
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
  }) in
  let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let ev4 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: ev3 :: ev4 :: rest)
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
      (ev1 :: ev2 :: ev3 :: ev4 :: rest)
      tail0_sent
      tail0_received
      final_model
  returns
    exists server_ch_raw ccs_raw received_tail.
      Seq.equal
        raw_received
        (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello server_ch))
        server_ch_raw /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: ev3 :: ev4 :: rest)
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
        (ev2 :: ev3 :: ev4 :: rest)
        tail1_sent
        tail1_received
        final_model
    returns
      exists server_ch_raw ccs_raw received_tail.
        Seq.equal
          raw_received
          (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        (ev3 :: ev4 :: rest)
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
          (ev3 :: ev4 :: rest)
          tail2_sent
          tail2_received
          final_model
      returns
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
      with _.
      (
        PWR.lemma_conn_events_raw_replay_head
          model3
          ev3
          (ev4 :: rest)
          tail2_sent
          tail2_received
          final_model;
        eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
          CS.legal_event model3 ev3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.event_raw_delta_legal model3 ev3 delta3_sent delta3_received /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_raw_replay model4 (ev4 :: rest) tail3_sent tail3_received final_model
        returns
          exists server_ch_raw ccs_raw received_tail.
            Seq.equal
              raw_received
              (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
            CS.received_cleartext_tls_message_raw
              (M.TlsHandshake (M.ClientHello server_ch))
              server_ch_raw /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
        with _.
        (
          lemma_conn_events_raw_replay_received_change_cipher_spec_head
            model4
            rest
            tail3_sent
            tail3_received
            final_model;
          eliminate exists ccs_raw tail4_received.
            Seq.equal tail3_received (B.append ccs_raw tail4_received) /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
          returns
            exists server_ch_raw ccs_raw received_tail.
              Seq.equal
                raw_received
                (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
              CS.received_cleartext_tls_message_raw
                (M.TlsHandshake (M.ClientHello server_ch))
                server_ch_raw /\
              CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
          with _.
          (
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
            assert (Seq.equal delta0_received B.empty);
            assert (CS.received_cleartext_tls_message_raw
              (M.TlsHandshake (M.ClientHello server_ch))
              delta1_received);
            assert (Seq.equal delta2_received B.empty);
            assert (Seq.equal delta3_received B.empty);
            Seq.lemma_eq_elim delta0_received B.empty;
            CL.lemma_append_empty_left tail0_received;
            assert (Seq.equal raw_received tail0_received);
            Seq.lemma_eq_elim raw_received tail0_received;
            Seq.lemma_eq_elim tail0_received (B.append delta1_received tail1_received);
            Seq.lemma_eq_elim tail1_received (B.append delta2_received tail2_received);
            Seq.lemma_eq_elim delta2_received B.empty;
            CL.lemma_append_empty_left tail2_received;
            assert (Seq.equal tail1_received tail2_received);
            Seq.lemma_eq_elim tail1_received tail2_received;
            Seq.lemma_eq_elim tail2_received (B.append delta3_received tail3_received);
            Seq.lemma_eq_elim delta3_received B.empty;
            CL.lemma_append_empty_left tail3_received;
            assert (Seq.equal tail2_received tail3_received);
            Seq.lemma_eq_elim tail2_received tail3_received;
            Seq.lemma_eq_elim tail3_received (B.append ccs_raw tail4_received);
            Seq.append_assoc delta1_received ccs_raw tail4_received;
            assert (Seq.equal
              raw_received
              (B.append delta1_received (B.append ccs_raw tail4_received)));
            assert (exists server_ch_raw ccs_raw0 received_tail.
              Seq.equal
                raw_received
                (B.append server_ch_raw (B.append ccs_raw0 received_tail)) /\
              CS.received_cleartext_tls_message_raw
                (M.TlsHandshake (M.ClientHello server_ch))
                server_ch_raw /\
              CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw0)
          )
        )
      )
    )
  )

let lemma_server_start_client_hello_select_shared_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (rest:list CS.conn_event)
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
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)
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
    CL.message_value = M.TlsChangeCipherSpec;
  }) in
  PWR.lemma_conn_events_raw_replay_head
    model0
    ev0
    (ev1 :: ev2 :: ev3 :: ev4 :: rest)
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
      (ev1 :: ev2 :: ev3 :: ev4 :: rest)
      tail0_sent
      tail0_received
      final_model
  returns
    exists ccs_raw sent_tail.
      Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
  with _.
  (
    PWR.lemma_conn_events_raw_replay_head
      model1
      ev1
      (ev2 :: ev3 :: ev4 :: rest)
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
        (ev2 :: ev3 :: ev4 :: rest)
        tail1_sent
        tail1_received
        final_model
    returns
      exists ccs_raw sent_tail.
        Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
        CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model2
        ev2
        (ev3 :: ev4 :: rest)
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
          (ev3 :: ev4 :: rest)
          tail2_sent
          tail2_received
          final_model
      returns
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
      with _.
      (
        PWR.lemma_conn_events_raw_replay_head
          model3
          ev3
          (ev4 :: rest)
          tail2_sent
          tail2_received
          final_model;
        eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
          CS.legal_event model3 ev3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.event_raw_delta_legal model3 ev3 delta3_sent delta3_received /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_raw_replay model4 (ev4 :: rest) tail3_sent tail3_received final_model
        returns
          exists ccs_raw sent_tail.
            Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
        with _.
        (
          lemma_conn_events_raw_replay_sent_change_cipher_spec_head
            model4
            rest
            tail3_sent
            tail3_received
            final_model;
          eliminate exists ccs_raw tail4_sent.
            Seq.equal tail3_sent (B.append ccs_raw tail4_sent) /\
            CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
          returns
            exists ccs_raw sent_tail.
              Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
              CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
          with _.
          (
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
            assert (Seq.equal delta1_sent B.empty);
            assert (Seq.equal delta2_sent B.empty);
            assert (Seq.equal delta3_sent B.empty);
            Seq.lemma_eq_elim delta0_sent B.empty;
            CL.lemma_append_empty_left tail0_sent;
            assert (Seq.equal raw_sent tail0_sent);
            Seq.lemma_eq_elim raw_sent tail0_sent;
            Seq.lemma_eq_elim tail0_sent (B.append delta1_sent tail1_sent);
            Seq.lemma_eq_elim delta1_sent B.empty;
            CL.lemma_append_empty_left tail1_sent;
            assert (Seq.equal raw_sent tail1_sent);
            Seq.lemma_eq_elim tail1_sent (B.append delta2_sent tail2_sent);
            Seq.lemma_eq_elim delta2_sent B.empty;
            CL.lemma_append_empty_left tail2_sent;
            assert (Seq.equal raw_sent tail2_sent);
            Seq.lemma_eq_elim tail2_sent (B.append delta3_sent tail3_sent);
            Seq.lemma_eq_elim delta3_sent B.empty;
            CL.lemma_append_empty_left tail3_sent;
            assert (Seq.equal raw_sent tail3_sent);
            Seq.lemma_eq_elim tail3_sent (B.append ccs_raw tail4_sent);
            assert (exists ccs_raw0 sent_tail.
              Seq.equal raw_sent (B.append ccs_raw0 sent_tail) /\
              CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw0)
          )
        )
      )
    )
  )

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

let lemma_sent_server_hello_head_step_model_from_raw_replay
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
        exists model1 tail_sent tail_received.
          CS.step_model
            model
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
            })) == Some model1 /\
          CS.conn_events_raw_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)
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
    exists model1 tail_sent tail_received.
      CS.step_model model ev == Some model1 /\
      CS.conn_events_raw_replay
        model1
        rest
        tail_sent
        tail_received
        final_model
  with _.
  (
    assert (exists model1 tail_sent tail_received.
      CS.step_model model ev == Some model1 /\
      CS.conn_events_raw_replay
        model1
        rest
        tail_sent
        tail_received
        final_model)
  )

let lemma_client_cleartext_prefix_step_models_from_raw_replay
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
        exists model1 model2 model3 model4 tail_sent tail_received.
          CS.step_model
            model0
            (CS.ConnLocalEvent (CS.LocalStartHandshake client_start)) ==
            Some model1 /\
          CS.step_model
            model1
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
            })) == Some model2 /\
          CS.step_model
            model2
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
            })) == Some model3 /\
          CS.step_model
            model3
            (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
            Some model4 /\
          CS.conn_events_raw_replay
            model4
            client_rest
            tail_sent
            tail_received
            final_model)
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
    exists model1 model2 model3 model4 tail_sent tail_received.
      CS.step_model model0 ev0 == Some model1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.step_model model2 ev2 == Some model3 /\
      CS.step_model model3 ev3 == Some model4 /\
      CS.conn_events_raw_replay
        model4
        client_rest
        tail_sent
        tail_received
        final_model
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
      exists model1 model2 model3 model4 tail_sent tail_received.
        CS.step_model model0 ev0 == Some model1 /\
        CS.step_model model1 ev1 == Some model2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.step_model model3 ev3 == Some model4 /\
        CS.conn_events_raw_replay
          model4
          client_rest
          tail_sent
          tail_received
          final_model
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
        exists model1 model2 model3 model4 tail_sent tail_received.
          CS.step_model model0 ev0 == Some model1 /\
          CS.step_model model1 ev1 == Some model2 /\
          CS.step_model model2 ev2 == Some model3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.conn_events_raw_replay
            model4
            client_rest
            tail_sent
            tail_received
            final_model
      with _.
      (
        PWR.lemma_conn_events_raw_replay_head
          model3
          ev3
          client_rest
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
            client_rest
            tail3_sent
            tail3_received
            final_model
        returns
          exists model1 model2 model3 model4 tail_sent tail_received.
            CS.step_model model0 ev0 == Some model1 /\
            CS.step_model model1 ev1 == Some model2 /\
            CS.step_model model2 ev2 == Some model3 /\
            CS.step_model model3 ev3 == Some model4 /\
            CS.conn_events_raw_replay
              model4
              client_rest
              tail_sent
              tail_received
              final_model
        with _.
        (
          assert (exists model1 model2 model3 model4 tail_sent tail_received.
            CS.step_model model0 ev0 == Some model1 /\
            CS.step_model model1 ev1 == Some model2 /\
            CS.step_model model2 ev2 == Some model3 /\
            CS.step_model model3 ev3 == Some model4 /\
            CS.conn_events_raw_replay
              model4
              client_rest
              tail_sent
              tail_received
              final_model)
        )
      )
    )
  )

#push-options "--split_queries always --z3rlimit 20"

let hello_slots_frozen_control (control:CS.connection_control_state) : Tot prop =
  match control with
  | CS.ControlHandshaking CS.HsServerHelloReceived -> True
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived -> True
  | CS.ControlHandshaking CS.HsCertificateReceived -> True
  | CS.ControlHandshaking CS.HsCertificateValidated -> True
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived -> True
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified -> True
  | CS.ControlHandshaking CS.HsServerFinishedReceived -> True
  | CS.ControlHandshaking CS.HsServerFinishedVerified -> True
  | CS.ControlHandshaking CS.HsServerHelloSent -> True
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> True
  | CS.ControlHandshaking CS.HsServerFinishedSent -> True
  | CS.ControlHandshaking CS.HsClientFinishedReceived -> True
  | CS.ControlApplicationData -> True
  | CS.ControlClosing -> True
  | CS.ControlClosed -> True
  | CS.ControlFailed _ -> True
  | _ -> False

let lemma_step_model_preserves_frozen_hello_slots
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model1:CS.connection_model)
  (ch:M.client_hello)
  (sh:M.server_hello)
  : Lemma
      (requires
        hello_slots_frozen_control model.CS.model_control /\
        model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        CS.step_model model ev == Some model1)
      (ensures
        hello_slots_frozen_control model1.CS.model_control /\
        model1.CS.model_handshake.CS.hs_client_hello == Some ch /\
        model1.CS.model_handshake.CS.hs_server_hello == Some sh)
=
  match ev with
  | CS.ConnLocalEvent local ->
    (match local, model.CS.model_control with
     | CS.LocalStartHandshake _, CS.ControlNew -> assert False
     | CS.LocalStartServer, CS.ControlNew -> assert False
     | CS.LocalSelectServerParameters _, CS.ControlHandshaking CS.HsClientHelloReceived ->
       assert False
     | CS.LocalDeriveSharedSecret _, CS.ControlHandshaking CS.HsClientHelloReceived ->
       assert False
     | _, _ -> ())
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_value, msg.CL.message_direction, model.CS.model_control with
     | M.TlsHandshake (M.ClientHello _), CL.Sent, CS.ControlHandshaking CS.HsStarted ->
       assert False
     | M.TlsHandshake (M.ClientHello _), CL.Received, CS.ControlHandshaking CS.HsAwaitingClientHello ->
       assert False
     | M.TlsHandshake (M.ServerHello _), CL.Received, CS.ControlHandshaking CS.HsClientHelloSent ->
       assert False
     | M.TlsHandshake (M.ServerHello _), CL.Sent, CS.ControlHandshaking CS.HsClientHelloReceived ->
       assert False
     | _, _, _ -> ())

let rec lemma_conn_events_raw_replay_preserves_frozen_hello_slots
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  (ch:M.client_hello)
  (sh:M.server_hello)
  : Lemma
      (requires
        hello_slots_frozen_control model.CS.model_control /\
        model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        CS.conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures
        final_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        final_model.CS.model_handshake.CS.hs_server_hello == Some sh)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
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
      final_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
      final_model.CS.model_handshake.CS.hs_server_hello == Some sh
    with _.
    (
      lemma_step_model_preserves_frozen_hello_slots model ev model1 ch sh;
      lemma_conn_events_raw_replay_preserves_frozen_hello_slots
        model1
        rest
        tail_sent
        tail_received
        final_model
        ch
        sh
    )

let lemma_client_cleartext_prefix_final_hello_slots_from_raw_replay
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
        final_model.CS.model_handshake.CS.hs_client_hello ==
          Some client_ch /\
        final_model.CS.model_handshake.CS.hs_server_hello ==
          Some client_sh)
=
  lemma_client_cleartext_prefix_step_models_from_raw_replay
    model0
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 model2 model3 model4 tail_sent tail_received.
    CS.step_model
      model0
      (CS.ConnLocalEvent (CS.LocalStartHandshake client_start)) ==
      Some model1 /\
    CS.step_model
      model1
      (CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
      })) == Some model2 /\
    CS.step_model
      model2
      (CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
      })) == Some model3 /\
    CS.step_model
      model3
      (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
      Some model4 /\
    CS.conn_events_raw_replay
      model4
      client_rest
      tail_sent
      tail_received
      final_model
  returns
    final_model.CS.model_handshake.CS.hs_client_hello ==
      Some client_ch /\
    final_model.CS.model_handshake.CS.hs_server_hello ==
      Some client_sh
  with _.
  (
    assert (hello_slots_frozen_control model4.CS.model_control);
    assert (model4.CS.model_handshake.CS.hs_client_hello == Some client_ch);
    assert (model4.CS.model_handshake.CS.hs_server_hello == Some client_sh);
    lemma_conn_events_raw_replay_preserves_frozen_hello_slots
      model4
      client_rest
      tail_sent
      tail_received
      final_model
      client_ch
      client_sh
  )

#pop-options

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

let lemma_server_cleartext_prefix_step_models_from_raw_replay
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
        exists model1 model2 model3 model4 model5 tail_sent tail_received.
          CS.step_model
            model0
            (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
          CS.step_model
            model1
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
            })) == Some model2 /\
          CS.step_model
            model2
            (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
            Some model3 /\
          CS.step_model
            model3
            (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
            Some model4 /\
          CS.step_model
            model4
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
            })) == Some model5 /\
          CS.conn_events_raw_replay
            model5
            server_rest
            tail_sent
            tail_received
            final_model)
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
    exists model1 model2 model3 model4 model5 tail_sent tail_received.
      CS.step_model model0 ev0 == Some model1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.step_model model2 ev2 == Some model3 /\
      CS.step_model model3 ev3 == Some model4 /\
      CS.step_model model4 ev4 == Some model5 /\
      CS.conn_events_raw_replay
        model5
        server_rest
        tail_sent
        tail_received
        final_model
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
      exists model1 model2 model3 model4 model5 tail_sent tail_received.
        CS.step_model model0 ev0 == Some model1 /\
        CS.step_model model1 ev1 == Some model2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.step_model model3 ev3 == Some model4 /\
        CS.step_model model4 ev4 == Some model5 /\
        CS.conn_events_raw_replay
          model5
          server_rest
          tail_sent
          tail_received
          final_model
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
        exists model1 model2 model3 model4 model5 tail_sent tail_received.
          CS.step_model model0 ev0 == Some model1 /\
          CS.step_model model1 ev1 == Some model2 /\
          CS.step_model model2 ev2 == Some model3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.step_model model4 ev4 == Some model5 /\
          CS.conn_events_raw_replay
            model5
            server_rest
            tail_sent
            tail_received
            final_model
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
          exists model1 model2 model3 model4 model5 tail_sent tail_received.
            CS.step_model model0 ev0 == Some model1 /\
            CS.step_model model1 ev1 == Some model2 /\
            CS.step_model model2 ev2 == Some model3 /\
            CS.step_model model3 ev3 == Some model4 /\
            CS.step_model model4 ev4 == Some model5 /\
            CS.conn_events_raw_replay
              model5
              server_rest
              tail_sent
              tail_received
              final_model
        with _.
        (
          lemma_sent_server_hello_head_step_model_from_raw_replay
            model4
            server_sh
            server_rest
            tail3_sent
            tail3_received
            final_model;
          eliminate exists model5 tail4_sent tail4_received.
            CS.step_model model4 ev4 == Some model5 /\
            CS.conn_events_raw_replay
              model5
              server_rest
              tail4_sent
              tail4_received
              final_model
          returns
            exists model1 model2 model3 model4 model5 tail_sent tail_received.
              CS.step_model model0 ev0 == Some model1 /\
              CS.step_model model1 ev1 == Some model2 /\
              CS.step_model model2 ev2 == Some model3 /\
              CS.step_model model3 ev3 == Some model4 /\
              CS.step_model model4 ev4 == Some model5 /\
              CS.conn_events_raw_replay
                model5
                server_rest
                tail_sent
                tail_received
                final_model
          with _.
          (
            assert (exists model1 model2 model3 model4 model5 tail_sent tail_received.
              CS.step_model model0 ev0 == Some model1 /\
              CS.step_model model1 ev1 == Some model2 /\
              CS.step_model model2 ev2 == Some model3 /\
              CS.step_model model3 ev3 == Some model4 /\
              CS.step_model model4 ev4 == Some model5 /\
              CS.conn_events_raw_replay
                model5
                server_rest
                tail_sent
                tail_received
                final_model)
          )
        )
      )
    )
  )

#push-options "--split_queries always --z3rlimit 20"

let lemma_server_cleartext_prefix_final_hello_slots_from_raw_replay
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
        final_model.CS.model_handshake.CS.hs_client_hello ==
          Some server_ch /\
        final_model.CS.model_handshake.CS.hs_server_hello ==
          Some server_sh)
=
  lemma_server_cleartext_prefix_step_models_from_raw_replay
    model0
    server_ch
    selection
    server_shared
    server_sh
    server_rest
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 model2 model3 model4 model5 tail_sent tail_received.
    CS.step_model
      model0
      (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
    CS.step_model
      model1
      (CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      })) == Some model2 /\
    CS.step_model
      model2
      (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
      Some model3 /\
    CS.step_model
      model3
      (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
      Some model4 /\
    CS.step_model
      model4
      (CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
      })) == Some model5 /\
    CS.conn_events_raw_replay
      model5
      server_rest
      tail_sent
      tail_received
      final_model
  returns
    final_model.CS.model_handshake.CS.hs_client_hello ==
      Some server_ch /\
    final_model.CS.model_handshake.CS.hs_server_hello ==
      Some server_sh
  with _.
  (
    assert (hello_slots_frozen_control model5.CS.model_control);
    assert (model5.CS.model_handshake.CS.hs_client_hello == Some server_ch);
    assert (model5.CS.model_handshake.CS.hs_server_hello == Some server_sh);
    lemma_conn_events_raw_replay_preserves_frozen_hello_slots
      model5
      server_rest
      tail_sent
      tail_received
      final_model
      server_ch
      server_sh
  )

#pop-options

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
