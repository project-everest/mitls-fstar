module TLS13.Impl.ConnectionState.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.StateMachine
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Model = TLS13.Impl.ConnectionState.Model
module Queries = TLS13.Impl.ConnectionState.Queries
module Repr = TLS13.Impl.ConnectionState.Repr
module Tags = TLS13.Impl.ConnectionState.Tags
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ser = TLS13.Impl.Serializer
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model
open TLS13.Impl.ConnectionState.Queries
open TLS13.Impl.ConnectionState.Repr

let restored_read_sequence_model
  (model:CS.connection_model)
  (previous:R.direction_state)
  : CS.connection_model =
  { model with
      CS.model_record =
        { model.CS.model_record with
            CS.record_read = previous;
        };
  }

let pending_protected_bytes
  (fragment:B.bytes)
  (parsed:nat)
  : B.bytes =
  if parsed < B.length fragment then fragment else B.empty

let pending_protected_offset
  (fragment:B.bytes)
  (parsed:nat)
  : nat =
  if parsed < B.length fragment then parsed else 0

ghost fn reframe_server_key_share_private
  (slot:optional_fixed_bytes)
  (#old_hs:erased CS.handshake_state)
  (new_hs:erased CS.handshake_state)
  requires server_key_share_private_exactly slot (Ghost.reveal old_hs) **
           pure (
             (Ghost.reveal old_hs).CS.hs_server_selection ==
               (Ghost.reveal new_hs).CS.hs_server_selection)
  ensures server_key_share_private_exactly slot (Ghost.reveal new_hs)
{
  rewrite
    (server_key_share_private_exactly slot (Ghost.reveal old_hs))
    as
    (server_key_share_private_exactly slot (Ghost.reveal new_hs))
}

ghost fn reframe_client_hello_metadata
  (messages:handshake_message_storage)
  (#old_hs:erased CS.handshake_state)
  (new_hs:erased CS.handshake_state)
  requires client_hello_metadata_exactly
             messages.client_hello_has_server_name
             messages.client_hello_server_name_len
             messages.client_hello_cipher_suites_len
             messages.client_hello_signature_schemes_len
             (Ghost.reveal old_hs).CS.hs_client_hello **
           pure (
             (Ghost.reveal old_hs).CS.hs_client_hello ==
               (Ghost.reveal new_hs).CS.hs_client_hello)
  ensures client_hello_metadata_exactly
            messages.client_hello_has_server_name
            messages.client_hello_server_name_len
            messages.client_hello_cipher_suites_len
            messages.client_hello_signature_schemes_len
            (Ghost.reveal new_hs).CS.hs_client_hello
{
  rewrite
    (client_hello_metadata_exactly
      messages.client_hello_has_server_name
      messages.client_hello_server_name_len
      messages.client_hello_cipher_suites_len
      messages.client_hello_signature_schemes_len
      (Ghost.reveal old_hs).CS.hs_client_hello)
    as
    (client_hello_metadata_exactly
      messages.client_hello_has_server_name
      messages.client_hello_server_name_len
      messages.client_hello_cipher_suites_len
      messages.client_hello_signature_schemes_len
      (Ghost.reveal new_hs).CS.hs_client_hello)
}

ghost fn reframe_handshake_messages
  (messages:handshake_message_storage)
  (#old_hs:erased CS.handshake_state)
  (new_hs:erased CS.handshake_state)
  requires handshake_messages_exactly messages (Ghost.reveal old_hs) **
           pure (
             (Ghost.reveal old_hs).CS.hs_client_hello ==
               (Ghost.reveal new_hs).CS.hs_client_hello /\
             (Ghost.reveal old_hs).CS.hs_server_hello ==
               (Ghost.reveal new_hs).CS.hs_server_hello /\
             (Ghost.reveal old_hs).CS.hs_encrypted_extensions ==
               (Ghost.reveal new_hs).CS.hs_encrypted_extensions /\
             (Ghost.reveal old_hs).CS.hs_certificate ==
               (Ghost.reveal new_hs).CS.hs_certificate /\
             (Ghost.reveal old_hs).CS.hs_certificate_verify ==
               (Ghost.reveal new_hs).CS.hs_certificate_verify /\
             (Ghost.reveal old_hs).CS.hs_server_finished ==
               (Ghost.reveal new_hs).CS.hs_server_finished /\
             (Ghost.reveal old_hs).CS.hs_client_finished ==
               (Ghost.reveal new_hs).CS.hs_client_finished)
  ensures handshake_messages_exactly messages (Ghost.reveal new_hs)
{
  unfold (handshake_messages_exactly messages (Ghost.reveal old_hs));
  rewrite (client_hello_slot_exactly
    messages.client_hello_present
    messages.client_hello
    (Ghost.reveal old_hs).CS.hs_client_hello)
    as (client_hello_slot_exactly
      messages.client_hello_present
      messages.client_hello
      (Ghost.reveal new_hs).CS.hs_client_hello);
  call_ghost
    (reframe_client_hello_metadata messages #old_hs)
    new_hs;
  rewrite (server_hello_slot_exactly
    messages.server_hello
    (Ghost.reveal old_hs).CS.hs_server_hello)
    as (server_hello_slot_exactly
      messages.server_hello
      (Ghost.reveal new_hs).CS.hs_server_hello);
  rewrite (encrypted_extensions_slot_exactly
    messages.encrypted_extensions
    (Ghost.reveal old_hs).CS.hs_encrypted_extensions)
    as (encrypted_extensions_slot_exactly
      messages.encrypted_extensions
      (Ghost.reveal new_hs).CS.hs_encrypted_extensions);
  rewrite (certificate_slot_exactly
    messages.certificate
    (Ghost.reveal old_hs).CS.hs_certificate)
    as (certificate_slot_exactly
      messages.certificate
      (Ghost.reveal new_hs).CS.hs_certificate);
  rewrite (certificate_verify_slot_exactly
    messages.certificate_verify
    (Ghost.reveal old_hs).CS.hs_certificate_verify)
    as (certificate_verify_slot_exactly
      messages.certificate_verify
      (Ghost.reveal new_hs).CS.hs_certificate_verify);
  rewrite (finished_slot_exactly
    messages.server_finished
    (Ghost.reveal old_hs).CS.hs_server_finished)
    as (finished_slot_exactly
      messages.server_finished
      (Ghost.reveal new_hs).CS.hs_server_finished);
  rewrite (finished_slot_exactly
    messages.client_finished
    (Ghost.reveal old_hs).CS.hs_client_finished)
    as (finished_slot_exactly
      messages.client_finished
      (Ghost.reveal new_hs).CS.hs_client_finished);
  fold (handshake_messages_exactly messages (Ghost.reveal new_hs))
}

fn mark_received_change_cipher_spec
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure ((exists stage.
                    st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsChangeCipherSpec;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  unfold (connection_exactly c st0);
  assert (pure ((received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model == st0.CS.cs_model));
  lemma_received_change_cipher_spec_state_evolves st0 (Ghost.reveal 'raw_bytes);
  MR.update c.ghost_state (received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes));
  fold (connection_exactly c (received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes)))
}

fn mark_received_alert_failure
  (c:connection_state)
  (raw:array U8.t)
  (alert_wire:U8.t)
  (#alert:erased T.alert_description)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (Ghost.reveal alert <> T.Close_notify /\
                 Tags.alert_tag_matches alert_wire (Ghost.reveal alert) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert (Ghost.reveal alert);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_alert_failure_state st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (Ghost.reveal alert <> T.Close_notify));
  assert (pure (Tags.alert_tag_matches alert_wire (Ghost.reveal alert)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert (Ghost.reveal alert);
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 0uy;
  c.control.failure_alert := alert_wire;

  assert (pure (Tags.tls_error_code_matches 0uy alert_wire (T.AlertError (Ghost.reveal alert))));
  assert (pure (Tags.control_state_matches
    5uy
    0uy
    true
    0uy
    alert_wire
    (CS.ControlFailed (T.AlertError (Ghost.reveal alert)))));
  fold (control_exactly
    c.control
    (CS.ControlFailed (T.AlertError (Ghost.reveal alert)))
    (Some (T.AlertError (Ghost.reveal alert))));
  assert (pure ((CS.fail_model st0.CS.cs_model (T.AlertError (Ghost.reveal alert))).CS.model_control ==
                CS.ControlFailed (T.AlertError (Ghost.reveal alert))));
  assert (pure ((CS.fail_model st0.CS.cs_model (T.AlertError (Ghost.reveal alert))).CS.model_failure ==
                Some (T.AlertError (Ghost.reveal alert))));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model (T.AlertError (Ghost.reveal alert))));

  lemma_received_alert_failure_state_evolves st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes);
  MR.update c.ghost_state (received_alert_failure_state st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly c (received_alert_failure_state st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)))
}

fn mark_received_close_notify_for_role
  (c:connection_state)
  (raw:array U8.t)
  (#role:erased CS.endpoint_role)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure ((st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == role /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert T.Close_notify;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                st0.CS.cs_model.CS.model_control == CS.ControlClosing));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert T.Close_notify;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  assert (pure (st0.CS.cs_model.CS.model_failure == None));
  c.control.control_tag := 4uy;
  c.control.handshake_stage_tag := 0uy;
  c.control.failure_present := false;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 0uy;

  assert (pure (Tags.control_state_matches
    4uy
    0uy
    false
    0uy
    0uy
    CS.ControlClosed));
  fold (control_exactly
    c.control
    CS.ControlClosed
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  assert (pure ((received_close_notify_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control ==
                CS.ControlClosed));
  assert (pure ((received_close_notify_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_failure ==
                st0.CS.cs_model.CS.model_failure));
  fold (connection_model_exactly
    c
    (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_close_notify_state_evolves_for_role
    role
    st0
    (Ghost.reveal 'raw_bytes);
  MR.update c.ghost_state (received_close_notify_state st0 (Ghost.reveal 'raw_bytes));
  fold (connection_exactly c (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)))
}

fn mark_received_close_notify
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure ((st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                  st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert T.Close_notify;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  mark_received_close_notify_for_role c raw #CS.ClientEndpoint
}

fn mark_received_hello_retry_request_rejected
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloSent /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_hello_retry_request_rejected_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloSent));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake M.HelloRetryRequest;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 4uy;
  c.control.failure_alert := 0uy;

  assert (pure (Tags.tls_error_code_matches
    4uy
    0uy
    tls_hello_retry_request_rejected_error));
  assert (pure (Tags.control_state_matches
    5uy
    0uy
    true
    4uy
    0uy
    (CS.ControlFailed tls_hello_retry_request_rejected_error)));
  fold (control_exactly
    c.control
    (CS.ControlFailed tls_hello_retry_request_rejected_error)
    (Some tls_hello_retry_request_rejected_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_hello_retry_request_rejected_error).CS.model_control ==
                CS.ControlFailed tls_hello_retry_request_rejected_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_hello_retry_request_rejected_error).CS.model_failure ==
                Some tls_hello_retry_request_rejected_error));
  fold (connection_model_exactly
    c
    (CS.fail_model st0.CS.cs_model tls_hello_retry_request_rejected_error));

  lemma_received_hello_retry_request_rejected_state_evolves
    st0
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_hello_retry_request_rejected_state st0 (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_hello_retry_request_rejected_state st0 (Ghost.reveal 'raw_bytes)))
}

let lemma_received_server_hello_state_server_hello
  (st:CS.connection_state) (sh:GSH.serverHello) (raw:B.bytes)
  : Lemma
      (ensures (received_server_hello_state st sh raw).CS.cs_model.CS.model_handshake.CS.hs_server_hello
               == Some sh)
  = ()

fn mark_received_server_hello
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased GSH.serverHello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloSent /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 SZ.v fragment_len <= max_server_hello_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.ServerHello sh)) /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   B.length (W.serialize_handshake (M.ServerHello sh)) <=
                   max_transcript_len /\
                 CS.legal_event
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh);
                   }) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloSent));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  // TODO-A1: Phase 4 deleted W.lemma_serialize_server_hello_len, whose structural
  // guarantee `B.length (serialize_handshake (M.ServerHello sh)) <= max_server_hello_len`
  // is no longer a theorem.  The bound `SZ.v fragment_len <= max_server_hello_len`
  // is now a (caller-discharged) precondition; recover the serialize-length bound
  // from the precondition's Seq.equal fact.
  Seq.lemma_eq_elim (Ghost.reveal 'fragment_bytes) (W.serialize_handshake (M.ServerHello sh));
  assert (pure (B.length (W.serialize_handshake (M.ServerHello sh)) <= max_server_hello_len));
  assert (pure (SZ.v fragment_len <= max_server_hello_len));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);
  unfold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some sh -> CS.server_hello_key_share sh
     | None -> None));
  with old_server_key_share_present old_server_key_share_storage. _;

  c.control.handshake_stage_tag := 3uy;

  assert (pure (Tags.control_state_matches
    1uy
    3uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerHelloReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerHelloReceived)
    st0.CS.cs_model.CS.model_failure);

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
  with stored_server_hello. _;
  drop_ (match stored_server_hello, st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_server_hello old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.server_hello := Some lsh;

  unfold (IM.is_valid_server_hello lsh sh);
  with lsh_random lsh_key_share. _;
  V.to_array_pts_to lsh.IM.server_hello_key_share;
  V.to_array_pts_to c.handshake.server_key_share.bytes;
  Arr.memcpy
    32sz
    (V.vec_to_array lsh.IM.server_hello_key_share)
    (V.vec_to_array c.handshake.server_key_share.bytes);
  V.to_vec_pts_to lsh.IM.server_hello_key_share;
  V.to_vec_pts_to c.handshake.server_key_share.bytes;
  c.handshake.server_key_share.present := true;
  with copied_server_key_share. assert (V.pts_to c.handshake.server_key_share.bytes copied_server_key_share);
  assert (pure (Some? (CS.server_hello_key_share (Ghost.reveal sh)) /\
    Seq.equal copied_server_key_share (Some?.v (CS.server_hello_key_share (Ghost.reveal sh)))));
  assert (pure (optional_fixed_bytes_match true copied_server_key_share 32 (CS.server_hello_key_share (Ghost.reveal sh))));
  lemma_received_server_hello_state_server_hello st0 sh (Ghost.reveal 'raw_bytes);
  fold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (match (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some sh -> CS.server_hello_key_share sh
     | None -> None));
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (IM.is_valid_server_hello lsh sh);

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (sized_bytes_exactly
    c.handshake.buffers.server_hello_bytes
    max_server_hello_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes);

  with old_server_hello_storage old_server_hello_len. _;
  V.to_array_pts_to c.handshake.buffers.server_hello_bytes.bytes;
  ArrPts.pts_to_len fragment;
  ArrPts.pts_to_len (V.vec_to_array c.handshake.buffers.server_hello_bytes.bytes);
  Arr.memcpy_l fragment_len fragment (V.vec_to_array c.handshake.buffers.server_hello_bytes.bytes);
  V.to_vec_pts_to c.handshake.buffers.server_hello_bytes.bytes;
  with server_hello_storage. assert (V.pts_to c.handshake.buffers.server_hello_bytes.bytes server_hello_storage);
  Seq.lemma_len_slice server_hello_storage 0 (SZ.v fragment_len);
  assert (pure (Seq.equal
    (Seq.slice server_hello_storage 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes)));
  assert (pure (Seq.equal
    (Seq.slice server_hello_storage 0 (SZ.v fragment_len))
    (W.serialize_handshake (M.ServerHello sh))));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_server_hello_prefix_to_transcript
    c.handshake.buffers.server_hello_bytes.bytes
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_server_hello_storage copied_transcript_storage.
    assert (V.pts_to c.handshake.buffers.server_hello_bytes.bytes copied_server_hello_storage **
            V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (copied_server_hello_storage == server_hello_storage));

  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.buffers.server_hello_bytes.len := fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  fold (sized_bytes_exactly
    c.handshake.buffers.server_hello_bytes
    max_server_hello_len
    (W.serialize_handshake (M.ServerHello sh)));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.ServerHello sh))));

  fold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    (Some (Ghost.reveal sh)));
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly
    c.handshake
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_server_hello_state_evolves
    st0
    sh
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)))
}

fn mark_received_client_hello
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lch:IM.client_hello)
  (#ch:erased GCH.clientHello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_client_hello lch ch **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsAwaitingClientHello /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                 Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 SZ.v fragment_len <= max_client_hello_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.ClientHello ch)) /\
                 lch.IM.client_hello_has_server_name == true /\
                 client_hello_server_name_len_for ch ==
                   lch.IM.client_hello_server_name_len /\
                 client_hello_cipher_suites_len_for ch ==
                   lch.IM.client_hello_cipher_suites_len /\
                 client_hello_signature_schemes_len_for ch ==
                   lch.IM.client_hello_signature_schemes_len /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   B.length (W.serialize_handshake (M.ClientHello ch)) <=
                   max_transcript_len /\
                 CS.legal_event
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ClientHello ch);
                   }) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ClientHello ch);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
          IM.is_valid_client_hello lch ch
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsAwaitingClientHello));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    })));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 13uy;

  assert (pure (Tags.control_state_matches
    1uy
    13uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsClientHelloReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsClientHelloReceived)
    st0.CS.cs_model.CS.model_failure);

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with old_client_hello_present old_l_random old_l_server_name
       old_l_key_share old_l_cipher_suites old_l_signature_schemes. _;
  unfold (client_hello_metadata_exactly
    c.handshake.messages.client_hello_has_server_name
    c.handshake.messages.client_hello_server_name_len
    c.handshake.messages.client_hello_cipher_suites_len
    c.handshake.messages.client_hello_signature_schemes_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with old_ch_has_server_name old_ch_server_name_len
       old_ch_cipher_suites_len old_ch_signature_schemes_len. _;
  assert (pure (old_client_hello_present == false));
  assert (pure (old_ch_has_server_name == false));

  unfold (IM.is_valid_client_hello lch ch);
  with lch_random lch_server_name lch_key_share
       lch_cipher_suites lch_signature_schemes. _;

  V.to_array_pts_to lch.IM.client_hello_random;
  V.to_array_pts_to c.handshake.messages.client_hello.IM.client_hello_random;
  Arr.memcpy
    32sz
    (V.vec_to_array lch.IM.client_hello_random)
    (V.vec_to_array c.handshake.messages.client_hello.IM.client_hello_random);
  V.to_vec_pts_to lch.IM.client_hello_random;
  V.to_vec_pts_to c.handshake.messages.client_hello.IM.client_hello_random;

  V.to_array_pts_to lch.IM.client_hello_server_name;
  V.to_array_pts_to c.handshake.messages.client_hello.IM.client_hello_server_name;
  Arr.memcpy
    max_hostname_len_sz
    (V.vec_to_array lch.IM.client_hello_server_name)
    (V.vec_to_array c.handshake.messages.client_hello.IM.client_hello_server_name);
  V.to_vec_pts_to lch.IM.client_hello_server_name;
  V.to_vec_pts_to c.handshake.messages.client_hello.IM.client_hello_server_name;

  V.to_array_pts_to lch.IM.client_hello_key_share;
  V.to_array_pts_to c.handshake.messages.client_hello.IM.client_hello_key_share;
  Arr.memcpy
    32sz
    (V.vec_to_array lch.IM.client_hello_key_share)
    (V.vec_to_array c.handshake.messages.client_hello.IM.client_hello_key_share);
  V.to_vec_pts_to lch.IM.client_hello_key_share;
  V.to_vec_pts_to c.handshake.messages.client_hello.IM.client_hello_key_share;

  V.to_array_pts_to lch.IM.client_hello_cipher_suites;
  V.to_array_pts_to c.handshake.messages.client_hello.IM.client_hello_cipher_suites;
  Arr.memcpy
    max_cipher_suites_sz
    (V.vec_to_array lch.IM.client_hello_cipher_suites)
    (V.vec_to_array c.handshake.messages.client_hello.IM.client_hello_cipher_suites);
  V.to_vec_pts_to lch.IM.client_hello_cipher_suites;
  V.to_vec_pts_to c.handshake.messages.client_hello.IM.client_hello_cipher_suites;

  V.to_array_pts_to lch.IM.client_hello_signature_schemes;
  V.to_array_pts_to c.handshake.messages.client_hello.IM.client_hello_signature_schemes;
  Arr.memcpy
    max_signature_schemes_sz
    (V.vec_to_array lch.IM.client_hello_signature_schemes)
    (V.vec_to_array c.handshake.messages.client_hello.IM.client_hello_signature_schemes);
  V.to_vec_pts_to lch.IM.client_hello_signature_schemes;
  V.to_vec_pts_to c.handshake.messages.client_hello.IM.client_hello_signature_schemes;

  c.handshake.messages.client_hello_present := true;
  c.handshake.messages.client_hello_has_server_name :=
    lch.IM.client_hello_has_server_name;
  c.handshake.messages.client_hello_server_name_len :=
    lch.IM.client_hello_server_name_len;
  c.handshake.messages.client_hello_cipher_suites_len :=
    lch.IM.client_hello_cipher_suites_len;
  c.handshake.messages.client_hello_signature_schemes_len :=
    lch.IM.client_hello_signature_schemes_len;

  with stored_random. assert (V.pts_to c.handshake.messages.client_hello.IM.client_hello_random stored_random);
  with stored_server_name. assert (V.pts_to c.handshake.messages.client_hello.IM.client_hello_server_name stored_server_name);
  with stored_key_share. assert (V.pts_to c.handshake.messages.client_hello.IM.client_hello_key_share stored_key_share);
  with stored_cipher_suites. assert (V.pts_to c.handshake.messages.client_hello.IM.client_hello_cipher_suites stored_cipher_suites);
  with stored_signature_schemes. assert (V.pts_to c.handshake.messages.client_hello.IM.client_hello_signature_schemes stored_signature_schemes);

  assert (pure (Seq.equal stored_random (Sem.clientHello_random (Ghost.reveal ch))));
  assert (pure (IM.optional_byte_prefix_matches
    true
    stored_server_name
    (client_hello_server_name_len_for (Ghost.reveal ch))
    (Sem.clientHello_server_name (Ghost.reveal ch))));
  assert (pure (match Sem.clientHello_key_share_x25519 (Ghost.reveal ch) with
    | Some k -> B.length k == 32 /\ Seq.equal stored_key_share k
    | None -> False));
  assert (pure (IM.cipher_suites_match
    stored_cipher_suites
    (SZ.v (client_hello_cipher_suites_len_for (Ghost.reveal ch)))
    (Sem.clientHello_cipher_suites (Ghost.reveal ch))));
  assert (pure (match Sem.clientHello_sig_algs (Ghost.reveal ch) with
    | Some sas ->
      IM.signature_schemes_match
        stored_signature_schemes
        (SZ.v (client_hello_signature_schemes_len_for (Ghost.reveal ch)))
        sas
    | None -> False));

  V.pts_to_len lch.IM.client_hello_random;
  V.pts_to_len lch.IM.client_hello_server_name;
  V.pts_to_len lch.IM.client_hello_key_share;
  V.pts_to_len lch.IM.client_hello_cipher_suites;
  V.pts_to_len lch.IM.client_hello_signature_schemes;
  V.pts_to_len c.handshake.messages.client_hello.IM.client_hello_random;
  V.pts_to_len c.handshake.messages.client_hello.IM.client_hello_server_name;
  V.pts_to_len c.handshake.messages.client_hello.IM.client_hello_key_share;
  V.pts_to_len c.handshake.messages.client_hello.IM.client_hello_cipher_suites;
  V.pts_to_len c.handshake.messages.client_hello.IM.client_hello_signature_schemes;

  fold (IM.is_valid_client_hello lch ch);
  fold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    (Some (Ghost.reveal ch)));
  fold (client_hello_metadata_exactly
    c.handshake.messages.client_hello_has_server_name
    c.handshake.messages.client_hello_server_name_len
    c.handshake.messages.client_hello_cipher_suites_len
    c.handshake.messages.client_hello_signature_schemes_len
    (Some (Ghost.reveal ch)));

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;
  unfold (sized_bytes_exactly
    c.handshake.buffers.client_hello_bytes
    max_client_hello_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes);
  with old_client_hello_storage old_client_hello_len. _;
  V.to_array_pts_to c.handshake.buffers.client_hello_bytes.bytes;
  ArrPts.pts_to_len fragment;
  ArrPts.pts_to_len (V.vec_to_array c.handshake.buffers.client_hello_bytes.bytes);
  Arr.memcpy_l fragment_len fragment (V.vec_to_array c.handshake.buffers.client_hello_bytes.bytes);
  V.to_vec_pts_to c.handshake.buffers.client_hello_bytes.bytes;
  with client_hello_storage. assert (V.pts_to c.handshake.buffers.client_hello_bytes.bytes client_hello_storage);
  Seq.lemma_len_slice client_hello_storage 0 (SZ.v fragment_len);
  assert (pure (Seq.equal
    (Seq.slice client_hello_storage 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes)));
  assert (pure (Seq.equal
    (Seq.slice client_hello_storage 0 (SZ.v fragment_len))
    (W.serialize_handshake (M.ClientHello ch))));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_client_hello_prefix_to_transcript
    c.handshake.buffers.client_hello_bytes.bytes
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_client_hello_storage copied_transcript_storage.
    assert (V.pts_to c.handshake.buffers.client_hello_bytes.bytes copied_client_hello_storage **
            V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (copied_client_hello_storage == client_hello_storage));

  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.buffers.client_hello_bytes.len := fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  fold (sized_bytes_exactly
    c.handshake.buffers.client_hello_bytes
    max_client_hello_len
    (W.serialize_handshake (M.ClientHello ch)));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.ClientHello ch))));

  fold (handshake_messages_exactly
    c.handshake.messages
    (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_exactly
    c.handshake
    (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_client_hello_state_evolves
    st0
    ch
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)))
}

fn store_pending_protected_handshake
  (c:connection_state)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (parsed:SZ.t)
  (#model:erased CS.connection_model)
  requires connection_model_exactly c model **
           ArrPts.pts_to fragment 'fragment_bytes **
           pure (
             CS.protected_handshake_buffer_empty (Ghost.reveal model) /\
             B.length (Ghost.reveal 'fragment_bytes) == SZ.v fragment_len /\
             SZ.v fragment_len <= max_handshake_flight_len /\
             SZ.v parsed < SZ.v fragment_len)
  ensures connection_model_exactly
            c
            (CS.set_pending_protected_handshake
              (Ghost.reveal model)
              (Ghost.reveal 'fragment_bytes)
              (SZ.v parsed)) **
          ArrPts.pts_to fragment 'fragment_bytes
{
  let target_model = Ghost.hide (
    CS.set_pending_protected_handshake
      (Ghost.reveal model)
      (Ghost.reveal 'fragment_bytes)
      (SZ.v parsed));
  unfold (connection_model_exactly c (Ghost.reveal model));
  unfold (handshake_exactly
    c.handshake
    (Ghost.reveal model).CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    (Ghost.reveal model).CS.model_handshake.CS.hs_buffers);
  with old_parsed. _;
  unfold (sized_bytes_exactly
    c.handshake.buffers.encrypted_server_handshake_bytes
    max_handshake_flight_len
    (Ghost.reveal model).CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes);
  fold (sized_bytes_allocated
    c.handshake.buffers.encrypted_server_handshake_bytes
    max_handshake_flight_len);
  copy_array_to_sized_bytes
    fragment
    c.handshake.buffers.encrypted_server_handshake_bytes
    max_handshake_flight_len_sz
    fragment_len;
  c.handshake.buffers.encrypted_server_handshake_parsed := parsed;
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_start ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_start));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_server_selection ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_selection));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_server_hello ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_hello));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_validated_peer ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_transcript ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_transcript));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_keys ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_keys));
  rewrite (handshake_start_exactly
    c.handshake.start
    (Ghost.reveal model).CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_start);
  rewrite (server_selection_presence_exactly
    c.handshake.server_selection_present
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_selection)
    as (server_selection_presence_exactly
      c.handshake.server_selection_present
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_server_selection);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    (Ghost.reveal model).CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (Ghost.reveal target_model).CS.model_handshake);
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_server_selection ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_selection));
  call_ghost
    (reframe_server_key_share_private
      c.handshake.server_key_share_private
      #(Ghost.hide (Ghost.reveal model).CS.model_handshake))
    (Ghost.hide (Ghost.reveal target_model).CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    (Ghost.reveal model).CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_validated_peer);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (Ghost.reveal model).CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_transcript);
  rewrite (key_schedule_exactly
    c.handshake.keys
    (Ghost.reveal model).CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_keys);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (Ghost.reveal target_model).CS.model_handshake.CS.hs_buffers);
  call_ghost
    (reframe_handshake_messages
      c.handshake.messages
      #(Ghost.hide (Ghost.reveal model).CS.model_handshake))
    (Ghost.hide (Ghost.reveal target_model).CS.model_handshake);
  fold (handshake_exactly
    c.handshake
    (Ghost.reveal target_model).CS.model_handshake);
  fold (connection_model_exactly
    c
    (Ghost.reveal target_model))
}

fn advance_pending_protected_handshake_storage
  (c:connection_state)
  (parsed:SZ.t)
  (#fragment:erased B.bytes)
  requires sized_bytes_exactly
             c.handshake.buffers.encrypted_server_handshake_bytes
             max_handshake_flight_len
             (Ghost.reveal fragment) **
           (exists* old_parsed.
              Box.pts_to
                c.handshake.buffers.encrypted_server_handshake_parsed
                old_parsed **
              pure (
                SZ.v old_parsed < SZ.v parsed /\
                SZ.v parsed <= B.length (Ghost.reveal fragment)))
  ensures sized_bytes_exactly
            c.handshake.buffers.encrypted_server_handshake_bytes
            max_handshake_flight_len
            (pending_protected_bytes
              (Ghost.reveal fragment)
              (SZ.v parsed)) **
          (exists* new_parsed.
             Box.pts_to
               c.handshake.buffers.encrypted_server_handshake_parsed
               new_parsed **
             pure (
               SZ.v new_parsed ==
                 pending_protected_offset
                   (Ghost.reveal fragment)
                   (SZ.v parsed)))
{
  with old_parsed.
  unfold (sized_bytes_exactly
    c.handshake.buffers.encrypted_server_handshake_bytes
    max_handshake_flight_len
    (Ghost.reveal fragment));
  with stored_fragment stored_len. _;
  let actual_len =
    !c.handshake.buffers.encrypted_server_handshake_bytes.len;
  assert (pure (actual_len == stored_len));
  assert (pure (SZ.v stored_len == B.length (Ghost.reveal fragment)));
  let has_remaining = SZ.lt parsed actual_len;
  assert (pure (has_remaining == SZ.lt parsed stored_len));
  if has_remaining {
    assert (pure (SZ.v parsed < B.length (Ghost.reveal fragment)));
    c.handshake.buffers.encrypted_server_handshake_parsed := parsed;
    fold (sized_bytes_exactly
      c.handshake.buffers.encrypted_server_handshake_bytes
      max_handshake_flight_len
      (Ghost.reveal fragment));
  } else {
    assert (pure (SZ.lt parsed stored_len == false));
    assert (pure (SZ.v parsed == SZ.v actual_len));
    c.handshake.buffers.encrypted_server_handshake_bytes.len := 0sz;
    c.handshake.buffers.encrypted_server_handshake_parsed := 0sz;
    Seq.lemma_len_slice stored_fragment 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice stored_fragment 0 0);
    fold (sized_bytes_exactly
      c.handshake.buffers.encrypted_server_handshake_bytes
      max_handshake_flight_len
      B.empty);
  }
}

fn advance_pending_protected_handshake
  (c:connection_state)
  (parsed:SZ.t)
  (#model:erased CS.connection_model)
  requires connection_model_exactly c model **
           pure (
             B.length
               (Ghost.reveal model).CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes >
               0 /\
             (Ghost.reveal model).CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed <
               SZ.v parsed /\
             SZ.v parsed <=
               B.length
                 (Ghost.reveal model).CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes)
  ensures connection_model_exactly
            c
            (CS.set_pending_protected_handshake
              (Ghost.reveal model)
              (Ghost.reveal model).CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes
              (SZ.v parsed))
{
  let target_model = Ghost.hide (
    CS.set_pending_protected_handshake
      (Ghost.reveal model)
      (Ghost.reveal model).CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes
      (SZ.v parsed));
  unfold (connection_model_exactly c (Ghost.reveal model));
  unfold (handshake_exactly
    c.handshake
    (Ghost.reveal model).CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    (Ghost.reveal model).CS.model_handshake.CS.hs_buffers);
  with old_parsed. _;
  advance_pending_protected_handshake_storage
    c
    parsed
    #(Ghost.hide
      (Ghost.reveal model).CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes);
  with new_parsed. _;
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_start ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_start));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_server_selection ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_selection));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_server_hello ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_hello));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_validated_peer ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_transcript ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_transcript));
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_keys ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_keys));
  rewrite (handshake_start_exactly
    c.handshake.start
    (Ghost.reveal model).CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_start);
  rewrite (server_selection_presence_exactly
    c.handshake.server_selection_present
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_selection)
    as (server_selection_presence_exactly
      c.handshake.server_selection_present
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_server_selection);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    (Ghost.reveal model).CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (Ghost.reveal target_model).CS.model_handshake);
  assert (pure ((Ghost.reveal target_model).CS.model_handshake.CS.hs_server_selection ==
    (Ghost.reveal model).CS.model_handshake.CS.hs_server_selection));
  call_ghost
    (reframe_server_key_share_private
      c.handshake.server_key_share_private
      #(Ghost.hide (Ghost.reveal model).CS.model_handshake))
    (Ghost.hide (Ghost.reveal target_model).CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    (Ghost.reveal model).CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_validated_peer);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (Ghost.reveal model).CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_transcript);
  rewrite (key_schedule_exactly
    c.handshake.keys
    (Ghost.reveal model).CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (Ghost.reveal target_model).CS.model_handshake.CS.hs_keys);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (Ghost.reveal target_model).CS.model_handshake.CS.hs_buffers);
  call_ghost
    (reframe_handshake_messages
      c.handshake.messages
      #(Ghost.hide (Ghost.reveal model).CS.model_handshake))
    (Ghost.hide (Ghost.reveal target_model).CS.model_handshake);
  fold (handshake_exactly
    c.handshake
    (Ghost.reveal target_model).CS.model_handshake);
  fold (connection_model_exactly
    c
    (Ghost.reveal target_model))
}

fn restore_previous_read_sequence
  (c:connection_state)
  (#previous:erased R.direction_state)
  (#model:erased CS.connection_model)
  requires connection_model_exactly c model **
           pure (
             (Ghost.reveal model).CS.model_record.CS.record_read ==
               R.next_seq (Ghost.reveal previous))
  ensures connection_model_exactly
            c
            (restored_read_sequence_model
              (Ghost.reveal model)
              (Ghost.reveal previous))
{
  unfold (connection_model_exactly c (Ghost.reveal model));
  unfold (record_layer_exactly
    c.records
    (Ghost.reveal model).CS.model_record);
  rewrite (Rec.is_record_state
    c.records.read
    (Ghost.reveal model).CS.model_record.CS.record_read)
    as (Rec.is_record_state
      c.records.read
      (R.next_seq (Ghost.reveal previous)));
  Rec.restore_previous_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { (Ghost.reveal model).CS.model_record with
        CS.record_read = Ghost.reveal previous;
    });
  fold (connection_model_exactly
    c
    (restored_read_sequence_model
      (Ghost.reveal model)
      (Ghost.reveal previous)))
}

fn apply_received_encrypted_extensions
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lee:IM.encrypted_extensions)
  (#ee:erased GEE.encryptedExtensions)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_encrypted_extensions lee ee **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerHelloReceived /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.EncryptedExtensions ee)) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len)
  ensures MR.pts_to c.ghost_state #1.0R st0 **
          connection_model_exactly
            c
            (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model **
          pure (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st0) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerHelloReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 4uy;
  assert (pure (Tags.control_state_matches
    1uy
    4uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsEncryptedExtensionsReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsEncryptedExtensionsReceived)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
  with stored_encrypted_extensions. _;
  drop_ (match stored_encrypted_extensions, st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_encrypted_extensions old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.encrypted_extensions := Some lee;
  fold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    (Some (Ghost.reveal ee)));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_array_to_transcript
    fragment
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (Ghost.reveal 'fragment_bytes)
    (W.serialize_handshake (M.EncryptedExtensions ee))));
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'fragment_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.EncryptedExtensions ee)))));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.EncryptedExtensions ee))));

  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_exactly
    c.handshake
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model);

}

fn mark_received_encrypted_extensions
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lee:IM.encrypted_extensions)
  (#ee:erased GEE.encryptedExtensions)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_encrypted_extensions lee ee **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerHelloReceived /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.EncryptedExtensions ee)) /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= max_transcript_len /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes
{
  apply_received_encrypted_extensions
    c raw fragment fragment_len lee #ee #st0;
  lemma_received_encrypted_extensions_state_evolves
    st0
    ee
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)))
}

fn mark_received_protected_encrypted_extensions
  (c:connection_state)
  (raw:array U8.t)
  (message_fragment:array U8.t)
  (message_len:SZ.t)
  (protected_fragment:array U8.t)
  (protected_fragment_len:SZ.t)
  (lee:IM.encrypted_extensions)
  (#ee:erased GEE.encryptedExtensions)
  (#step:erased CS.protected_handshake_step)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           ArrPts.pts_to message_fragment 'message_fragment_bytes **
           ArrPts.pts_to protected_fragment 'protected_fragment_bytes **
           IM.is_valid_encrypted_extensions lee ee **
           pure (
             (Ghost.reveal step).CS.protected_handshake_message ==
               M.EncryptedExtensions (Ghost.reveal ee) /\
             Seq.equal
               (Ghost.reveal step).CS.protected_handshake_fragment
               (Ghost.reveal 'protected_fragment_bytes) /\
             (Ghost.reveal step).CS.protected_handshake_offset == 0 /\
             (Ghost.reveal step).CS.protected_handshake_consumed == SZ.v message_len /\
             (Ghost.reveal step).CS.protected_handshake_head /\
             B.length (Ghost.reveal 'message_fragment_bytes) == SZ.v message_len /\
             Seq.equal
               (Ghost.reveal 'message_fragment_bytes)
               (W.serialize_handshake (M.EncryptedExtensions (Ghost.reveal ee))) /\
             B.length (Ghost.reveal 'protected_fragment_bytes) ==
               SZ.v protected_fragment_len /\
             SZ.v protected_fragment_len <= max_handshake_flight_len /\
             SZ.v message_len < SZ.v protected_fragment_len /\
             st0.CS.cs_model.CS.model_control ==
               CS.ControlHandshaking CS.HsServerHelloReceived /\
             st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
             Some?
               st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
             U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
             B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
               SZ.v message_len <= max_transcript_len /\
             CS.legal_event
               st0.CS.cs_model
               (CS.ConnProtectedHandshake (Ghost.reveal step)) /\
             Some?
               (CS.step_protected_handshake
                 st0.CS.cs_model
                 (Ghost.reveal step)) /\
             CS.event_raw_delta_legal
               st0.CS.cs_model
               (CS.ConnProtectedHandshake (Ghost.reveal step))
               B.empty
               (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (protected_handshake_state
              st0
              (Ghost.reveal step)
              (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes **
          ArrPts.pts_to message_fragment 'message_fragment_bytes **
          ArrPts.pts_to protected_fragment 'protected_fragment_bytes
{
  apply_received_encrypted_extensions
    c
    raw
    message_fragment
    message_len
    lee
    #ee
    #st0;
  store_pending_protected_handshake
    c
    protected_fragment
    protected_fragment_len
    message_len
    #(Ghost.hide
      (received_encrypted_extensions_state
        st0
        (Ghost.reveal ee)
        (Ghost.reveal 'raw_bytes)).CS.cs_model);
  assert (pure (
    (protected_handshake_state
      st0
      (Ghost.reveal step)
      (Ghost.reveal 'raw_bytes)).CS.cs_model ==
    (CS.set_pending_protected_handshake
      (received_encrypted_extensions_state
        st0
        (Ghost.reveal ee)
        (Ghost.reveal 'raw_bytes)).CS.cs_model
      (Ghost.reveal 'protected_fragment_bytes)
      (SZ.v message_len))));
  lemma_protected_handshake_state_evolves
    st0
    (Ghost.reveal step)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (protected_handshake_state
      st0
      (Ghost.reveal step)
      (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (protected_handshake_state
      st0
      (Ghost.reveal step)
      (Ghost.reveal 'raw_bytes)))
}

fn apply_received_certificate
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcert:IM.certificate_msg)
  (#cert:erased GCert.certificate)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_msg lcert cert **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
           st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
           Sem.certificate_entries (Ghost.reveal cert) <> [] /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len)
  ensures MR.pts_to c.ghost_state #1.0R st0 **
          connection_model_exactly
            c
            (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model **
          pure (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st0) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
          pure (match Sem.certificate_entries (Ghost.reveal cert) with
                | leaf :: _ ->
                  (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).
                    CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
                    Some leaf
                | [] -> False)
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsEncryptedExtensionsReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));
  assert (pure (Sem.certificate_entries (Ghost.reveal cert) <> []));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 5uy;
  assert (pure (Tags.control_state_matches
    1uy
    5uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateReceived)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  with stored_certificate. _;
  drop_ (match stored_certificate, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_certificate_msg old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.certificate := Some lcert;

  unfold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
  with chain_bytes offsets lens. _;
  V.pts_to_len lcert.IM.certificate_msg_chain_bytes;
  V.pts_to_len lcert.IM.certificate_msg_cert_offsets;
  V.pts_to_len lcert.IM.certificate_msg_cert_lens;
  assert (pure (B.length chain_bytes == IM.max_certificate_chain_bytes));
  assert (pure (Seq.length offsets == IM.max_certificate_chain_entries));
  assert (pure (Seq.length lens == IM.max_certificate_chain_entries));
  assert (pure (SZ.v lcert.IM.certificate_msg_cert_count > 0));
  lemma_certificate_chain_matches_head
    chain_bytes
    (SZ.v lcert.IM.certificate_msg_chain_bytes_len)
    offsets
    lens
    (SZ.v lcert.IM.certificate_msg_cert_count)
    (Sem.certificate_entries (Ghost.reveal cert));

  assert (pure (SZ.v 0sz < IM.max_certificate_chain_entries));
  V.to_array_pts_to lcert.IM.certificate_msg_cert_offsets;
  let first_offset = (V.vec_to_array lcert.IM.certificate_msg_cert_offsets).(0sz);
  V.to_vec_pts_to lcert.IM.certificate_msg_cert_offsets;
  V.to_array_pts_to lcert.IM.certificate_msg_cert_lens;
  let first_len = (V.vec_to_array lcert.IM.certificate_msg_cert_lens).(0sz);
  V.to_vec_pts_to lcert.IM.certificate_msg_cert_lens;
  assert (pure (first_offset == Seq.index offsets 0));
  assert (pure (first_len == Seq.index lens 0));

  let leaf =
    Ghost.hide
      (match Sem.certificate_entries (Ghost.reveal cert) with
       | cert_leaf :: _ -> cert_leaf
       | [] -> B.empty);
  assert (pure (Seq.equal
    (Ghost.reveal leaf)
    (Seq.slice chain_bytes (SZ.v first_offset) (SZ.v first_offset + SZ.v first_len))));
  assert (pure (SZ.v first_offset + SZ.v first_len <= B.length chain_bytes));
  assert (pure (SZ.v first_len <= max_handshake_flight_len));

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;
  rewrite (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
    as (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_leaf_der
      max_handshake_flight_len
      None);
  overwrite_optional_sized_bytes_from_certificate_chain
    lcert.IM.certificate_msg_chain_bytes
    c.handshake.buffers.certificate_leaf_der
    first_offset
    first_len
    #leaf;

  fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
  fold (certificate_slot_exactly
    c.handshake.messages.certificate
    (Some (Ghost.reveal cert)));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_array_to_transcript
    fragment
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (Ghost.reveal 'fragment_bytes)
    (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'fragment_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Certificate (Ghost.reveal cert))))));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));

  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
    Some (Ghost.reveal leaf)));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly
    c.handshake
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model);

}

fn mark_received_certificate
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcert:IM.certificate_msg)
  (#cert:erased GCert.certificate)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_msg lcert cert **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 Sem.certificate_entries (Ghost.reveal cert) <> [] /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= max_transcript_len /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
          pure (match Sem.certificate_entries (Ghost.reveal cert) with
                | leaf :: _ ->
                  (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).
                    CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
                    Some leaf
                | [] -> False)
{
  apply_received_certificate c raw fragment fragment_len lcert #cert #st0;
  lemma_received_certificate_state_evolves
    st0
    (Ghost.reveal cert)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)))
}

fn apply_received_certificate_verify
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcv:IM.certificate_verify)
  (#cv:erased GCV.certificateVerify)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           ArrPts.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_verify lcv cv **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateValidated /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len)
  ensures MR.pts_to c.ghost_state #1.0R st0 **
          connection_model_exactly
            c
            (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model **
          pure (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st0) **
          ArrPts.pts_to raw 'raw_bytes **
          ArrPts.pts_to fragment 'fragment_bytes **
          pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).
                  CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
                Some
                  (H.certificate_verify_input
                    (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)))
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateValidated));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 7uy;
  assert (pure (Tags.control_state_matches
    1uy
    7uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateVerifyReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateVerifyReceived)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  with stored_certificate_verify. _;
  drop_ (match stored_certificate_verify, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.certificate_verify := Some lcv;
  fold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    (Some (Ghost.reveal cv)));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));
  assert (pure (byte_prefix_matches
    old_transcript_storage
    transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  let mut certificate_verify_input = [| 0uy; 130sz |];
  Ser.build_server_certificate_verify_input
    transcript_hash
    certificate_verify_input
    130sz;
  with certificate_verify_input_bytes.
    assert (ArrPts.pts_to certificate_verify_input certificate_verify_input_bytes);
  assert (pure (B.length certificate_verify_input_bytes == 130));
  assert (pure (B.length transcript_hash_bytes == 32));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  W.lemma_serialize_server_certificate_verify_input_len32
    (Ghost.reveal transcript_hash_bytes);
  assert (pure (Seq.equal
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))
    (H.certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (H.certificate_verify_input (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  let cv_input = Ghost.hide
    (H.certificate_verify_input (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;
  rewrite (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
    as (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      None);
  assert (pure (SZ.v 130sz <= max_certificate_verify_input_len));
  overwrite_optional_certificate_verify_input
    certificate_verify_input
    c.handshake.buffers.certificate_verify_input
    130sz
    #cv_input;

  copy_array_to_transcript
    fragment
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (Ghost.reveal 'fragment_bytes)
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'fragment_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));

  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
    Some (H.certificate_verify_input (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  rewrite (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    (Some (Ghost.reveal cv_input)))
    as (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly
    c.handshake
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model);

}

fn mark_received_certificate_verify
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcv:IM.certificate_verify)
  (#cv:erased GCV.certificateVerify)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           ArrPts.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_verify lcv cv **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateValidated /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= max_transcript_len /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes **
          ArrPts.pts_to fragment 'fragment_bytes **
          pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).
                  CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
                Some
                  (H.certificate_verify_input
                    (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)))
{
  apply_received_certificate_verify c raw fragment fragment_len lcv #cv #st0;
  lemma_received_certificate_verify_state_evolves
    st0
    (Ghost.reveal cv)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)))
}

fn apply_received_server_finished
  (c:connection_state)
  (raw:array U8.t)
  (lfin:IM.finished)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                    max_transcript_len /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
  ensures MR.pts_to c.ghost_state #1.0R st0 **
          connection_model_exactly
            c
            (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model **
          pure (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st0) **
          ArrPts.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateVerifyVerified));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
    max_transcript_len));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  let mut serialized_finished = [| 0uy; 36sz |];

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  // Field equalities between the target state and st0 for all handshake fields
  // that are unchanged by delivery of the server Finished.  These prime the SMT
  // context for the fold operations below.
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    Some (Ghost.reveal fin)));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == true));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));

  // (1) advance control state to HsServerFinishedVerified
  c.control.handshake_stage_tag := 10uy;
  assert (pure (Tags.control_state_matches
    1uy
    10uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerFinishedVerified)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerFinishedVerified)
    st0.CS.cs_model.CS.model_failure);

  // (2) mark the server Finished verified
  c.handshake.server_finished_verified := true;

  // (3) serialize the Finished and store it in the message slot
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  with stored_server_finished. _;
  drop_ (match stored_server_finished, st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False);
  let written_len =
    Ser.serialize_finished_handshake
      #fin
      lfin
      serialized_finished
      36sz;
  with serialized_finished_bytes.
    assert (ArrPts.pts_to serialized_finished serialized_finished_bytes);
  assert (pure (Seq.equal
    serialized_finished_bytes
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (SZ.v written_len == 36));
  assert (pure (B.length (W.serialize_handshake (M.Finished (Ghost.reveal fin))) == 36));
  c.handshake.messages.server_finished := Some lfin;
  fold (finished_slot_exactly
    c.handshake.messages.server_finished
    (Some (Ghost.reveal fin)));
  // NOTE: the fold of handshake_messages_exactly is deferred until after the
  // server-application material has been derived, so that we can fold with an
  // explicit record-with literal for the target handshake_state.  The literal
  // is required because the inner client_hello_metadata_exactly conjunct
  // carries no mkey, so its spec argument must reduce syntactically to st0's
  // (the atomic constructor's `match Some? ks_master_secret` wrapper blocks
  // that reduction on the constructor itself).

  // (4) append the serialized Finished to the transcript
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v written_len <= max_transcript_len));
  copy_array_to_transcript
    serialized_finished
    c.handshake.transcript.bytes
    written_len
    transcript_len;
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v written_len)));
  let new_transcript_len = SZ.add transcript_len written_len;
  c.handshake.transcript.len := new_transcript_len;
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      serialized_finished_bytes)
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  // (5) hash the transcript THROUGH the server Finished
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  with hashed_transcript_storage hashed_transcript_len. _;
  let transcript_len_runtime = !c.handshake.transcript.len;
  assert (pure (transcript_len_runtime == hashed_transcript_len));
  assert (pure (byte_prefix_matches
    hashed_transcript_storage
    transcript_len_runtime
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))
    (Seq.slice hashed_transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))
    (Seq.slice hashed_transcript_storage 0 (SZ.v transcript_len_runtime));
  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes ==
    Tr.hash
      (B.append
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
        (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  // (6) derive the server-application traffic secret and material
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  with ms_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
  with ms_secret_storage.
    assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
  lemma_optional_fixed_bytes_match_present_of_some
    ms_present
    ms_secret_storage
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
    Some ms_secret_storage));
  let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

  V.to_array_pts_to c.handshake.keys.master_secret.secret;
  let mut traffic_secret_out = [| 0uy; 32sz |];
  KS.server_application_traffic_secret
    (V.vec_to_array c.handshake.keys.master_secret.secret)
    transcript_hash
    traffic_secret_out;
  V.to_vec_pts_to c.handshake.keys.master_secret.secret;
  with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
  assert (pure (traffic_secret_bytes ==
    K.server_application_traffic_secret
      (Ghost.reveal ms_secret)
      (Tr.hash
        (B.append
          st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
          (W.serialize_handshake (M.Finished (Ghost.reveal fin)))))));

  let mut traffic_key_out = [| 0uy; 32sz |];
  KS.derive_traffic_key traffic_secret_out traffic_key_out;
  let mut traffic_iv_out = [| 0uy; 12sz |];
  KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
  with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
  with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

  let material = Ghost.hide (CS.traffic_key_material_for_secret traffic_secret_bytes);
  assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));

  // connect the runtime material to the ghost constructor's material
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic ==
    Some (Ghost.reveal material)));

  store_traffic_key_material
    c.handshake.keys.server_application_traffic
    traffic_secret_out
    traffic_key_out
    traffic_iv_out
    #material;
  fold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    ({ st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
        CS.ks_server_application_traffic = Some (Ghost.reveal material) }));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    ({ st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
        CS.ks_server_application_traffic = Some (Ghost.reveal material) })));
  rewrite (key_schedule_exactly
    c.handshake.keys
    ({ st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
        CS.ks_server_application_traffic = Some (Ghost.reveal material) }))
    as (key_schedule_exactly
      c.handshake.keys
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  // Fold handshake_messages_exactly with an explicit record-with literal for
  // the target handshake_state.  Projecting the unchanged fields (e.g.
  // hs_client_hello) out of the literal reduces syntactically to st0's fields,
  // which lets the mkey-less client_hello_metadata_exactly conjunct match.  We
  // then rewrite the folded predicate to the constructor form using the record
  // equality between the literal and the target state.
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (({ st0.CS.cs_model.CS.model_handshake with
        CS.hs_server_finished = Some (Ghost.reveal fin);
        CS.hs_server_finished_verified = true;
        CS.hs_transcript =
          B.append
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.Finished (Ghost.reveal fin)));
        CS.hs_keys =
          { st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
              CS.ks_server_application_traffic = Some (Ghost.reveal material) };
    }) ==
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake));
  fold (handshake_messages_exactly
    c.handshake.messages
    ({ st0.CS.cs_model.CS.model_handshake with
        CS.hs_server_finished = Some (Ghost.reveal fin);
        CS.hs_server_finished_verified = true;
        CS.hs_transcript =
          B.append
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.Finished (Ghost.reveal fin)));
        CS.hs_keys =
          { st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
              CS.ks_server_application_traffic = Some (Ghost.reveal material) };
    }));
  rewrite (handshake_messages_exactly
    c.handshake.messages
    ({ st0.CS.cs_model.CS.model_handshake with
        CS.hs_server_finished = Some (Ghost.reveal fin);
        CS.hs_server_finished_verified = true;
        CS.hs_transcript =
          B.append
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.Finished (Ghost.reveal fin)));
        CS.hs_keys =
          { st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
              CS.ks_server_application_traffic = Some (Ghost.reveal material) };
    }))
    as (handshake_messages_exactly
      c.handshake.messages
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);

  // (7) install the server-application READ keys in the record layer
  Rec.install_application_keys_runtime c.records.read traffic_key_out traffic_iv_out;
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_write ==
    st0.CS.cs_model.CS.model_record.CS.record_write));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_read ==
    R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv));
  rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
    as (Rec.is_record_state
      c.records.write
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_write);
  rewrite (Rec.is_record_state
    c.records.read
    (R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv))
    as (Rec.is_record_state
      c.records.read
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_read);
  fold (record_layer_exactly
    c.records
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record);

  // (8) reassemble the handshake predicate for the target state
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == true));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))))
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly
    c.handshake
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model);

}

fn mark_received_server_finished
  (c:connection_state)
  (raw:array U8.t)
  (lfin:IM.finished)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   max_transcript_len /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes
{
  apply_received_server_finished c raw lfin #fin #st0;
  lemma_received_server_finished_state_evolves
    st0
    (Ghost.reveal fin)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)))
}

fn mark_received_client_finished
  (c:connection_state)
  (raw:array U8.t)
  (lfin:IM.finished)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pure (Model.can_receive_client_finished st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes
{
  assert (pure (Model.can_receive_client_finished st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)));
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedSent));
  assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
    max_transcript_len));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  let mut serialized_finished = [| 0uy; 36sz |];

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  // Field equalities between the target state and st0 for all handshake fields
  // that are unchanged by delivery of the client Finished (everything except
  // hs_client_finished, hs_transcript and hs_keys).  These prime the SMT
  // context for the fold operations below.
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    Some (Ghost.reveal fin)));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));

  // (1) advance control state directly to ControlApplicationData
  c.control.control_tag := 2uy;
  assert (pure (Tags.control_state_matches
    2uy
    10uy
    false
    0uy
    0uy
    CS.ControlApplicationData));
  fold (control_exactly
    c.control
    CS.ControlApplicationData
    st0.CS.cs_model.CS.model_failure);

  // (2) serialize the Finished and store it in the client_finished slot
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  with stored_client_finished. _;
  drop_ (match stored_client_finished, st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False);
  let written_len =
    Ser.serialize_finished_handshake
      #fin
      lfin
      serialized_finished
      36sz;
  with serialized_finished_bytes.
    assert (ArrPts.pts_to serialized_finished serialized_finished_bytes);
  assert (pure (Seq.equal
    serialized_finished_bytes
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (SZ.v written_len == 36));
  assert (pure (B.length (W.serialize_handshake (M.Finished (Ghost.reveal fin))) == 36));
  c.handshake.messages.client_finished := Some lfin;
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    (Some (Ghost.reveal fin)));
  // NOTE: handshake_messages_exactly is re-folded later with an explicit
  // record-with literal, once the client-application material is available.

  // (3) derive the client-application traffic secret from the CURRENT (OLD)
  //     transcript hash, BEFORE appending the client Finished
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (byte_prefix_matches
    old_transcript_storage
    transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len));
  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes ==
    Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  // (4) append the serialized Finished to the transcript
  assert (pure (SZ.v transcript_len + SZ.v written_len <= max_transcript_len));
  copy_array_to_transcript
    serialized_finished
    c.handshake.transcript.bytes
    written_len
    transcript_len;
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v written_len)));
  let new_transcript_len = SZ.add transcript_len written_len;
  c.handshake.transcript.len := new_transcript_len;
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      serialized_finished_bytes)
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  // (5) derive the client-application traffic secret and material
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  with ms_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
  with ms_secret_storage.
    assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
  lemma_optional_fixed_bytes_match_present_of_some
    ms_present
    ms_secret_storage
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
    Some ms_secret_storage));
  let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

  V.to_array_pts_to c.handshake.keys.master_secret.secret;
  let mut traffic_secret_out = [| 0uy; 32sz |];
  KS.client_application_traffic_secret
    (V.vec_to_array c.handshake.keys.master_secret.secret)
    transcript_hash
    traffic_secret_out;
  V.to_vec_pts_to c.handshake.keys.master_secret.secret;
  with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
  assert (pure (traffic_secret_bytes ==
    K.client_application_traffic_secret
      (Ghost.reveal ms_secret)
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  let mut traffic_key_out = [| 0uy; 32sz |];
  KS.derive_traffic_key traffic_secret_out traffic_key_out;
  let mut traffic_iv_out = [| 0uy; 12sz |];
  KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
  with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
  with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

  let material = Ghost.hide (CS.traffic_key_material_for_secret traffic_secret_bytes);
  assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));

  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic ==
    Some (Ghost.reveal material)));

  store_traffic_key_material
    c.handshake.keys.client_application_traffic
    traffic_secret_out
    traffic_key_out
    traffic_iv_out
    #material;
  fold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    ({ st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
        CS.ks_client_application_traffic = Some (Ghost.reveal material) }));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    ({ st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
        CS.ks_client_application_traffic = Some (Ghost.reveal material) })));
  rewrite (key_schedule_exactly
    c.handshake.keys
    ({ st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
        CS.ks_client_application_traffic = Some (Ghost.reveal material) }))
    as (key_schedule_exactly
      c.handshake.keys
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  // Fold handshake_messages_exactly with an explicit record-with literal for
  // the target handshake_state (see the server op for the rationale: the
  // mkey-less client_hello_metadata_exactly conjunct needs its spec argument
  // to reduce syntactically to st0's).
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (({ st0.CS.cs_model.CS.model_handshake with
        CS.hs_client_finished = Some (Ghost.reveal fin);
        CS.hs_transcript =
          B.append
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.Finished (Ghost.reveal fin)));
        CS.hs_keys =
          { st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
              CS.ks_client_application_traffic = Some (Ghost.reveal material) };
    }) ==
    (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake));
  fold (handshake_messages_exactly
    c.handshake.messages
    ({ st0.CS.cs_model.CS.model_handshake with
        CS.hs_client_finished = Some (Ghost.reveal fin);
        CS.hs_transcript =
          B.append
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.Finished (Ghost.reveal fin)));
        CS.hs_keys =
          { st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
              CS.ks_client_application_traffic = Some (Ghost.reveal material) };
    }));
  rewrite (handshake_messages_exactly
    c.handshake.messages
    ({ st0.CS.cs_model.CS.model_handshake with
        CS.hs_client_finished = Some (Ghost.reveal fin);
        CS.hs_transcript =
          B.append
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.Finished (Ghost.reveal fin)));
        CS.hs_keys =
          { st0.CS.cs_model.CS.model_handshake.CS.hs_keys with
              CS.ks_client_application_traffic = Some (Ghost.reveal material) };
    }))
    as (handshake_messages_exactly
      c.handshake.messages
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);

  // (6) install the client-application READ keys in the record layer
  Rec.install_application_keys_runtime c.records.read traffic_key_out traffic_iv_out;
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_write ==
    st0.CS.cs_model.CS.model_record.CS.record_write));
  assert (pure ((received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_read ==
    R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv));
  rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
    as (Rec.is_record_state
      c.records.write
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_write);
  rewrite (Rec.is_record_state
    c.records.read
    (R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv))
    as (Rec.is_record_state
      c.records.read
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_read);
  fold (record_layer_exactly
    c.records
    (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record);

  // (7) reassemble the handshake predicate for the target state
  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))))
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly
    c.handshake
    (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_client_finished_state_evolves
    st0
    (Ghost.reveal fin)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)))
}

fn mark_received_application_data
  (c:connection_state)
  (raw:array U8.t)
  (#bytes:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsApplicationData bytes;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsApplicationData bytes;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  assert (pure (TLS13.Spec.StateMachine.Correspondence.pending_application_consistent
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application);

  assert (pure ((received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control ==
                st0.CS.cs_model.CS.model_control));
  assert (pure ((received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake ==
                st0.CS.cs_model.CS.model_handshake));
  fold (connection_model_exactly
    c
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_application_data_state_evolves
    st0
    bytes
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)))
}

fn mark_received_application_data_for_role
  (c:connection_state)
  (raw:array U8.t)
  (#role:erased CS.endpoint_role)
  (#bytes:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == role /\
                 CS.application_traffic_available_for_role
                   role
                   st0.CS.cs_model.CS.model_handshake
                   CL.Received /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsApplicationData bytes;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (CS.application_traffic_available_for_role
    role
    st0.CS.cs_model.CS.model_handshake
    CL.Received));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsApplicationData bytes;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  assert (pure (TLS13.Spec.StateMachine.Correspondence.pending_application_consistent
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application);

  assert (pure ((received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control ==
                st0.CS.cs_model.CS.model_control));
  assert (pure ((received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake ==
                st0.CS.cs_model.CS.model_handshake));
  fold (connection_model_exactly
    c
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_application_data_state_evolves_for_role
    role
    st0
    bytes
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)))
}

fn mark_received_ignored_post_handshake
  (c:connection_state)
  (raw:array U8.t)
  (#body:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsIgnoredPostHandshake body;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsIgnoredPostHandshake body;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  assert (pure ((received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
                st0.CS.cs_model.CS.model_config));
  assert (pure ((received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control ==
                st0.CS.cs_model.CS.model_control));
  assert (pure ((received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake ==
                st0.CS.cs_model.CS.model_handshake));
  assert (pure ((received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application ==
                st0.CS.cs_model.CS.model_application));
  fold (connection_model_exactly
    c
    (received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_ignored_post_handshake_state_evolves
    st0
    body
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)))
}

fn mark_received_key_update
  (c:connection_state)
  (raw:array U8.t)
  (requested:bool)
  (#req:erased M.key_update_request)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                 (requested ==> req == M.UpdateRequested) /\
                 (requested == false ==> req == M.UpdateNotRequested) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsKeyUpdate req;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (requested ==> req == M.UpdateRequested));
  assert (pure (requested == false ==> req == M.UpdateNotRequested));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsKeyUpdate req;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  with old_present old_secret old_key old_iv. _;
  lemma_traffic_key_material_match_present_of_some
    old_present
    old_secret
    old_key
    old_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic;
  assert (pure (old_present));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic ==
    Some {
      CS.traffic_secret = old_secret;
      CS.traffic_key = old_key;
      CS.traffic_iv = old_iv;
    }));
  let old_material = Ghost.hide (Some?.v
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  assert (pure ((Ghost.reveal old_material).CS.traffic_secret == old_secret));

  V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_secret;
  let mut traffic_secret_out = [| 0uy; 32sz |];
  KS.application_traffic_secret_update
    (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_secret)
    traffic_secret_out;
  V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_secret;
  with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
  assert (pure (traffic_secret_bytes ==
    K.application_traffic_secret_update old_secret));

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  let mut traffic_key_out = [| 0uy; 32sz |];
  KS.derive_traffic_key traffic_secret_out traffic_key_out;
  let mut traffic_iv_out = [| 0uy; 12sz |];
  KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
  with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
  with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

  let traffic_secret = Ghost.hide traffic_secret_bytes;
  let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
  assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
  assert (pure (Ghost.reveal material == CS.updated_traffic_key_material (Ghost.reveal old_material)));

  store_traffic_key_material
    c.handshake.keys.server_application_traffic
    traffic_secret_out
    traffic_key_out
    traffic_iv_out
    #material;

  fold (key_schedule_exactly
    c.handshake.keys
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  Rec.install_application_keys_runtime c.records.read traffic_key_out traffic_iv_out;
  assert (pure (R.install_keys
    st0.CS.cs_model.CS.model_record.CS.record_read
    R.Application
    (Ghost.reveal material).CS.traffic_key
    (Ghost.reveal material).CS.traffic_iv ==
    R.install_keys
      (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read)
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv));
  rewrite (Rec.is_record_state
    c.records.read
    (R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv))
    as (Rec.is_record_state
      c.records.read
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
    as (Rec.is_record_state
      c.records.write
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record);

  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
                st0.CS.cs_model.CS.model_config));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control ==
                st0.CS.cs_model.CS.model_control));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application ==
                CS.received_key_update_pending
                  st0.CS.cs_model.CS.model_application
                  req));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
                st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  rewrite (client_hello_metadata_exactly
    c.handshake.messages.client_hello_has_server_name
    c.handshake.messages.client_hello_server_name_len
    c.handshake.messages.client_hello_cipher_suites_len
    c.handshake.messages.client_hello_signature_schemes_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello) as
    (client_hello_metadata_exactly
      c.handshake.messages.client_hello_has_server_name
      c.handshake.messages.client_hello_server_name_len
      c.handshake.messages.client_hello_cipher_suites_len
      c.handshake.messages.client_hello_signature_schemes_len
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  assert (pure (cv_verified ==
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);

  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config);
  rewrite (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure)
    as (control_exactly
      c.control
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control
      (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_failure);
  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  with source_offset pending_response. _;
  if requested {
    assert (pure (req == M.UpdateRequested));
    c.application.key_update_response_pending := true;
    assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application.CS.app_key_update_response_pending == true));
  } else {
    assert (pure (requested == false));
    assert (pure (req == M.UpdateNotRequested));
    assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application.CS.app_key_update_response_pending ==
                  st0.CS.cs_model.CS.model_application.CS.app_key_update_response_pending));
  };
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application.CS.app_pending_source_record ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_source_record));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application.CS.app_pending_source_offset ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_source_offset));
  assert (pure ((received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application.CS.app_pending_received_raw ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_received_raw));
  assert (pure (TLS13.Spec.StateMachine.Correspondence.pending_application_consistent
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_key_update_state_evolves
    st0
    req
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)))
}
