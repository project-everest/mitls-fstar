module Common.ChannelImplementation

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Common.ProtocolImplementation
module ID = FStar.IndefiniteDescription
module L = FStar.List.Tot
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8
module WFSM = Common.WireFormatStateMachine

noeq
type application_log (message:Type0) = {
  sent: list message;
  received: list message;
}

let empty_application_log (#message:Type0) : application_log message = {
  sent = [];
  received = [];
}

let append_sent
  (#message:Type0)
  (log:application_log message)
  (msg:message)
  : application_log message =
  { log with sent = L.append log.sent [msg] }

let append_received
  (#message:Type0)
  (log:application_log message)
  (msg:message)
  : application_log message =
  { log with received = L.append log.received [msg] }

let application_log_extends
  (#message:Type0)
  (old_log:application_log message)
  (new_log:application_log message)
  : prop =
  exists sent_delta received_delta.
    new_log.sent == L.append old_log.sent sent_delta /\
    new_log.received == L.append old_log.received received_delta

let byte_at (bytes:TCP.bytes) (i:nat) : U8.t =
  if i < Seq.length bytes then Seq.index bytes i else 0uy

noextract
let ordered_subsequence
  (accepted observed:TCP.bytes)
  : prop =
  exists (embedding:nat -> nat).
    (forall (i:nat). i < Seq.length accepted ==>
      embedding i < Seq.length observed /\
      byte_at accepted i == byte_at observed (embedding i)) /\
    (forall (i j:nat).
      i < j /\ j < Seq.length accepted ==>
      embedding i < embedding j)

let lemma_ordered_subsequence_empty
  (observed:TCP.bytes)
  : Lemma (ordered_subsequence (Seq.empty #U8.t) observed)
=
  let embedding (_:nat) : nat = 0 in
  FStar.Classical.exists_intro
    (fun embedding' ->
      (forall (i:nat). i < Seq.length (Seq.empty #U8.t) ==>
        embedding' i < Seq.length observed /\
        byte_at (Seq.empty #U8.t) i ==
          byte_at observed (embedding' i)) /\
      (forall (i j:nat).
        i < j /\ j < Seq.length (Seq.empty #U8.t) ==>
        embedding' i < embedding' j))
    embedding

let lemma_ordered_subsequence_append_right
  (accepted observed suffix:TCP.bytes)
  : Lemma
      (requires ordered_subsequence accepted observed)
      (ensures ordered_subsequence accepted (Seq.append observed suffix))
=
  let embedding =
    ID.indefinite_description_ghost
      (nat -> nat)
      (fun embedding ->
        (forall (i:nat). i < Seq.length accepted ==>
          embedding i < Seq.length observed /\
          byte_at accepted i == byte_at observed (embedding i)) /\
        (forall (i j:nat).
          i < j /\ j < Seq.length accepted ==>
          embedding i < embedding j)) in
  assert (
    (forall (i:nat). i < Seq.length accepted ==>
      embedding i < Seq.length observed /\
      byte_at accepted i == byte_at observed (embedding i)) /\
    (forall (i j:nat).
      i < j /\ j < Seq.length accepted ==>
      embedding i < embedding j));
  Seq.lemma_len_append observed suffix;
  let index_proof (i:nat { i < Seq.length accepted })
    : Lemma
        (embedding i < Seq.length (Seq.append observed suffix) /\
         byte_at accepted i ==
           byte_at (Seq.append observed suffix) (embedding i))
    =
    Seq.lemma_index_app1 observed suffix (embedding i)
  in
  FStar.Classical.forall_intro
    #(i:nat { i < Seq.length accepted })
    #(fun i ->
      embedding i < Seq.length (Seq.append observed suffix) /\
      byte_at accepted i ==
        byte_at (Seq.append observed suffix) (embedding i))
    index_proof;
  FStar.Classical.exists_intro
    (fun embedding' ->
      (forall (i:nat). i < Seq.length accepted ==>
        embedding' i < Seq.length (Seq.append observed suffix) /\
        byte_at accepted i ==
          byte_at (Seq.append observed suffix) (embedding' i)) /\
      (forall (i j:nat).
        i < j /\ j < Seq.length accepted ==>
        embedding' i < embedding' j))
    embedding

let lemma_ordered_subsequence_append_both
  (accepted observed delta:TCP.bytes)
  : Lemma
      (requires ordered_subsequence accepted observed)
      (ensures
        ordered_subsequence
          (Seq.append accepted delta)
          (Seq.append observed delta))
=
  let old_embedding =
    ID.indefinite_description_ghost
      (nat -> nat)
      (fun embedding ->
        (forall (i:nat). i < Seq.length accepted ==>
          embedding i < Seq.length observed /\
          byte_at accepted i == byte_at observed (embedding i)) /\
        (forall (i j:nat).
          i < j /\ j < Seq.length accepted ==>
          embedding i < embedding j)) in
  assert (
    (forall (i:nat). i < Seq.length accepted ==>
      old_embedding i < Seq.length observed /\
      byte_at accepted i == byte_at observed (old_embedding i)) /\
    (forall (i j:nat).
      i < j /\ j < Seq.length accepted ==>
      old_embedding i < old_embedding j));
  let embedding (i:nat) : nat =
    if i < Seq.length accepted
    then old_embedding i
    else Seq.length observed + (i - Seq.length accepted) in
  Seq.lemma_len_append accepted delta;
  Seq.lemma_len_append observed delta;
  let index_proof
    (i:nat { i < Seq.length (Seq.append accepted delta) })
    : Lemma
        (embedding i < Seq.length (Seq.append observed delta) /\
         byte_at (Seq.append accepted delta) i ==
           byte_at (Seq.append observed delta) (embedding i))
    =
    if i < Seq.length accepted then (
      Seq.lemma_index_app1 accepted delta i;
      Seq.lemma_index_app1 observed delta (old_embedding i)
    ) else (
      Seq.lemma_index_app2 accepted delta i;
      Seq.lemma_index_app2 observed delta (embedding i)
    )
  in
  FStar.Classical.forall_intro
    #(i:nat { i < Seq.length (Seq.append accepted delta) })
    #(fun i ->
      embedding i < Seq.length (Seq.append observed delta) /\
      byte_at (Seq.append accepted delta) i ==
        byte_at (Seq.append observed delta) (embedding i))
    index_proof;
  let order_proof
    (i:nat)
    (j:nat)
    : Lemma
        (requires
          i < j /\ j < Seq.length (Seq.append accepted delta))
        (ensures embedding i < embedding j)
    =
    if j < Seq.length accepted then (
      assert (i < Seq.length accepted);
      assert (old_embedding i < old_embedding j)
    ) else if i < Seq.length accepted then (
      assert (old_embedding i < Seq.length observed);
      assert (Seq.length observed <= embedding j)
    ) else (
      assert (i - Seq.length accepted < j - Seq.length accepted)
    )
  in
  let order_for_i
    (i:nat)
    : Lemma
        (forall (j:nat).
          i < j /\ j < Seq.length (Seq.append accepted delta) ==>
          embedding i < embedding j)
    =
    let order_for_j
      (j:nat)
      : Lemma
          (i < j /\ j < Seq.length (Seq.append accepted delta) ==>
           embedding i < embedding j)
      =
      if i < j /\ j < Seq.length (Seq.append accepted delta)
      then order_proof i j
      else ()
    in
    FStar.Classical.forall_intro
      #(j:nat)
      #(fun j ->
        i < j /\ j < Seq.length (Seq.append accepted delta) ==>
        embedding i < embedding j)
      order_for_j
  in
  FStar.Classical.forall_intro
    #(i:nat)
    #(fun i ->
      forall (j:nat).
        i < j /\ j < Seq.length (Seq.append accepted delta) ==>
        embedding i < embedding j)
    order_for_i;
  FStar.Classical.exists_intro
    (fun embedding' ->
      (forall (i:nat). i < Seq.length (Seq.append accepted delta) ==>
        embedding' i < Seq.length (Seq.append observed delta) /\
        byte_at (Seq.append accepted delta) i ==
          byte_at (Seq.append observed delta) (embedding' i)) /\
      (forall (i j:nat).
        i < j /\ j < Seq.length (Seq.append accepted delta) ==>
        embedding' i < embedding' j))
    embedding

let channel_io_history_matches
  (raw_received raw_sent io_received io_sent:TCP.bytes)
  : prop =
  Seq.equal io_sent raw_sent /\
  ordered_subsequence raw_received io_received

let channel_state_valid
  (#impl #protocol_impl #state #wire_message #local_event #local_output #message:Type0)
  (protocol:CPI.protocol_implementation
    protocol_impl
    state
    wire_message
    local_event
    local_output)
  (protocol_impl_of:impl -> GTot protocol_impl)
  (project:state -> GTot (application_log message))
  (i:impl)
  (raw_received:TCP.bytes)
  (raw_sent:TCP.bytes)
  (app_log:application_log message)
  : prop =
  exists st residual_input.
    WFSM.valid_byte_trace
      (protocol.CPI.pi_system (protocol_impl_of i))
      raw_received
      st
      raw_sent
      residual_input /\
    app_log == project st

let channel_snapshot_ahead
  (#impl #protocol_impl #state #wire_message #local_event #local_output #message:Type0)
  (protocol:CPI.protocol_implementation
    protocol_impl
    state
    wire_message
    local_event
    local_output)
  (protocol_impl_of:impl -> GTot protocol_impl)
  (project:state -> GTot (application_log message))
  (i:impl)
  (old_received:TCP.bytes)
  (old_sent:TCP.bytes)
  (old_log:application_log message)
  (new_received:TCP.bytes)
  (new_sent:TCP.bytes)
  (new_log:application_log message)
  : prop =
  CPI.histories_ahead old_received old_sent new_received new_sent /\
  application_log_extends old_log new_log /\
  exists old_state new_state.
    old_log == project old_state /\
    new_log == project new_state /\
    CPI.state_ahead
      (protocol.CPI.pi_system (protocol_impl_of i))
      old_state
      new_state

let send_transition
  (#message #send_status:Type0)
  (message_of_bytes:TCP.bytes -> GTot message)
  (succeeded:send_status -> GTot bool)
  (status:send_status)
  (payload:TCP.bytes)
  (old_received:TCP.bytes)
  (old_sent:TCP.bytes)
  (old_log:application_log message)
  (new_received:TCP.bytes)
  (new_sent:TCP.bytes)
  (new_log:application_log message)
  : prop =
  CPI.histories_ahead old_received old_sent new_received new_sent /\
  new_log ==
    (if succeeded status
     then append_sent old_log (message_of_bytes payload)
     else old_log)

let receive_transition
  (#message #receive_result:Type0)
  (message_of_bytes:TCP.bytes -> GTot message)
  (succeeded:receive_result -> GTot bool)
  (result_length:receive_result -> GTot SZ.t)
  (result:receive_result)
  (output:TCP.bytes)
  (old_received:TCP.bytes)
  (old_sent:TCP.bytes)
  (old_log:application_log message)
  (new_received:TCP.bytes)
  (new_sent:TCP.bytes)
  (new_log:application_log message)
  : prop =
  CPI.histories_ahead old_received old_sent new_received new_sent /\
  new_log ==
    (if succeeded result
     then
       append_received
         old_log
         (message_of_bytes
           (if SZ.v (result_length result) <= Seq.length output
            then Seq.slice output 0 (SZ.v (result_length result))
            else Seq.empty))
     else old_log)

noextract
class channel_implementation
  (impl:Type0)
  (protocol_impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (message:Type0)
  (send_status:Type0)
  (receive_result:Type0)
  (protocol:CPI.protocol_implementation
    protocol_impl
    state
    wire_message
    local_event
    local_output)
  =
{
  ci_protocol_impl:
    impl -> GTot protocol_impl;

  ci_project:
    state -> GTot (application_log message);

  ci_message_of_bytes:
    TCP.bytes -> GTot message;

  ci_channel_inv:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    application_log message ->
    slprop;

  ci_io_frame:
    impl ->
    TCP.channel ->
    TCP.bytes ->
    TCP.bytes ->
    TCP.bytes ->
    TCP.bytes ->
    application_log message ->
    slprop;

  ci_snapshot:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    application_log message ->
    slprop;

  ci_send_succeeded:
    send_status -> GTot bool;

  ci_receive_succeeded:
    receive_result -> GTot bool;

  ci_receive_length:
    receive_result -> GTot SZ.t;

  ci_open_io_channel:
    i:impl ->
    raw_received:Ghost.erased TCP.bytes ->
    raw_sent:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost TCP.channel emp_inames
        (ci_channel_inv
          i
          (Ghost.reveal raw_received)
          (Ghost.reveal raw_sent)
          (Ghost.reveal app_log))
        (fun ch ->
          exists* io_received io_sent.
            TCP.is_channel ch io_received io_sent **
            ci_io_frame
              i
              ch
              (Ghost.reveal raw_received)
              (Ghost.reveal raw_sent)
              io_received
              io_sent
              (Ghost.reveal app_log) **
            pure (
              channel_io_history_matches
                (Ghost.reveal raw_received)
                (Ghost.reveal raw_sent)
                io_received
                io_sent));

  ci_close_io_channel:
    i:impl ->
    ch:TCP.channel ->
    raw_received:Ghost.erased TCP.bytes ->
    raw_sent:Ghost.erased TCP.bytes ->
    io_received:Ghost.erased TCP.bytes ->
    io_sent:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (TCP.is_channel
          ch
          (Ghost.reveal io_received)
          (Ghost.reveal io_sent) **
         ci_io_frame
          i
          ch
          (Ghost.reveal raw_received)
          (Ghost.reveal raw_sent)
          (Ghost.reveal io_received)
          (Ghost.reveal io_sent)
          (Ghost.reveal app_log) **
         pure (
           channel_io_history_matches
             (Ghost.reveal raw_received)
             (Ghost.reveal raw_sent)
             (Ghost.reveal io_received)
             (Ghost.reveal io_sent)))
        (fun _ ->
          ci_channel_inv
            i
            (Ghost.reveal raw_received)
            (Ghost.reveal raw_sent)
            (Ghost.reveal app_log));

  ci_invariant_valid:
    i:impl ->
    raw_received:Ghost.erased TCP.bytes ->
    raw_sent:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (ci_channel_inv
          i
          (Ghost.reveal raw_received)
          (Ghost.reveal raw_sent)
          (Ghost.reveal app_log))
        (fun _ ->
          ci_channel_inv
            i
            (Ghost.reveal raw_received)
            (Ghost.reveal raw_sent)
            (Ghost.reveal app_log) **
          pure (
            channel_state_valid
              protocol
              ci_protocol_impl
              ci_project
              i
              (Ghost.reveal raw_received)
              (Ghost.reveal raw_sent)
              (Ghost.reveal app_log)));

  ci_take_snapshot:
    i:impl ->
    raw_received:Ghost.erased TCP.bytes ->
    raw_sent:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (ci_channel_inv
          i
          (Ghost.reveal raw_received)
          (Ghost.reveal raw_sent)
          (Ghost.reveal app_log))
        (fun _ ->
          ci_channel_inv
            i
            (Ghost.reveal raw_received)
            (Ghost.reveal raw_sent)
            (Ghost.reveal app_log) **
          ci_snapshot
            i
            (Ghost.reveal raw_received)
            (Ghost.reveal raw_sent)
            (Ghost.reveal app_log));

  ci_recall_snapshot:
    i:impl ->
    old_received:Ghost.erased TCP.bytes ->
    old_sent:Ghost.erased TCP.bytes ->
    old_log:Ghost.erased (application_log message) ->
    new_received:Ghost.erased TCP.bytes ->
    new_sent:Ghost.erased TCP.bytes ->
    new_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (ci_snapshot
          i
          (Ghost.reveal old_received)
          (Ghost.reveal old_sent)
          (Ghost.reveal old_log) **
         ci_channel_inv
          i
          (Ghost.reveal new_received)
          (Ghost.reveal new_sent)
          (Ghost.reveal new_log))
        (fun _ ->
          ci_snapshot
            i
            (Ghost.reveal old_received)
            (Ghost.reveal old_sent)
            (Ghost.reveal old_log) **
          ci_channel_inv
            i
            (Ghost.reveal new_received)
            (Ghost.reveal new_sent)
            (Ghost.reveal new_log) **
          pure (
            channel_snapshot_ahead
              protocol
              ci_protocol_impl
              ci_project
              i
              (Ghost.reveal old_received)
              (Ghost.reveal old_sent)
              (Ghost.reveal old_log)
              (Ghost.reveal new_received)
              (Ghost.reveal new_sent)
              (Ghost.reveal new_log)));

  ci_send:
    i:impl ->
    raw_received0:Ghost.erased TCP.bytes ->
    raw_sent0:Ghost.erased TCP.bytes ->
    app_log0:Ghost.erased (application_log message) ->
    payload:array U8.t ->
    payload_bytes:Ghost.erased TCP.bytes ->
    payload_len:SZ.t ->
      stt send_status
        (ci_channel_inv
           i
           (Ghost.reveal raw_received0)
           (Ghost.reveal raw_sent0)
           (Ghost.reveal app_log0) **
         pts_to payload (Ghost.reveal payload_bytes) **
         pure (Seq.length (Ghost.reveal payload_bytes) == SZ.v payload_len))
        (fun status ->
          exists* raw_received1 raw_sent1 app_log1.
            ci_channel_inv i raw_received1 raw_sent1 app_log1 **
            pts_to payload (Ghost.reveal payload_bytes) **
            pure (
              send_transition
                ci_message_of_bytes
                ci_send_succeeded
                status
                (Ghost.reveal payload_bytes)
                (Ghost.reveal raw_received0)
                (Ghost.reveal raw_sent0)
                (Ghost.reveal app_log0)
                raw_received1
                raw_sent1
                app_log1));

  ci_receive:
    i:impl ->
    raw_received0:Ghost.erased TCP.bytes ->
    raw_sent0:Ghost.erased TCP.bytes ->
    app_log0:Ghost.erased (application_log message) ->
    out:array U8.t ->
    old_output:Ghost.erased TCP.bytes ->
    out_len:SZ.t ->
    local_fuel:SZ.t ->
    network_fuel:SZ.t ->
      stt receive_result
        (ci_channel_inv
           i
           (Ghost.reveal raw_received0)
           (Ghost.reveal raw_sent0)
           (Ghost.reveal app_log0) **
         pts_to out (Ghost.reveal old_output) **
         pure (Seq.length (Ghost.reveal old_output) == SZ.v out_len))
        (fun result ->
          exists* raw_received1 raw_sent1 app_log1 output.
            ci_channel_inv i raw_received1 raw_sent1 app_log1 **
            pts_to out output **
            pure (
              Seq.length output == SZ.v out_len /\
              SZ.v (ci_receive_length result) <= SZ.v out_len /\
              receive_transition
                ci_message_of_bytes
                ci_receive_succeeded
                ci_receive_length
                result
                output
                (Ghost.reveal raw_received0)
                (Ghost.reveal raw_sent0)
                (Ghost.reveal app_log0)
                raw_received1
                raw_sent1
                app_log1));
}
