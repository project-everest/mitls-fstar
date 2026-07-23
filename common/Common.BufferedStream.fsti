module Common.BufferedStream

#lang-pulse

open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module TCP = Common.TCP
module BT  = Common.BufferedTCP

type classification (output:Type0) (error:Type0) =
  | NeedMore : classification output error
  | Progress : consumed:nat -> classification output error
  | Yield    : consumed:nat -> out:output -> classification output error
  | Reject   : err:error -> classification output error

type process_outcome (output error result:Type0) =
  | Processed :
      result ->
      classification output error ->
      process_outcome output error result
  | ProcessBufferFull :
      result ->
      process_outcome output error result

type drive_outcome (output error result:Type0) =
  | DriveProgress :
      result ->
      nat ->
      FStar.SizeT.t ->
      drive_outcome output error result
  | DriveYield :
      result ->
      nat ->
      output ->
      FStar.SizeT.t ->
      drive_outcome output error result
  | DriveReject :
      result ->
      error ->
      FStar.SizeT.t ->
      drive_outcome output error result
  | DriveBufferFull :
      result ->
      FStar.SizeT.t ->
      drive_outcome output error result
  | DriveExhausted :
      drive_outcome output error result

let consumed_of (#output #error:Type0) (d:classification output error) : nat =
  match d with
  | NeedMore -> 0
  | Progress k -> k
  | Yield k _ -> k
  | Reject _ -> 0

let drive_fuel_left
  (#output #error #result:Type0)
  (outcome:drive_outcome output error result)
  : FStar.SizeT.t =
  match outcome with
  | DriveProgress _ _ fuel_left
  | DriveYield _ _ _ fuel_left
  | DriveReject _ _ fuel_left
  | DriveBufferFull _ fuel_left ->
    fuel_left
  | DriveExhausted ->
    0sz

let process_transition
  (#output #error:Type0)
  (d:classification output error)
  (committed committed':TCP.bytes)
  (b b':BT.phys_buffer)
  : prop =
  match d with
  | NeedMore ->
    Seq.equal committed' committed /\ b' == b
  | Reject _ ->
    True
  | Progress k ->
    0 < k /\ k <= Seq.length (BT.pending b) /\
    Seq.equal committed' (BT.committed_after committed b k) /\
    b' == BT.compact b k
  | Yield k _ ->
    0 < k /\ k <= Seq.length (BT.pending b) /\
    Seq.equal committed' (BT.committed_after committed b k) /\
    b' == BT.compact b k

let read_delivers
  (received received':TCP.bytes)
  (b b':BT.phys_buffer)
  : prop =
  BT.buffer_wf b' /\
  BT.capacity b' == BT.capacity b /\
  (exists (chunk:TCP.bytes).
     BT.chunk_fits b chunk /\
     Seq.equal (BT.pending b') (Seq.append (BT.pending b) chunk) /\
     Seq.equal received' (Seq.append received chunk))

noextract
let process_post
  (#endpoint #state #output #error #result:Type0)
  (decide:result -> GTot (classification output error))
  (needs_more:state -> TCP.bytes -> prop)
  (result_valid:endpoint -> state -> result -> state -> prop)
  (owns:endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop)
  (terminal:endpoint -> state -> TCP.bytes -> slprop)
  (buffer_full:endpoint -> state -> TCP.bytes -> slprop)
  (read_auth:endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop)
  (e:endpoint)
  (st:state)
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  (outcome:process_outcome output error result)
  : slprop =
  match outcome with
  | ProcessBufferFull r ->
    exists* st' committed' b'.
      buffer_full e st' received **
      pure (
        decide r == NeedMore /\
        result_valid e st r st' /\
        needs_more st (BT.pending b) /\
        process_transition
          (decide r)
          committed
          committed'
          b
          b' /\
        st' == st /\
        BT.free_space b == 0)
  | Processed r decision ->
    match decision with
    | Reject _ ->
      exists* st' received'.
        terminal e st' received' **
        pure (
          decision == decide r /\
          result_valid e st r st')
    | NeedMore ->
      exists* st' committed' b'.
        read_auth e st' received committed' b' **
        pure (
          decision == decide r /\
          result_valid e st r st' /\
          needs_more st (BT.pending b) /\
          process_transition
            decision
            committed
            committed'
            b
            b' /\
          st' == st /\
          BT.can_read b)
    | Progress _ ->
      exists* st' committed' b'.
        owns e st' received committed' b' **
        pure (
          decision == decide r /\
          result_valid e st r st' /\
          process_transition
            decision
            committed
            committed'
            b
            b')
    | Yield _ _ ->
      exists* st' committed' b'.
        owns e st' received committed' b' **
        pure (
          decision == decide r /\
          result_valid e st r st' /\
          process_transition
            decision
            committed
            committed'
            b
            b')

noextract
class buffered_stream_endpoint
  (endpoint:Type0)
  (state:Type0)
  (output:Type0)
  (error:Type0)
  (result:Type0)
  =
{
  bse_decide:
    result -> GTot (classification output error);

  bse_needs_more:
    state -> TCP.bytes -> prop;

  bse_result_valid:
    endpoint -> before:state -> result -> after:state -> prop;

  bse_owns:
    endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop;

  bse_terminal:
    endpoint -> state -> TCP.bytes -> slprop;

  bse_buffer_full:
    endpoint -> state -> TCP.bytes -> slprop;

  bse_read_auth:
    endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop;

  bse_owns_wf:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt_ghost unit emp_inames
        (bse_owns
          e
          (Ghost.reveal st)
          (Ghost.reveal received)
          (Ghost.reveal committed)
          (Ghost.reveal b))
        (fun _ ->
          bse_owns
            e
            (Ghost.reveal st)
            (Ghost.reveal received)
            (Ghost.reveal committed)
            (Ghost.reveal b) **
          pure (
            BT.buffer_wf (Ghost.reveal b) /\
            BT.received_split
              (Ghost.reveal received)
              (Ghost.reveal committed)
              (Ghost.reveal b)));

  bse_process:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt (process_outcome output error result)
        (bse_owns
          e
          (Ghost.reveal st)
          (Ghost.reveal received)
          (Ghost.reveal committed)
          (Ghost.reveal b))
        (fun outcome ->
          process_post
            bse_decide
            bse_needs_more
            bse_result_valid
            bse_owns
            bse_terminal
            bse_buffer_full
            bse_read_auth
            e
            (Ghost.reveal st)
            (Ghost.reveal received)
            (Ghost.reveal committed)
            (Ghost.reveal b)
            outcome);

  bse_read:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt unit
        (bse_read_auth
           e
           (Ghost.reveal st)
           (Ghost.reveal received)
           (Ghost.reveal committed)
           (Ghost.reveal b) **
         pure (
           BT.buffer_wf (Ghost.reveal b) /\
           BT.can_read (Ghost.reveal b) /\
           bse_needs_more
             (Ghost.reveal st)
             (BT.pending (Ghost.reveal b))))
        (fun _ ->
          exists* received' b'.
            bse_owns
              e
              (Ghost.reveal st)
              received'
              (Ghost.reveal committed)
              b' **
            pure (
              read_delivers
                (Ghost.reveal received)
                received'
                (Ghost.reveal b)
                b'));
}

noextract
let drive_post
  (#endpoint #state #output #error #result:Type0)
  (ep:buffered_stream_endpoint endpoint state output error result)
  (e:endpoint)
  (initial:state)
  (outcome:drive_outcome output error result)
  : slprop =
  match outcome with
  | DriveExhausted ->
    exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b' **
      pure (st' == initial)
  | DriveBufferFull r _ ->
    exists* st' received'.
      ep.bse_buffer_full e st' received' **
      pure (ep.bse_result_valid e initial r st')
  | DriveProgress r consumed _ ->
    exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b' **
      pure (
        ep.bse_decide r == Progress consumed /\
        ep.bse_result_valid e initial r st')
  | DriveYield r consumed output _ ->
    exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b' **
      pure (
        ep.bse_decide r == Yield consumed output /\
        ep.bse_result_valid e initial r st')
  | DriveReject r error _ ->
    exists* st' received'.
      ep.bse_terminal e st' received' **
      pure (
        ep.bse_decide r == Reject error /\
        ep.bse_result_valid e initial r st')

noextract
fn drive_until_conclusive
  (#endpoint #state #output #error #result:Type0)
  (ep:buffered_stream_endpoint endpoint state output error result)
  (e:endpoint)
  (st:Ghost.erased state)
  (received:Ghost.erased TCP.bytes)
  (committed:Ghost.erased TCP.bytes)
  (b:Ghost.erased BT.phys_buffer)
  (fuel:FStar.SizeT.t)
  requires
    ep.bse_owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal b)
  returns outcome:drive_outcome output error result
  ensures
    drive_post ep e (Ghost.reveal st) outcome **
    pure (
      FStar.SizeT.v (drive_fuel_left outcome) <=
        FStar.SizeT.v fuel)
