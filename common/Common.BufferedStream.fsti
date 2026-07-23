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
      drive_outcome output error result
  | DriveYield :
      result ->
      nat ->
      output ->
      drive_outcome output error result
  | DriveReject :
      result ->
      error ->
      drive_outcome output error result
  | DriveBufferFull :
      result ->
      drive_outcome output error result
  | DriveExhausted :
      drive_outcome output error result

let consumed_of (#output #error:Type0) (d:classification output error) : nat =
  match d with
  | NeedMore -> 0
  | Progress k -> k
  | Yield k _ -> k
  | Reject _ -> 0

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
          match outcome with
          | ProcessBufferFull r ->
            exists* st' committed' b'.
              bse_buffer_full e st' (Ghost.reveal received) **
              pure (
                bse_decide r == NeedMore /\
                bse_needs_more
                  (Ghost.reveal st)
                  (BT.pending (Ghost.reveal b)) /\
                process_transition
                  (bse_decide r)
                  (Ghost.reveal committed)
                  committed'
                  (Ghost.reveal b)
                  b' /\
                st' == Ghost.reveal st /\
                BT.free_space (Ghost.reveal b) == 0)
          | Processed r decision ->
            match decision with
            | Reject _ ->
              (exists* st' received'. bse_terminal e st' received') **
              pure (decision == bse_decide r)
            | NeedMore ->
              exists* st' committed' b'.
                bse_read_auth
                  e st' (Ghost.reveal received) committed' b' **
                pure (
                  decision == bse_decide r /\
                  bse_needs_more
                    (Ghost.reveal st)
                    (BT.pending (Ghost.reveal b)) /\
                  process_transition
                    decision
                    (Ghost.reveal committed)
                    committed'
                    (Ghost.reveal b)
                    b' /\
                  st' == Ghost.reveal st /\
                  BT.can_read (Ghost.reveal b))
            | Progress _ ->
              exists* st' committed' b'.
                bse_owns
                  e st' (Ghost.reveal received) committed' b' **
                pure (
                  decision == bse_decide r /\
                  process_transition
                    decision
                    (Ghost.reveal committed)
                    committed'
                    (Ghost.reveal b)
                    b')
            | Yield _ _ ->
              exists* st' committed' b'.
                bse_owns
                  e st' (Ghost.reveal received) committed' b' **
                pure (
                  decision == bse_decide r /\
                  process_transition
                    decision
                    (Ghost.reveal committed)
                    committed'
                    (Ghost.reveal b)
                    b'));

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
  (outcome:drive_outcome output error result)
  : slprop =
  match outcome with
  | DriveExhausted ->
    exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b'
  | DriveBufferFull _ ->
    exists* st' received'. ep.bse_buffer_full e st' received'
  | DriveProgress r consumed ->
    (exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b') **
    pure (ep.bse_decide r == Progress consumed)
  | DriveYield r consumed output ->
    (exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b') **
    pure (ep.bse_decide r == Yield consumed output)
  | DriveReject r error ->
    (exists* st' received'. ep.bse_terminal e st' received') **
    pure (ep.bse_decide r == Reject error)

inline_for_extraction
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
  ensures drive_post ep e outcome
