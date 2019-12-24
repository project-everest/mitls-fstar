module TLS.Handshake.Client

/// Implements the transitions of the Client state machine: processing
/// input flights of messages, issuing output messages, and advancing
/// the key schedule.

open Mem
open TLSConstants
open TLSError
// open FStar.HyperStack.ST included in Mem

module B = LowStar.Buffer // not FStar.Bytes
module HS = FStar.HyperStack

// module KS = Old.KeySchedule
module Msg = HandshakeMessages
open TLS.Handshake.Machine

type tag = Hashing.Spec.anyTag

(*** Hello messages ***)

/// C_Init ==> C_wait_ServerHello (initial)
val client_ClientHello:
  hs: client ->
  ST (result unit)
  (requires fun h0 ->
    let Client _ _ r = hs in
    invariant hs h0 /\
    C_init? (HS.sel h0 r))
  (ensures fun h0 r h1 ->
    invariant hs h1)
(*
// precise pre- and post-condition are now defined in the stateful invariant

    let n = HS.sel h0 Nego.(s.nego.state) in
    let t = HSL.transcript h0 s.log in
    let k = HS.sel h1 s.ks.KS.state in
    ( Correct? r ==>
      ( match n with
        | Nego.C_Offer offer -> (
          ( if offer.CH.version = TLS_1p3
            then
             k = KS.(C(C_wait_ServerHello
              (nonce s)
              [] (*TODO: es for 0RTT*)
              (C_wait_ServerHello?.gs (C?.s k)) // TODO
                 // ADL: need an existential for the keyshares (offer only has contains shares)
                 // + check that that the group and CommonDH.pubshare g gx match
              //(Nego.gs_of offer)
             ))
            else k = KS.(C(C12_Full_CH offer.CH.random)) /\
          t = [HSL.Msg (Msg.M_client_hello offer)] ))
        | _ -> False )))
*)

/// C_wait_ServerHello (initial) ==> C_wait_ServerHello (retried)
val client_HelloRetryRequest:
  hs: client ->
  hrr: Msg.hrr ->
  ST Receive.incoming
  (requires fun h0 ->
    let Client _ _ r = hs in
    invariant hs h0 /\
    C_wait_ServerHello? (HS.sel h0 r))
  (ensures fun h0 r h1 ->
    invariant hs h1)

/// C_wait_ServerHello (any) ==> C13_wait_Finished1
val client_ServerHello:
  hs: client ->
  sh: Msg.sh ->
  ST Receive.incoming
  (requires fun h0 ->
    let Client rgn cfg r = hs in
    invariant hs h0 /\
    C_wait_ServerHello? (HS.sel h0 r))
  (ensures fun h0 r h1 ->
    invariant hs h1)

(*** TLS 1.3 ***)

/// Send the client second flight (typically just Finished) and
/// conclude the handshake; this final step of client13_Finished1 may
/// be delayed till the key change after EOED.

// we may instead get cfk from ks
// we may need to add ghost input and output transcripts

val client13_Finished2:
  hs: client ->
  // cr: option Msg.certificateRequest13 ->
  ST (result unit)
  (requires fun h0 ->
    let Client _ _ r = hs in
    invariant hs h0 /\
    (match HS.sel h0 r with
    | C13_complete _ _ _ _ _ _ (Finished_pending _ _ false) -> True
    | _ -> False ))
  (ensures fun h0 r h1 ->
    let Client _ _ r = hs in
    invariant hs h1 /\
    (match HS.sel h0 r with
    | C13_complete _ _ _ _ _ _ (Finished_sent _ _) -> True
    | _ -> False ))

/// C13_wait_Finished1 ==> C13_complete
///
/// process the TLS 1.3 decrypted server flight
/// [EncryptedExtension..Finished1].
///
/// All these messages still require hashing
///
/// If successful, complete the key exchange and send [Finished2].
///
val client13_Finished1:
  hs: client ->
  ee: Msg.encryptedExtensions ->
  ocr: option Msg.certificateRequest13 ->
  ocvv: option (Msg.certificate13 & Msg.certificateVerify13) ->
  svd: Bytes.bytes ->
  ST Receive.incoming
  (requires fun h0 ->
    let Client _ _ r = hs in
    invariant hs h0 /\
    C13_wait_Finished1? (HS.sel h0 r))
  (ensures fun h0 i h1 ->
    invariant hs h1)

/// Post-handshake incoming ticket
/// (stays in C13_complete)

val client13_NewSessionTicket:
  hs: client ->
  nst: Msg.newSessionTicket13 ->
  ST Receive.incoming
  (requires fun h0 ->
    let Client _ _ r = hs in
    invariant hs h0 /\
    C13_complete? (HS.sel h0 r))
  (ensures fun h0 i h1 ->
    invariant hs h1)

/// used for QUIC signalling; underspecified
val early_rejected:
  hs: client ->
  ST bool
  (requires fun h0 ->
    invariant hs h0)
  (ensures fun h0 r h1 -> h0 == h1)

(*** TLS 1.2 ***)

val client12_ServerHelloDone:
  hs: client ->
  cert: Msg.certificate12 ->
  ske_bytes: Bytes.bytes -> // delayed parsing
  cr: option Msg.certificateRequest12 ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)

val client12_R_ServerFinished:
  hs: client ->
  f: Bytes.bytes ->
  digest_nst: tag ->
  digest_sf: tag ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)

val client12_ServerFinished:
  hs: client ->
  fin: Bytes.bytes ->
  digest: tag ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)

val client12_NewSessionTicket:
  hs: client ->
  resume: bool ->
  digest: tag ->
  nst: Msg.newSessionTicket12 ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)
