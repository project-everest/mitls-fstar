module TLS.Handshake.Client

/// Implementing the transitions of the Client state machine:
/// processing incoming flights of messages, issuing messages, and
/// advancing the key schedule.
///
open Mem
open TLSConstants
open TLSError
open FStar.HyperStack.ST

module B = LowStar.Buffer // not FStar.Bytes
module HS = FStar.HyperStack
module HSM = HandshakeMessages
module Nego = Negotiation
module Hash = Hashing.Spec
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule

open TLS.Handshake.Machine

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
    // see precise post-condition in the stateful invariant
    invariant hs h1)
(*
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
          t = [HSL.Msg (HSM.M_client_hello offer)] ))
        | _ -> False )))
*)

/// C_wait_ServerHello (initial) ==> C_wait_ServerHello (retried)
val client_HelloRetryRequest:
  hs: client ->
  hrr: HSM.hrr ->
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
  sh: HSM.sh ->
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
  // cr: option HSM.certificateRequest13 ->
  ST (result unit)
  (requires fun h0 ->
    let Client _ _ r = hs in
    invariant hs h0 /\
    C13_complete? (HS.sel h0 r))
  (ensures fun h0 r h1 ->
    let Client _ _ r = hs in
    invariant hs h1 /\
    C13_complete? (HS.sel h1 r) )

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
  ee: HSM.encryptedExtensions ->
  ocr: option HSM.certificateRequest13 ->
  ocvv: option (HSM.certificate13 & HSM.certificateVerify13) ->
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
  nst: HSM.newSessionTicket13 ->
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
  cert: HSM.certificate12 ->
  ske_bytes: Bytes.bytes -> // delayed parsing
  cr: option HSM.certificateRequest12 ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)

val client12_R_ServerFinished:
  hs: client ->
  f: Bytes.bytes ->
  digest_nst: Hash.anyTag ->
  digest_sf: Hash.anyTag ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)

val client12_ServerFinished:
  hs: client ->
  fin: Bytes.bytes ->
  digest: Hash.anyTag ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)

val client12_NewSessionTicket:
  hs: client ->
  resume: bool ->
  digest: Hash.anyTag ->
  nst: HSM.newSessionTicket12 ->
  ST Receive.incoming
  (requires fun h0 -> invariant hs h0)
  (ensures fun h0 i h1 -> invariant hs h1)
