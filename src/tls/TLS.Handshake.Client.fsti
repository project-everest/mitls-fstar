module TLS.Handshake.Client

open Mem
open TLSConstants
open TLSError
open FStar.HyperStack.ST
open TLS.Handshake.Machine

module B = LowStar.Buffer // not FStar.Bytes
module CH = Parsers.ClientHello
module HSM = HandshakeMessages
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module HSL = HandshakeLog
module Nego = Negotiation
module HS = FStar.HyperStack
module H = Hashing.Spec

(*** Hello messages ***)

let inv (Client rgn cfg st:client) h0 =
  h0 `HS.contains` st /\
  B.loc_disjoint (B.loc_mreference st) (TLS.Handshake.Machine.client_footprint (HS.sel h0 st)) /\
  TLS.Handshake.Machine.client_invariant (HS.sel h0 st) h0

/// C_Init ==> C_wait_ServerHello
val client_ClientHello:
  hs: client ->
  ST (result unit)
  (requires fun h0 ->
    inv hs h0 /\ (
    match hs with
    | Client _ _ r -> C_init? (HS.sel h0 r)))
  (ensures fun h0 r h1 ->
    // see precise post-condition in the stateful invariant
    inv hs h1)

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

val client_HelloRetryRequest:
  hs: client ->
  hrr: HSM.hrr ->
  ST Receive.incoming
  (requires fun h0 ->
    inv hs h0 /\ (
    match hs with
    | Client _ _ r -> C_wait_ServerHello? (HS.sel h0 r)))
  (ensures fun h0 r h1 ->
    inv hs h1)

(* useless?
let client_sel_t (Client rgn cfg r:client) = client_state rgn cfg
let client_sel h c: GTot (client_sel_t c) =
  let Client rgn cfg r = c in
  HS.sel h r
*)

val client_ServerHello:
  hs: client ->
  sh: HSM.sh ->
  ST Receive.incoming
  (requires fun h0 ->
    let Client rgn cfg r = hs in
    inv hs h0 /\
    C_wait_ServerHello? (HS.sel h0 r))
  (ensures fun h0 r h1 ->
    inv hs h1)


(*** TLS 1.2 ***)

val client_ServerHelloDone:
  hs: client ->
  cert: HSM.certificate12 ->
  ske_bytes: Bytes.bytes -> // delayed parsing
  cr: option HSM.certificateRequest12 ->
  ST Receive.incoming
  (requires fun h0 -> inv hs h0)
  (ensures fun h0 i h1 -> inv hs h1)

val client_R_ServerFinished:
  hs: client ->
  f: Bytes.bytes ->
  digest_nst: H.anyTag ->
  digest_sf: H.anyTag ->
  ST Receive.incoming
  (requires fun h0 -> inv hs h0)
  (ensures fun h0 i h1 -> inv hs h1)

val client_ServerFinished:
  hs: client ->
  fin: Bytes.bytes ->
  digest: H.anyTag ->
  ST Receive.incoming
  (requires fun h0 -> inv hs h0)
  (ensures fun h0 i h1 -> inv hs h1)

val client_NewSessionTicket_12:
  hs: client ->
  resume: bool ->
  digest: H.anyTag ->
  nst: HSM.newSessionTicket12 ->
  ST Receive.incoming
  (requires fun h0 -> inv hs h0)
  (ensures fun h0 i h1 -> inv hs h1)

(*** TLS 1.3 ***)

/// process the TLS 1.3 decrypted server flight
/// EncryptedExtension...ServerFinished
///
val c13_Finished1:
  hs: client ->
  ee: HSM.encryptedExtensions ->
  ocr: option HSM.certificateRequest13 ->
  oc: option HSM.certificate13 ->
  ocv: option HSM.certificateVerify13 ->
  svd: Bytes.bytes ->
  digestCert: option H.anyTag ->
  digestCertVerify: H.anyTag ->
  digestServerFinished: H.anyTag ->
  ST Receive.incoming
  (requires fun h0 ->
    let Client _ _ r = hs in
    inv hs h0 /\
    C13_wait_Finished1? (HS.sel h0 r))
  (ensures fun h0 i h1 -> inv hs h1)

// Send ClientFinished flight (hide from API?)
val client_ClientFinished_13:
  hs: client ->
  digest: H.anyTag ->
  cr: option HSM.certificateRequest13 ->
  cfk: (i:HMAC.finishedId & cfk:KS.fink i) ->
  St unit

val c13_NewSessionTicket:
  hs: client ->
  nst: HSM.newSessionTicket13 ->
  ST Receive.incoming
  (requires fun h0 ->
    let Client _ _ r = hs in
    inv hs h0 /\
    C13_complete? (HS.sel h0 r))
  (ensures fun h0 i h1 -> inv hs h1)

// used for QUIC signalling; underspecified
val early_rejected:
  hs: client ->
  ST bool
  (requires fun h0 -> inv hs h0)
  (ensures fun h0 r h1 -> h0 == h1)
