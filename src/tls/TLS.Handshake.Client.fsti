module TLS.Handshake.Client

open Mem
open TLSConstants
open TLSError
open FStar.HyperStack.ST
open TLS.Handshake.State

module B = FStar.Bytes
module CH = Parsers.ClientHello
module HSM = HandshakeMessages
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module HSL = HandshakeLog
module Nego = Negotiation
module HS = FStar.HyperStack
module H = Hashing.Spec

val client_ClientHello:
  s:hs ->
  ST (result unit)
  (requires fun h0 ->
    let n = HS.sel h0 Nego.(s.nego.state) in
    let t = HSL.transcript h0 s.log in
    let k = HS.sel h0 s.ks.KS.state in
    match n with
    | Nego.C_Init nonce -> k = KS.(C (C_Init nonce)) /\ t = []
    | _ -> False )
  (ensures fun h0 r h1 ->
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

val client_HelloRetryRequest:
  hs: hs ->
  hrr: HSM.hrr ->
  St incoming

val client_ServerHello:
  hs: hs ->
  sh: HSM.sh ->
  St incoming

(*** TLS 1.2 ***)

val client_ServerHelloDone:
  hs ->
  cert: HSM.certificate12 ->
  ske_bytes: B.bytes -> // delayed parsing
  cr: option HSM.certificateRequest12 ->
  ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

val client_R_ServerFinished:
  hs: hs ->
  f: B.bytes ->
  digest_nst: H.anyTag ->
  digest_sf: H.anyTag ->
  St incoming

val client_ServerFinished:
  hs: hs ->
  fin: B.bytes ->
  digest: H.anyTag ->
  St incoming

val client_NewSessionTicket_12:
  hs: hs ->
  resume: bool ->
  digest: H.anyTag ->
  nst: HSM.newSessionTicket12 ->
  St incoming

(*** TLS 1.3 ***)

// Send ClientFinished flight (hide from API?)
val client_ClientFinished_13:
  hs: hs ->
  digest: H.anyTag ->
  cr: option HSM.certificateRequest13 ->
  cfk: (i:HMAC.finishedId & cfk:KS.fink i) ->
  St unit

(* receive EncryptedExtension...ServerFinished for TLS 1.3, roughly mirroring client_ServerHelloDone *)
val client_ServerFinished_13:
  s: hs ->
  ee: HSM.encryptedExtensions ->
  ocr: option HSM.certificateRequest13 ->
  oc: option HSM.certificate13 ->
  ocv: option HSM.certificateVerify13 ->
  svd: B.bytes ->
  digestCert: option H.anyTag ->
  digestCertVerify: H.anyTag ->
  digestServerFinished: H.anyTag ->
  St incoming

val client_NewSessionTicket_13:
  hs: hs ->
  nst: HSM.newSessionTicket13 ->
  St incoming
