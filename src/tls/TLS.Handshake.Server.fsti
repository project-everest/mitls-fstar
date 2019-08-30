module TLS.Handshake.Server

open Mem
open TLSConstants
open TLSError
open FStar.HyperStack.ST
open TLS.Handshake.State

module B = FStar.Bytes
module CH = Parsers.ClientHello
module E = Extensions
module HSM = HandshakeMessages
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module HSL = HandshakeLog
module Nego = Negotiation
module HS = FStar.HyperStack
module H = Hashing.Spec

val server_ClientHello2:
  hs: hs ->
  ch1: HSM.clientHello ->
  hrr: HSM.hrr ->
  ch2: HSM.clientHello ->
  app_cookie: B.bytes ->
  ST incoming
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
  
val server_ClientHello:
  hs: hs ->
  ch: HSM.clientHello ->
  ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

(*** TLS 1.2 ***)

type cke_t = Parsers.Handshake12_m12_client_key_exchange.handshake12_m12_client_key_exchange

// Received [CKE; CCS]
val server_ClientCCS1:
  hs: hs ->
  cke: cke_t ->
  digestCCS1: H.anyTag ->
  St incoming

// Received [CF] (full handshake)
val server_ClientFinished:
  hs: hs ->
  cvd: B.bytes ->
  digestCCS: H.anyTag ->
  digestCF: H.anyTag ->
  St incoming

// Received [CF] (resumption)
val server_ClientFinished2:
  hs: hs ->
  cvd: B.bytes ->
  digestSF: H.anyTag ->
  digestCF: H.anyTag ->
  St incoming

(*** TLS 1.3 ***)

val server_ServerFinished_13:
  hs: hs ->
  St (result unit)

val server_EOED:
  hs: hs ->
  digestEOED: H.anyTag ->
  St incoming

val server_Ticket13:
  hs: hs ->
  app_data: B.bytes ->
  St unit

val server_ClientFinished_13: hs ->
  cvd: B.bytes ->
  digest_SF: H.anyTag ->
  digest_CF: H.anyTag ->
  client_cert: option (HSM.certificate13 * HSM.certificateVerify13 * H.anyTag) ->
  St incoming
