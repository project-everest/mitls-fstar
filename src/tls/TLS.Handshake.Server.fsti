module TLS.Handshake.Server

open Mem
open TLSConstants
open TLS.Result
open FStar.HyperStack.ST

module CH = Parsers.ClientHello
module E = Extensions
module HSM = HandshakeMessages
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module Nego = Negotiation
module HS = FStar.HyperStack
module H = Hashing.Spec

type hs = TLS.Handshake.Machine.server 

val server_ClientHello2:
  hs: hs ->
  ch1: HSM.ch ->
  hrr: HSM.hrr ->
  ch2: HSM.ch ->
  app_cookie: Bytes.bytes ->
  ST TLS.Handshake.Receive.incoming
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

val server_ClientHello:
  hs: hs ->
  ch: HSM.ch ->
  ST TLS.Handshake.Receive.incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

(*** TLS 1.2 ***)

type cke_t = Parsers.Handshake12_m12_client_key_exchange.handshake12_m12_client_key_exchange

// Received [CKE; CCS]
val server_ClientCCS1:
  hs: hs ->
  cke: cke_t ->
  digestCCS1: H.anyTag ->
  St TLS.Handshake.Receive.incoming

// Received [CF] (full handshake)
val server_ClientFinished:
  hs: hs ->
  cvd: Bytes.bytes ->
  digestCCS: H.anyTag ->
  digestCF: H.anyTag ->
  St TLS.Handshake.Receive.incoming

// Received [CF] (resumption)
val server_ClientFinished2:
  hs: hs ->
  cvd: Bytes.bytes ->
  digestSF: H.anyTag ->
  digestCF: H.anyTag ->
  St TLS.Handshake.Receive.incoming

(*** TLS 1.3 ***)

val server_ServerFinished_13:
  hs: hs ->
  St (result unit)

val server_EOED:
  hs: hs ->
  digestEOED: H.anyTag ->
  St TLS.Handshake.Receive.incoming

val server_Ticket13:
  hs: hs ->
  app_data: Bytes.bytes ->
  St bool

val server_ClientFinished_13: hs ->
  cvd: Bytes.bytes ->
  client_cert: option (HSM.certificate13 & HSM.certificateVerify13) ->
  St TLS.Handshake.Receive.incoming
