(* Copyright (C) 2012--2019 Microsoft Research and INRIA *)
(**
Handshake protocol messages
*)
module HandshakeMessages

open FStar.Error
open TLSError
open TLSConstants

module E = Extensions
module B = FStar.Bytes

include Parsers.HandshakeType
include Parsers.HandshakeHeader

include Parsers.Handshake
include Parsers.Handshake12
include Parsers.Handshake13

(* ServerHello also encodes HelloRetryRequest *)
include Parsers.ServerHello
include Parsers.ServerHello_is_hrr
include Parsers.HRRKind
include Parsers.SHKind
include Parsers.RealServerHello
include Parsers.HelloRetryRequest

include Parsers.ClientHello
include Parsers.NewSessionTicket12
include Parsers.NewSessionTicket13
include Parsers.EncryptedExtensions
include Parsers.Certificate12
include Parsers.Certificate13
include Parsers.ServerKeyExchange
include Parsers.CertificateRequest12
include Parsers.CertificateRequest13
include Parsers.CertificateVerify12
include Parsers.CertificateVerify13
include Parsers.ClientKeyExchange
include Parsers.KeyUpdate
include Parsers.KeyExchangeAlgorithm

module Binders = ParsersAux.Binders
(* Parsers are generated automatically, see src/parsers/Parsers.rfc *)

/// Selected specs shared with ParserAux,
/// to deal with truncated binders in ClientHello
/// 

unfold let binders: Type0           = Binders.binders
unfold let binders_len: Type0       = Binders.binders_len

/// Tests whether a ClientHello carries PSKs and binders
unfold let ch_bound                 = Binders.ch_bound

unfold let clientHello_with_binders = Binders.clientHello_with_binders
unfold let ch_binders               = Binders.ch_binders 
unfold let set_binders              = Binders.ch_set_binders 
unfold let ch_binders_len           = Binders.ch_binders_len
unfold let canonical_binders        = Binders.build_canonical_binders

/// `tch` is our type for specifying truncated ClientHello
/// messages: a (full) ClientHello with dummy binders.
let tch = ch:clientHello_with_binders
  { ch_binders ch == canonical_binders (ch_binders_len ch) } 

/// `clear_binders`: a specificational version of truncation that
/// replaces any binders in a ClientHello with canonical binders of
/// the correct length.
let clear_binders (ch:clientHello) = 
  if ch_bound ch then set_binders ch (canonical_binders (ch_binders_len ch)) else ch 


/// Trivial message for convenience; these could also be bound as named types in the RFC.
type finished = b:Bytes.bytes {0 <= Bytes.length b /\ Bytes.length b <= 16777215}
type eoed = unit 


module SH = Parsers.ServerHello

module HRK = Parsers.HRRKind
module SHK = Parsers.SHKind

/// `is_hrr`: a pure function to
/// decide if a server-hello message is a hello-retry-request (hrr)

inline_for_extraction
let is_hrr (m:serverHello): bool =
  ServerHello_is_hrr_true? m.is_hrr

/// These are the "semantic" server hello contents and HRR payloads;
/// we don't define sh13 yet because it depends on Nego.

type ch = clientHello 
type sh  = sh: serverHello {~(is_hrr sh)}
type hrr = sh: serverHello {is_hrr sh}

/// These types are awkward in specifications and high-level code, so
/// we also provide spec-level ad hoc accessors.

// Make these functions opaque? Fuse with Repr.ServerHello? 

private let sh_value (sh: sh) = 
  match sh.SH.is_hrr  with 
  | ServerHello_is_hrr_false v -> v
private let hrr_value (sh: hrr) = 
  match sh.SH.is_hrr  with 
  | ServerHello_is_hrr_true v -> v

let sh_version (sh: sh) = sh.SH.version 
let sh_random       (sh: sh) = (sh_value sh).tag 
let sh_session_id   (sh: sh) = (sh_value sh).value.SHK.session_id
let sh_cipher_suite (sh: sh) = (sh_value sh).value.SHK.cipher_suite 
let sh_extensions   (sh: sh) = (sh_value sh).value.SHK.extensions 

let hrr_version     (sh: hrr) = sh.SH.version 
let hrr_session_id  (sh: hrr) = (hrr_value sh).HRK.session_id
let hrr_cipher_suite(sh: hrr) = (hrr_value sh).HRK.cipher_suite
let hrr_extensions  (sh: hrr) = (hrr_value sh).HRK.extensions 

let mk_hrr v sid cs es : hrr = 
  SH.({
    version = v;
    is_hrr = ServerHello_is_hrr_true HRK.({
      session_id = sid;
      cipher_suite = cs;
      legacy_compression = Parsers.LegacyCompression.NullCompression;
      extensions = es }) })

let is_valid_hrr (sh: serverHello) = 
  is_hrr sh /\
  CipherSuite.(
    match cipherSuite_of_name (hrr_cipher_suite sh) with 
    | Some (CipherSuite13 _ _) -> True
    | _ -> False)
type valid_hrr = sh: hrr { is_valid_hrr sh }
 
let hrr_ha (sh: valid_hrr) = 
  match cipherSuite_of_name (hrr_cipher_suite sh) with 
    | Some (CipherSuite13 _ ha) -> ha

type valid_handshake = m: handshake {
  match m with 
  | M_server_hello sh -> (is_hrr sh ==> is_valid_hrr sh)
  | _ -> True }


let certificate13 = handshake13_m13_certificate

