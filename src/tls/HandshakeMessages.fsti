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

/// Selected specs shared with ParserAux

unfold let binders                  = Binders.binders
unfold let binders_len              = Binders.binders_len
unfold let ch_bound                 = Binders.ch_bound
unfold let clientHello_with_binders = Binders.clientHello_with_binders
unfold let ch_binders               = Binders.ch_binders 
unfold let set_binders              = Binders.ch_set_binders 
unfold let ch_binders_len           = Binders.ch_binders_len
unfold let canonical_binders        = Binders.build_canonical_binders

/// `tch` is a client hello with dummy binders: our specification of
/// truncated ClientHello messages.

let tch = ch:clientHello_with_binders
  { ch_binders ch == canonical_binders (ch_binders_len ch) } 

/// `truncate`: A specificational version of truncation
/// which replaces the binders of a client hellow with canonical binders
/// of the appropriate length
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

/// 19-09-02 These are the "semantic" server hello contents and HRR
/// payloads.

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

type valid_hrr = sh: hrr {
  CipherSuite.(
    match cipherSuite_of_name (hrr_cipher_suite sh) with 
    | Some (CipherSuite13 _ _) -> True
    | _ -> False) }

let hrr_ha (sh: valid_hrr) = 
  match cipherSuite_of_name (hrr_cipher_suite sh) with 
    | Some (CipherSuite13 _ ha) -> ha

// prior, simpler types, but without a direct wire format: 
// type sh = realServerHello
// type hrr = helloRetryRequest

// module RSH = Parsers.RealServerHello
// module HRR = Parsers.HelloRetryRequest

// let sh_version      (sh: sh) = sh.RSH.version
// let sh_random       (sh: sh) = sh.RSH.random
// let sh_session_id   (sh: sh) = sh.RSH.session_id
// let sh_cipher_suite (sh: sh) = sh.RSH.cipher_suite 
// let sh_extensions   (sh: sh) = sh.RSH.extensions 

// let hrr_version     (sh: hrr) = sh.HRR.version
// let hrr_session_id  (sh: hrr) = sh.HRR.session_id
// let hrr_cipher_suite(sh: hrr) = sh.HRR.cipher_suite
// let hrr_extensions  (sh: hrr) = sh.HRR.extensions 

// /// The function below provides *temporary* conversions to the
// /// simpler, synthetic types.

// let get_hrr (m:serverHello{is_hrr m}) : hrr =
//   let ServerHello_is_hrr_true hrr = m.is_hrr in
//   let open Parsers.HelloRetryRequest in
//   ({
//     version = m.SH.version;
//     session_id = hrr.HRK.session_id;
//     cipher_suite = hrr.HRK.cipher_suite;
//     legacy_compression = hrr.HRK.legacy_compression;
//     extensions = hrr.HRK.extensions;
//   })

// let get_sh (m:serverHello{not (is_hrr m)}) : sh =
//   let ServerHello_is_hrr_false sh = m.is_hrr in
//   let open Parsers.RealServerHello in
//   ({
//     version = m.SH.version;
//     random = sh.tag;
//     session_id = sh.value.SHK.session_id;
//     cipher_suite = sh.value.SHK.cipher_suite;
//     compression_method = sh.value.SHK.compression_method;
//     extensions = sh.value.SHK.extensions;
//   })


// let serverHello_of_sh (m:sh{m.RSH.random <> serverHello_is_hrr_cst}) =
//   SH.({
//     version = m.RSH.version;
//     is_hrr = ServerHello_is_hrr_false Parsers.ServerHello_is_hrr.({
//       tag = m.RSH.random;
//       value = Parsers.SHKind.({
//         session_id = m.RSH.session_id;
// 	cipher_suite = m.RSH.cipher_suite;
// 	compression_method = m.RSH.compression_method;
// 	extensions = m.RSH.extensions;
//       });
//     });
//   })

// let serverHello_of_hrr (m:hrr) =
//   SH.({
//     version = m.HRR.version;
//     is_hrr = ServerHello_is_hrr_true Parsers.HRRKind.({
//       session_id = m.HRR.session_id;
//       cipher_suite = m.HRR.cipher_suite;
//       legacy_compression = m.HRR.legacy_compression;
//       extensions = m.HRR.extensions;
//     })
//   })
