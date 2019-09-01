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

(* Parsers are generated automatically, see src/parsers/Parsers.rfc *)

// trivial message for convenience; these could also be bound as named types in the RFC.
type finished = b:Bytes.bytes {0 <= Bytes.length b /\ Bytes.length b <= 16777215}
type eoed = unit 

type sh = realServerHello
type hrr = helloRetryRequest

/// TODO: this is the same as HSL.Transcript.is_hrr; decide which one to keep.
/// In fact, I claim that we should redefine `hrr` above as (sh: serverHello { is_hrr sh })
/// and so get rid of the conversion functions below.
let is_hrr (m:serverHello) =
  match m.is_hrr with
  | ServerHello_is_hrr_false _ -> false
  | ServerHello_is_hrr_true _ -> true

module SH = Parsers.ServerHello
module HRK = Parsers.HRRKind
module SHK = Parsers.SHKind

let get_hrr (m:serverHello{is_hrr m}) : hrr =
  let ServerHello_is_hrr_true hrr = m.is_hrr in
  let open Parsers.HelloRetryRequest in
  ({
    version = m.SH.version;
    session_id = hrr.HRK.session_id;
    cipher_suite = hrr.HRK.cipher_suite;
    legacy_compression = hrr.HRK.legacy_compression;
    extensions = hrr.HRK.extensions;
  })

let get_sh (m:serverHello{not (is_hrr m)}) : sh =
  let ServerHello_is_hrr_false sh = m.is_hrr in
  let open Parsers.RealServerHello in
  ({
    version = m.SH.version;
    random = sh.tag;
    session_id = sh.value.SHK.session_id;
    cipher_suite = sh.value.SHK.cipher_suite;
    compression_method = sh.value.SHK.compression_method;
    extensions = sh.value.SHK.extensions;
  })

module RSH = Parsers.RealServerHello
module HRR = Parsers.HelloRetryRequest

let serverHello_of_sh (m:sh{m.RSH.random <> serverHello_is_hrr_cst}) =
  SH.({
    version = m.RSH.version;
    is_hrr = ServerHello_is_hrr_false Parsers.ServerHello_is_hrr.({
      tag = m.RSH.random;
      value = Parsers.SHKind.({
        session_id = m.RSH.session_id;
	cipher_suite = m.RSH.cipher_suite;
	compression_method = m.RSH.compression_method;
	extensions = m.RSH.extensions;
      });
    });
  })

let serverHello_of_hrr (m:hrr) =
  SH.({
    version = m.HRR.version;
    is_hrr = ServerHello_is_hrr_true Parsers.HRRKind.({
      session_id = m.HRR.session_id;
      cipher_suite = m.HRR.cipher_suite;
      legacy_compression = m.HRR.legacy_compression;
      extensions = m.HRR.extensions;
    })
  })
