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
