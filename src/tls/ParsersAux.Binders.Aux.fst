module ParsersAux.Binders.Aux

module LP = LowParse.Low
module LS = LowParse.SLow.List
module U32 = FStar.UInt32

module L = FStar.List.Tot
module H = Parsers.Handshake
module CH = Parsers.ClientHello
module CHE = Parsers.ClientHelloExtension
module Psks = Parsers.OfferedPsks
module ET = Parsers.ExtensionType
module CHEs = Parsers.ClientHelloExtensions
module HT = Parsers.HandshakeType

friend Parsers.OfferedPsks
friend Parsers.ClientHelloExtension_CHE_pre_shared_key
friend Parsers.PreSharedKeyClientExtension
friend Parsers.ClientHelloExtensions
friend Parsers.ClientHello
friend Parsers.Handshake_m_client_hello

let serialize_offeredPsks_eq
  o
= LP.serialize_synth_eq _ Psks.synth_offeredPsks Psks.offeredPsks'_serializer Psks.synth_offeredPsks_recip () o;
  LP.serialize_nondep_then_eq Psks.offeredPsks_identities_serializer Psks.offeredPsks_binders_serializer (o.Psks.identities, o.Psks.binders)

let serialize_clientHelloExtension_CHE_pre_shared_key_eq
  o
= LP.serialize_synth_eq _ CHE.synth_clientHelloExtension_CHE_pre_shared_key CHE.clientHelloExtension_CHE_pre_shared_key'_serializer CHE.synth_clientHelloExtension_CHE_pre_shared_key_recip () o;
  Psks.offeredPsks_bytesize_eq o

let serialize_list_clientHelloExtension
  l
= LP.serialize (LP.serialize_list _ CHE.clientHelloExtension_serializer) l

let serialize_list_clientHelloExtension_eq
  l
= L.append_init_last l;
  LP.serialize_list_append _ CHE.clientHelloExtension_serializer (L.init l) [L.last l];
  LP.serialize_list_singleton _ CHE.clientHelloExtension_serializer (L.last l)

let serialize_list_clientHelloExtension_inj_prefix
  l1 l2 b1 b2
= LP.serialize_list_eq_parser_fail CHE.clientHelloExtension_serializer l1 l2 b1 b2

let size32_list_clientHelloExtension
  l
= LS.size32_list CHE.clientHelloExtension_size32 () l

module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack

let list_clientHelloExtension_last_pos
  #rrel #rel sl pos pos' gl
= LP.list_last_pos CHE.clientHelloExtension_serializer CHE.clientHelloExtension_jumper sl pos pos' gl

let clientHelloExtensions_list_bytesize_eq'
  l
= CHEs.clientHelloExtensions_list_bytesize_eq l

let serialize_clientHelloExtensions_eq
  l
= CHEs.clientHelloExtensions_list_bytesize_eq l;
  LP.serialized_list_length_eq_length_serialize_list CHE.clientHelloExtension_serializer l;
  LP.serialize_synth_eq _ CHEs.synth_clientHelloExtensions CHEs.clientHelloExtensions'_serializer CHEs.synth_clientHelloExtensions_recip () l

let serialize_clientHello_eq
  c
= LP.serialize_synth_eq _ CH.synth_clientHello CH.clientHello'_serializer CH.synth_clientHello_recip () c;
  LP.serialize_nondep_then_eq Parsers.ProtocolVersion.protocolVersion_serializer Parsers.Random.random_serializer (c.CH.version, c.CH.random);
  LP.serialize_nondep_then_eq (LP.serialize_nondep_then Parsers.ProtocolVersion.protocolVersion_serializer Parsers.Random.random_serializer) Parsers.SessionID.sessionID_serializer ((c.CH.version, c.CH.random), c.CH.session_id);
  LP.serialize_nondep_then_eq (LP.serialize_nondep_then (LP.serialize_nondep_then Parsers.ProtocolVersion.protocolVersion_serializer Parsers.Random.random_serializer) Parsers.SessionID.sessionID_serializer) CH.clientHello_cipher_suites_serializer (((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites);
  LP.serialize_nondep_then_eq (LP.serialize_nondep_then (LP.serialize_nondep_then (LP.serialize_nondep_then Parsers.ProtocolVersion.protocolVersion_serializer Parsers.Random.random_serializer) Parsers.SessionID.sessionID_serializer) CH.clientHello_cipher_suites_serializer) CH.clientHello_compression_method_serializer ((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method);
  LP.serialize_nondep_then_eq (LP.serialize_nondep_then (LP.serialize_nondep_then (LP.serialize_nondep_then (LP.serialize_nondep_then Parsers.ProtocolVersion.protocolVersion_serializer Parsers.Random.random_serializer) Parsers.SessionID.sessionID_serializer) CH.clientHello_cipher_suites_serializer) CH.clientHello_compression_method_serializer) CHEs.clientHelloExtensions_serializer (((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method), c.CH.extensions)

let serialize_handshake_m_client_hello_eq
  c
= CH.clientHello_bytesize_eq c
