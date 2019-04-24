module ParsersAux.Binders.Aux

module LP = LowParse.Spec.BoundedInt
module U32 = FStar.UInt32

module L = FStar.List.Tot
module H = Parsers.Handshake
module CH = Parsers.ClientHello
module CHE = Parsers.ClientHelloExtension
module Psks = Parsers.OfferedPsks
module ET = Parsers.ExtensionType
module CHEs = Parsers.ClientHelloExtensions
module HT = Parsers.HandshakeType

val serialize_offeredPsks_eq
  (o: Psks.offeredPsks)
: Lemma
  (LP.serialize Psks.offeredPsks_serializer o == LP.serialize Psks.offeredPsks_identities_serializer o.Psks.identities `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer o.Psks.binders)

val serialize_clientHelloExtension_CHE_pre_shared_key_eq
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: Lemma
  ( LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o ==
    LP.serialize (LP.serialize_bounded_integer 2) (U32.uint_to_t (Psks.offeredPsks_bytesize o)) `Seq.append`
    LP.serialize Psks.offeredPsks_serializer o )

val serialize_list_clientHelloExtension (l: list CHE.clientHelloExtension) : GTot LP.bytes

val serialize_list_clientHelloExtension_eq
  (l: list CHE.clientHelloExtension {
    Cons? l
  })
: Lemma
  (serialize_list_clientHelloExtension l ==
  serialize_list_clientHelloExtension (L.init l) `Seq.append`
  LP.serialize CHE.clientHelloExtension_serializer (L.last l))

val size32_list_clientHelloExtension (l: list CHE.clientHelloExtension { Seq.length (serialize_list_clientHelloExtension l) < 4294967296 }) : Tot (x: U32.t { U32.v x == Seq.length (serialize_list_clientHelloExtension l) })

val clientHelloExtensions_list_bytesize_eq'
  (l: list CHE.clientHelloExtension)
: Lemma
  (CHEs.clientHelloExtensions_list_bytesize l == Seq.length (serialize_list_clientHelloExtension l))

val serialize_clientHelloExtensions_eq
  (l: CHEs.clientHelloExtensions)
: Lemma
  (LP.serialize CHEs.clientHelloExtensions_serializer l ==
   LP.serialize (LP.serialize_bounded_integer 2) (U32.uint_to_t (CHEs.clientHelloExtensions_list_bytesize l)) `Seq.append`
   serialize_list_clientHelloExtension l)

val serialize_clientHello_eq
  (c: CH.clientHello)
: Lemma
  (LP.serialize CH.clientHello_serializer c `Seq.equal` (
   LP.serialize Parsers.ProtocolVersion.protocolVersion_serializer c.CH.version `Seq.append`
   LP.serialize Parsers.Random.random_serializer c.CH.random `Seq.append`
   LP.serialize Parsers.SessionID.sessionID_serializer c.CH.session_id `Seq.append`
   LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c.CH.cipher_suites  `Seq.append`
   LP.serialize Parsers.ClientHello_compression_method.clientHello_compression_method_serializer c.CH.compression_method `Seq.append`
   LP.serialize CHEs.clientHelloExtensions_serializer c.CH.extensions
 ))

val serialize_handshake_m_client_hello_eq
  (c: H.handshake_m_client_hello)
: Lemma
  (LP.serialize H.handshake_m_client_hello_serializer c ==
   LP.serialize (LP.serialize_bounded_integer 3) (U32.uint_to_t (CH.clientHello_bytesize c))
   `Seq.append`
   LP.serialize CH.clientHello_serializer c)

