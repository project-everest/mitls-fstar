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
  LP.serialize_nondep_then_eq _ Psks.offeredPsks_identities_serializer () _ Psks.offeredPsks_binders_serializer (o.Psks.identities, o.Psks.binders)

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

#push-options "--z3rlimit 16"

let rec serialize_list_eq_parser_fail
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (s: LP.serializer p { k.LP.parser_kind_subkind == Some LP.ParserStrong /\ k.LP.parser_kind_low > 0 })
  (l1 l2: list t)
  (b1 b2: LP.bytes)
: Lemma
  (requires (
    LP.serialize (LP.serialize_list _ s) l1 `Seq.append` b1 == LP.serialize (LP.serialize_list _ s) l2 `Seq.append` b2 /\
    LP.parse p b1 == None /\
    LP.parse p b2 == None
  ))
  (ensures (l1 == l2 /\ b1 == b2))
  (decreases (L.length l1))
= LP.serialize_list_nil _ s;
  assert (b1 `Seq.equal` (Seq.append Seq.empty b1));
  assert (b2 `Seq.equal` (Seq.append Seq.empty b2));
  if L.length l2 < L.length l1
  then serialize_list_eq_parser_fail s l2 l1 b2 b1
  else match l1, l2 with
  | [], [] -> ()
  | x1 :: l1', x2 :: l2' ->
    LP.serialize_list_cons _ s x1 l1' ;
    LP.serialize_list_cons _ s x2 l2' ;
    Seq.append_assoc (LP.serialize s x1) (LP.serialize (LP.serialize_list _ s) l1') b1;
    Seq.append_assoc (LP.serialize s x2) (LP.serialize (LP.serialize_list _ s) l2') b2;
    LP.serialize_strong_prefix s x1 x2 (LP.serialize (LP.serialize_list _ s) l1' `Seq.append` b1) (LP.serialize (LP.serialize_list _ s) l2' `Seq.append` b2);
    serialize_list_eq_parser_fail s l1' l2' b1 b2
  | [], x2 :: l2' ->
    LP.serialize_list_cons _ s x2 l2' ;
    LP.parse_strong_prefix p (LP.serialize s x2) b1

#pop-options

let size32_list_clientHelloExtension
  l
= LS.size32_list CHE.clientHelloExtension_size32 () l

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
  LP.serialize_nondep_then_eq _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer (c.CH.version, c.CH.random);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer ((c.CH.version, c.CH.random), c.CH.session_id);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer (((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer) () _ CH.clientHello_compression_method_serializer ((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer) () _ CH.clientHello_compression_method_serializer) () _ CHEs.clientHelloExtensions_serializer (((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method), c.CH.extensions)

let serialize_handshake_m_client_hello_eq
  c
= CH.clientHello_bytesize_eq c
