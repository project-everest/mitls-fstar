module ParsersAux.Binders.Aux

(*

friend Parsers.OfferedPsks


friend Parsers.ClientHelloExtension_CHE_pre_shared_key
friend Parsers.PreSharedKeyClientExtension


let serialize_offeredPsks_eq
  (o: Psks.offeredPsks)
: Lemma
  (LP.serialize Psks.offeredPsks_serializer o == LP.serialize Psks.offeredPsks_identities_serializer o.Psks.identities `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer o.Psks.binders)
= LPs.serialize_synth_eq _ Psks.synth_offeredPsks Psks.offeredPsks'_serializer Psks.synth_offeredPsks_recip () o;
  LPs.serialize_nondep_then_eq _ Psks.offeredPsks_identities_serializer () _ Psks.offeredPsks_binders_serializer (o.Psks.identities, o.Psks.binders)


let serialize_clientHelloExtension_CHE_pre_shared_key_eq
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: Lemma
  ( LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o ==
    LP.serialize (LPs.serialize_bounded_integer 2) (U32.uint_to_t (Psks.offeredPsks_bytesize o)) `Seq.append`
    LP.serialize Psks.offeredPsks_serializer o )
= LPs.serialize_synth_eq _ CHE.synth_clientHelloExtension_CHE_pre_shared_key CHE.clientHelloExtension_CHE_pre_shared_key'_serializer CHE.synth_clientHelloExtension_CHE_pre_shared_key_recip () o;
  Psks.offeredPsks_bytesize_eq o;
  LP.serialized_length_eq Psks.offeredPsks_serializer o


let serialize_list_clientHelloExtension_eq
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Lemma
  (LP.serialize (LPs.serialize_list _ CHE.clientHelloExtension_serializer) l ==
  LP.serialize (LPs.serialize_list _ CHE.clientHelloExtension_serializer) (L.init l) `Seq.append`
  LP.serialize CHE.clientHelloExtension_serializer (L.last l))
= list_append_init_last l;
  LP.serialize_list_append _ CHE.clientHelloExtension_serializer (L.init l) [L.last l];
  LP.serialize_list_singleton _ CHE.clientHelloExtension_serializer (L.last l)

friend Parsers.ClientHelloExtensions

let serialize_clientHelloExtensions_eq
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Lemma
  (LP.serialize CHEs.clientHelloExtensions_serializer l ==
   LP.serialize (LPs.serialize_bounded_integer 2) (U32.uint_to_t (CHEs.clientHelloExtensions_list_bytesize l)) `Seq.append`
   LP.serialize
   (LPs.serialize_list _ CHE.clientHelloExtension_serializer) l)
= CHEs.clientHelloExtensions_list_bytesize_eq l;
  LP.serialized_list_length_eq_length_serialize_list CHE.clientHelloExtension_serializer l;
  LPs.serialize_synth_eq _ CHEs.synth_clientHelloExtensions CHEs.clientHelloExtensions'_serializer CHEs.synth_clientHelloExtensions_recip () l

friend Parsers.ClientHello

let serialize_clientHello_eq
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
= LP.serialize_synth_eq _ CH.synth_clientHello CH.clientHello'_serializer CH.synth_clientHello_recip () c;
  LP.serialize_nondep_then_eq _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer (c.CH.version, c.CH.random);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer ((c.CH.version, c.CH.random), c.CH.session_id);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer (((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer) () _ CH.clientHello_compression_method_serializer ((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer) () _ CH.clientHello_compression_method_serializer) () _ CHEs.clientHelloExtensions_serializer (((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method), c.CH.extensions)

friend Parsers.Handshake_m_client_hello

let serialize_handshake_m_client_hello_eq
  (c: H.handshake_m_client_hello)
: Lemma
  (LP.serialize H.handshake_m_client_hello_serializer c ==
   LP.serialize (LPs.serialize_bounded_integer 3) (U32.uint_to_t (CH.clientHello_bytesize c))
   `Seq.append`
   LP.serialize CH.clientHello_serializer c)
= CH.clientHello_bytesize_eq c

*)
