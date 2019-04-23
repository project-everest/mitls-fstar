module ParsersAux.Binders

module LP = LowParse.Low.List
module HS = FStar.HyperStack
module U32 = FStar.UInt32

(* ClientHello binders *)

module L = FStar.List.Tot
module H = Parsers.Handshake
module CH = Parsers.ClientHello
module CHE = ParsersAux.ClientHelloExtension

module BY = FStar.Bytes

module LPS = LowParse.SLow.List
module LPs = LowParse.Spec

module B = LowStar.Monotonic.Buffer
module HST = FStar.HyperStack.ST

module Psks = Parsers.OfferedPsks

let offeredPsks_set_binders
  (o: Psks.offeredPsks)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Tot (o' : Psks.offeredPsks {
    o'.Psks.identities == o.Psks.identities /\
    o'.Psks.binders == b' /\
    Psks.offeredPsks_bytesize o' == Psks.offeredPsks_bytesize o
  })
= {
  Psks.identities = o.Psks.identities;
  Psks.binders = b';
}

friend Parsers.OfferedPsks

let serialize_offeredPsks_eq
  (o: Psks.offeredPsks)
: Lemma
  (LP.serialize Psks.offeredPsks_serializer o == LP.serialize Psks.offeredPsks_identities_serializer o.Psks.identities `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer o.Psks.binders)
= LPs.serialize_synth_eq _ Psks.synth_offeredPsks Psks.offeredPsks'_serializer Psks.synth_offeredPsks_recip () o;
  LPs.serialize_nondep_then_eq _ Psks.offeredPsks_identities_serializer () _ Psks.offeredPsks_binders_serializer (o.Psks.identities, o.Psks.binders)

let offeredPsks_binders_offset
  (o: Psks.offeredPsks)
: Tot (x: U32.t {
    let s = LP.serialize Psks.offeredPsks_serializer o in
    U32.v x <= Seq.length s
  })
= serialize_offeredPsks_eq o;
  Psks.offeredPsks_identities_size32 o.Psks.identities

let truncate_offeredPsks
  (o: Psks.offeredPsks)
: GTot LP.bytes
= Seq.slice (LP.serialize Psks.offeredPsks_serializer o) 0 (U32.v (offeredPsks_binders_offset o))

let binders_offset_offeredPsks_set_binders
  (o: Psks.offeredPsks)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Lemma
  (let o' = offeredPsks_set_binders o b' in
  let off = offeredPsks_binders_offset o in
  let tr = truncate_offeredPsks o in
  offeredPsks_binders_offset o' == off /\
  truncate_offeredPsks o' `Seq.equal` tr /\
  LP.serialize Psks.offeredPsks_serializer o' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let o' = offeredPsks_set_binders o b' in
  let off = offeredPsks_binders_offset o in
  serialize_offeredPsks_eq o;
  serialize_offeredPsks_eq o'

friend Parsers.ClientHelloExtension_CHE_pre_shared_key
friend Parsers.PreSharedKeyClientExtension

let serialize_clientHelloExtension_CHE_pre_shared_key_eq
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: Lemma
  ( LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o ==
    LP.serialize (LPs.serialize_bounded_integer 2) (U32.uint_to_t (Psks.offeredPsks_bytesize o)) `Seq.append`
    LP.serialize Psks.offeredPsks_serializer o )
= LPs.serialize_synth_eq _ CHE.synth_clientHelloExtension_CHE_pre_shared_key CHE.clientHelloExtension_CHE_pre_shared_key'_serializer CHE.synth_clientHelloExtension_CHE_pre_shared_key_recip () o;
  Psks.offeredPsks_bytesize_eq o;
  LP.serialized_length_eq Psks.offeredPsks_serializer o

let clientHelloExtension_CHE_pre_shared_key_set_binders
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Tot (o' : CHE.clientHelloExtension_CHE_pre_shared_key {
    o'.Psks.identities == o.Psks.identities /\
    o'.Psks.binders == b' /\
    CHE.clientHelloExtension_CHE_pre_shared_key_bytesize o' == CHE.clientHelloExtension_CHE_pre_shared_key_bytesize o
  })
= offeredPsks_set_binders o b'

let clientHelloExtension_CHE_pre_shared_key_binders_offset
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: Tot (x: U32.t {
    let s = LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o in
    U32.v x <= Seq.length s
  })
= serialize_clientHelloExtension_CHE_pre_shared_key_eq o;
  2ul `U32.add` offeredPsks_binders_offset o

let truncate_clientHelloExtension_CHE_pre_shared_key
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: GTot LP.bytes
= Seq.slice (LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o) 0 (U32.v (clientHelloExtension_CHE_pre_shared_key_binders_offset o))

#push-options "--z3rlimit 16"

let binders_offset_clientHelloExtension_CHE_pre_shared_key_set_binders
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Lemma
  (let o' = clientHelloExtension_CHE_pre_shared_key_set_binders o b' in
  let off = clientHelloExtension_CHE_pre_shared_key_binders_offset o in
  let tr = truncate_clientHelloExtension_CHE_pre_shared_key o in
  clientHelloExtension_CHE_pre_shared_key_binders_offset o' == off /\
  truncate_clientHelloExtension_CHE_pre_shared_key o' `Seq.equal` tr /\
  LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let o' = clientHelloExtension_CHE_pre_shared_key_set_binders o b' in
  let off = clientHelloExtension_CHE_pre_shared_key_binders_offset o in
  serialize_clientHelloExtension_CHE_pre_shared_key_eq o;
  serialize_clientHelloExtension_CHE_pre_shared_key_eq o';
  binders_offset_offeredPsks_set_binders o b'

#pop-options

module ET = Parsers.ExtensionType

let clientHelloExtension_binders_offset
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
: Tot (x: U32.t { U32.v x <= Seq.length (LP.serialize CHE.clientHelloExtension_serializer e) })
= CHE.clientHelloExtension_bytesize_eq e;
  2ul `U32.add` clientHelloExtension_CHE_pre_shared_key_binders_offset (CHE.CHE_pre_shared_key?._0 e)

let truncate_clientHelloExtension
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
: GTot LP.bytes
= Seq.slice (LP.serialize CHE.clientHelloExtension_serializer e) 0 (U32.v (clientHelloExtension_binders_offset e))

let clientHelloExtension_set_binders
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 e).Psks.binders})
: Tot (e' : CHE.clientHelloExtension {
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CHE.clientHelloExtension_bytesize e' == CHE.clientHelloExtension_bytesize e
  })
= CHE.CHE_pre_shared_key (clientHelloExtension_CHE_pre_shared_key_set_binders (CHE.CHE_pre_shared_key?._0 e) b')

#push-options "--z3rlimit 16"

let binders_offset_clientHelloExtension_set_binders
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 e).Psks.binders})
: Lemma
  (let e' = clientHelloExtension_set_binders e b' in
  let off = clientHelloExtension_binders_offset e in
  let tr = truncate_clientHelloExtension e in
  clientHelloExtension_binders_offset e' == off /\
  truncate_clientHelloExtension e' `Seq.equal` tr /\
  LP.serialize CHE.clientHelloExtension_serializer e' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let e' = clientHelloExtension_set_binders e b' in
  let off = clientHelloExtension_binders_offset e in
  CHE.serialize_clientHelloExtension_eq_pre_shared_key e;
  CHE.serialize_clientHelloExtension_eq_pre_shared_key e';
  binders_offset_clientHelloExtension_CHE_pre_shared_key_set_binders (CHE.CHE_pre_shared_key?._0 e) b'

#pop-options

module CHEs = Parsers.ClientHelloExtensions

let rec clientHelloExtensions_list_bytesize_append
  (l1 l2: list CHE.clientHelloExtension)
: Lemma
  (CHEs.clientHelloExtensions_list_bytesize (l1 `L.append` l2) == CHEs.clientHelloExtensions_list_bytesize l1 + CHEs.clientHelloExtensions_list_bytesize l2)
= match l1 with
  | [] -> ()
  | _ :: q -> clientHelloExtensions_list_bytesize_append q l2

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

let list_clientHelloExtension_binders_offset
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l) /\
    CHEs.clientHelloExtensions_list_bytesize l <= 65535
  })
: Tot (x: U32.t { U32.v x <= Seq.length (LP.serialize (LPs.serialize_list _ CHE.clientHelloExtension_serializer) l) })
= serialize_list_clientHelloExtension_eq l;
  CHEs.clientHelloExtensions_list_bytesize_eq l;
  LP.serialized_list_length_eq_length_serialize_list CHE.clientHelloExtension_serializer l;
  LPS.size32_list CHE.clientHelloExtension_size32 () (L.init l) `U32.add` clientHelloExtension_binders_offset (L.last l)

let truncate_list_clientHelloExtension
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l) /\
    CHEs.clientHelloExtensions_list_bytesize l <= 65535
  })
: GTot LP.bytes
= Seq.slice (LP.serialize (LP.serialize_list _ CHE.clientHelloExtension_serializer) l) 0 (U32.v (list_clientHelloExtension_binders_offset l))

let list_clientHelloExtension_set_binders
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders
  })
: Tot (l' : list CHE.clientHelloExtension {
    Cons? l' /\ (
    let e = L.last l in
    let e' = L.last l' in
    L.init l' = L.init l /\
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CHEs.clientHelloExtensions_list_bytesize l' == CHEs.clientHelloExtensions_list_bytesize l
  )})
= list_append_init_last l;
  let lt = L.init l in
  let e = L.last l in
  let e' = clientHelloExtension_set_binders (L.last l) b' in
  let l' = lt `L.append` [e'] in
  list_init_last_def lt e' ;
  clientHelloExtensions_list_bytesize_append lt [e];
  clientHelloExtensions_list_bytesize_append lt [e'];
  l'

#push-options "--z3rlimit 32"

let binders_offset_list_clientHelloExtension_set_binders
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l) /\
    CHEs.clientHelloExtensions_list_bytesize l <= 65535
  })
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders})
: Lemma
  (
  let l' = list_clientHelloExtension_set_binders l b' in
  let off = list_clientHelloExtension_binders_offset l in
  let tr = truncate_list_clientHelloExtension l in
  list_clientHelloExtension_binders_offset l' == off /\
  truncate_list_clientHelloExtension l' `Seq.equal` tr /\
  LP.serialize (LP.serialize_list _ CHE.clientHelloExtension_serializer) l' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let l' = list_clientHelloExtension_set_binders l b' in
  let off = list_clientHelloExtension_binders_offset l in
  serialize_list_clientHelloExtension_eq l;
  serialize_list_clientHelloExtension_eq l';
  binders_offset_clientHelloExtension_set_binders (L.last l) b';
  CHEs.clientHelloExtensions_list_bytesize_eq l;
  LP.serialized_list_length_eq_length_serialize_list CHE.clientHelloExtension_serializer l

#pop-options

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

let clientHelloExtensions_binders_offset
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Tot (x: U32.t { U32.v x <= Seq.length (LP.serialize CHEs.clientHelloExtensions_serializer l) })
= serialize_clientHelloExtensions_eq l;
  2ul `U32.add` list_clientHelloExtension_binders_offset l

let truncate_clientHelloExtensions
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: GTot LP.bytes
= Seq.slice (LP.serialize CHEs.clientHelloExtensions_serializer l) 0 (U32.v (clientHelloExtensions_binders_offset l))

let clientHelloExtensions_set_binders
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders
  })
: Tot (l' : CHEs.clientHelloExtensions {
    Cons? l' /\ (
    let e = L.last l in
    let e' = L.last l' in
    L.init l' = L.init l /\
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CHEs.clientHelloExtensions_bytesize l' == CHEs.clientHelloExtensions_bytesize l
  )})
= list_clientHelloExtension_set_binders l b'

#push-options "--z3rlimit 32"

let binders_offset_clientHelloExtensions_set_binders
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders})
: Lemma
  (let l' = clientHelloExtensions_set_binders l b' in
  let off = clientHelloExtensions_binders_offset l in
  let tr = truncate_clientHelloExtensions l in
  clientHelloExtensions_binders_offset l' == off /\
  truncate_clientHelloExtensions l' `Seq.equal` tr /\
  LP.serialize CHEs.clientHelloExtensions_serializer l' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let l' = clientHelloExtensions_set_binders l b' in
  serialize_clientHelloExtensions_eq l;
  serialize_clientHelloExtensions_eq l';
  binders_offset_list_clientHelloExtension_set_binders l b'

#pop-options

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

#push-options "--z3rlimit 16"

let clientHello_binders_offset
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Tot (x: U32.t { U32.v x <= Seq.length (LP.serialize CH.clientHello_serializer c) })
= serialize_clientHello_eq c;
  Parsers.ProtocolVersion.protocolVersion_size32 c.CH.version `U32.add`
  Parsers.Random.random_size32 c.CH.random `U32.add`
  Parsers.SessionID.sessionID_size32 c.CH.session_id `U32.add`
  Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_size32 c.CH.cipher_suites `U32.add` Parsers.ClientHello_compression_method.clientHello_compression_method_size32 c.CH.compression_method `U32.add`
  clientHelloExtensions_binders_offset c.CH.extensions

#pop-options

let truncate_clientHello
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: GTot LP.bytes
= Seq.slice (LP.serialize CH.clientHello_serializer c) 0 (U32.v (clientHello_binders_offset c))

let clientHello_set_binders
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    let l = c.CH.extensions in
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders
  })
: Tot (c' : CH.clientHello {
    let l' = c'.CH.extensions in
    c'.CH.version == c.CH.version /\
    c'.CH.random == c.CH.random /\
    c'.CH.session_id == c.CH.session_id /\
    c'.CH.cipher_suites == c.CH.cipher_suites /\
    c'.CH.compression_method == c.CH.compression_method /\
    Cons? l' /\ (
    let l = c.CH.extensions in
    let e = L.last l in
    let e' = L.last l' in
    L.init l' = L.init l /\
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CHEs.clientHelloExtensions_bytesize l' == CHEs.clientHelloExtensions_bytesize l
  )})
= {
    CH.version = c.CH.version;
    CH.random = c.CH.random;
    CH.session_id = c.CH.session_id;
    CH.cipher_suites = c.CH.cipher_suites;
    CH.compression_method = c.CH.compression_method;
    CH.extensions = clientHelloExtensions_set_binders c.CH.extensions b'
  }

#push-options "--z3rlimit 32"

let binders_offset_clientHello_set_binders
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    let l = c.CH.extensions in
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders})
: Lemma
  (let c' = clientHello_set_binders c b' in
  let off = clientHello_binders_offset c in
  let tr = truncate_clientHello c in
  clientHello_binders_offset c' == off /\
  truncate_clientHello c' `Seq.equal` tr /\
  LP.serialize CH.clientHello_serializer c' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let c' = clientHello_set_binders c b' in
  serialize_clientHello_eq c;
  serialize_clientHello_eq c';
  binders_offset_clientHelloExtensions_set_binders c.CH.extensions b'

#pop-options

let set_binders m b' =
  let c = H.M_client_hello?._0 m in
  H.M_client_hello (clientHello_set_binders c b')

let set_binders_bytesize m b' = ()

let binders_offset m = admit ()

let binders_offset_set_binder m b' = admit ()

let truncate_clientHello_bytes_correct m = admit ()

let truncate_clientHello_bytes_set_binders m b' = admit ()

#push-options "--z3rlimit 16" 

let truncate_clientHello_bytes_inj_binders_bytesize m1 m2 = admit ()

let binders_pos #rrel #rel sl pos = admit ()
