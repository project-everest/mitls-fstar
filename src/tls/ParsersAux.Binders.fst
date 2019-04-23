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

module CHEs = Parsers.ClientHelloExtensions

let rec clientHelloExtensions_list_bytesize_append
  (l1 l2: list CHE.clientHelloExtension)
: Lemma
  (CHEs.clientHelloExtensions_list_bytesize (l1 `L.append` l2) == CHEs.clientHelloExtensions_list_bytesize l1 + CHEs.clientHelloExtensions_list_bytesize l2)
= match l1 with
  | [] -> ()
  | _ :: q -> clientHelloExtensions_list_bytesize_append q l2

let serialize_list_clientHelloExtension
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
= serialize_list_clientHelloExtension l;
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

#push-options "--z3rlimit 16"

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
  serialize_list_clientHelloExtension l;
  serialize_list_clientHelloExtension l';
  binders_offset_clientHelloExtension_set_binders (L.last l) b';
  serialize_list_clientHelloExtension l;
  CHEs.clientHelloExtensions_list_bytesize_eq l;
  LP.serialized_list_length_eq_length_serialize_list CHE.clientHelloExtension_serializer l

#pop-options

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

let set_binders m b' =
  let c = H.M_client_hello?._0 m in
  H.M_client_hello ({
    CH.version = c.CH.version;
    CH.random = c.CH.random;
    CH.session_id = c.CH.session_id;
    CH.cipher_suites = c.CH.cipher_suites;
    CH.compression_method = c.CH.compression_method;
    CH.extensions = clientHelloExtensions_set_binders c.CH.extensions b'
  })

let set_binders_bytesize m b' = ()

let binders_offset m = admit ()

let binders_offset_set_binder m b' = admit ()

let truncate_clientHello_bytes_correct m = admit ()

let truncate_clientHello_bytes_set_binders m b' = admit ()

let truncate_clientHello_bytes_inj_binders_bytesize m1 m2 = admit ()

let binders_pos #rrel #rel sl pos = admit ()
