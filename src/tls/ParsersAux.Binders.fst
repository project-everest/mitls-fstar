module ParsersAux.Binders

module LP = LowParse.Low.Base
module HS = FStar.HyperStack
module U32 = FStar.UInt32

(* ClientHello binders *)

module L = FStar.List.Tot
module H = Parsers.Handshake
module CH = Parsers.ClientHello
module CHE = Parsers.ClientHelloExtension

module BY = FStar.Bytes

module LPS = LowParse.SLow.Base

module B = LowStar.Monotonic.Buffer
module HST = FStar.HyperStack.ST

module Psks = Parsers.OfferedPsks

let clientHelloExtension_CHE_pre_shared_key_set_binders
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Tot (o' : CHE.clientHelloExtension_CHE_pre_shared_key {
    o'.Psks.identities == o.Psks.identities /\
    o'.Psks.binders == b' /\
    CHE.clientHelloExtension_CHE_pre_shared_key_bytesize o' == CHE.clientHelloExtension_CHE_pre_shared_key_bytesize o
  })
= {
  Psks.identities = o.Psks.identities;
  Psks.binders = b';
}

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

module CHEs = Parsers.ClientHelloExtensions

let rec clientHelloExtensions_list_bytesize_append
  (l1 l2: list CHE.clientHelloExtension)
: Lemma
  (CHEs.clientHelloExtensions_list_bytesize (l1 `L.append` l2) == CHEs.clientHelloExtensions_list_bytesize l1 + CHEs.clientHelloExtensions_list_bytesize l2)
= match l1 with
  | [] -> ()
  | _ :: q -> clientHelloExtensions_list_bytesize_append q l2

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
= list_append_init_last l;
  let lt = L.init l in
  let e = L.last l in
  let e' = clientHelloExtension_set_binders (L.last l) b' in
  let l' = lt `L.append` [e'] in
  list_init_last_def lt e' ;
  clientHelloExtensions_list_bytesize_append lt [e];
  clientHelloExtensions_list_bytesize_append lt [e'];
  l'
  
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
