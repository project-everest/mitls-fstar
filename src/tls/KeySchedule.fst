module KeySchedule
(*the top level key schedule module, it should not expose secrets to Handshake *)

(* the goal is to keep ephemerals like eph_s and eph_c as currently defined 
   in Handshake local *)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties
open FStar.Set  

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSExtensions
open TLSInfo
open Range
open HandshakeMessages
open StatefulLHAE
open HKDF

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap

// *** PSK ***

// The constraints for PSK indexes are:
//  - must be public (as psk index appears in hsId, msId and derived keys)
//  - must support application-provided PSK as well as RMS-based PSK
//  - must support dynamic compromise; we want to prove KI of 1RT keys in PSK_DHE
//    even for leaked PSK (but not PSK-based auth obivously)
// Implementation style:
//  - pskid is the TLS PSK identifier, an internal index to the PSK table
//  - for tickets, the encrypted serialized state is the PSK identifier
//  - we store in the table the PSK context and compromise status
let pskid = b:bytes{length b < 65536}

// TODO: add certificates and other authPSK info
let psk_context = {
  allow_early_data: bool;      // New draft 13 flag
  allow_dhe_resumption: bool;  // New draft 13 flag
  allow_psk_resumption: bool;  // New draft 13 flag
  time_created: int;
  early_ae: aeadAlg;
  early_hash: hashAlg;
  resumption_context: option b:bytes{length b <= 64}; // None for application PSK
}

// We rule out all PSK that do not have at least one non-null byte
// thus avoiding possible confusion with non-PSK for all possible hash algs
type psk = b:bytes{exists i.{:pattern index b i} index b i <> 0z}

// TODO store the leaked ref in a better region?
abstract let psk (i:pskid) =
  psk * ctx:psk_context * leaked:(rref tls_tables_region bool)

// injectivity predicate on map from PSK identities to secret key
let psk_injective (m:MM.map' pskid psk) =
  forall i1 i2.{:pattern (MM.sel m i1); (MM.sel m i2)}
       equalBytes i1 i2 <==> (match MM.sel m i1, MM.sel m i2 with
                  | Some (psk1,_,_), Some (psk2,_,_) -> equalBytes psk1 psk2
                  | _ -> True)

// Monotonic table mapping injectively PSK identities to keys and context
let psk_table : MM.t tls_tables_region pskid psk psk_injective =
  MM.alloc #TLSConstants.tls_tables_region #pskid #psk #psk_injective

let registered_psk (i:pskid) = is_Some (MM.sel psk_table i)

let get_psk_context (i:pskid{registered_psk i}) =
  let (_, c, _) = Some.v (MM.sel psk_table i) in c

let leaked_psk (i:pskid{registered_psk i}) =
  let (_, _, l) = Some.v (MM.sel psk_table i) in !l

let leak (i:pskid{registered_psk i}) =
  let (v, _, l) = Somve.v (MM.sel psk_table i) in
  l := true; v

// Generates a fresh PSK identity
let fresh_psk_id () : St i:pskid{~ registered_psk i} =
  let rec subgen () =
     let id = CoreCrypto.random 8 in
     match MM.sel psk_table id with
     | None -> id
     | Some _ -> subgen () in
   subgen ()

// "Application PSK" generator (enforces empty session context)
// Usual caveat of random producing pairwise distinct keys (TODO)
let gen_psk i:pskid{~ registered_psk i} ctx:psk_context{is_None ctx.session_context} : psk i =
  let psk = CoreCrypto.random 32 in
  let leaked = ralloc tls_tables_region false in
  let add : psk i = (psk, ctx, leaked) in
  assume (forall j.{:pattern MM.sel psk_table j}
                   match MM.sel psk_table j with | None -> True
                   | Some (p,_,_) -> equalBytes p psk <==> equalBytes i j); // TODO
  MM.extend psk_table i add;
  add

// Lifted psk_injective lemma
let registered_psk_injective #i1:pskid #i2:pskid ((p1, _, _):psk i1) ((p2, _, _):psk i2)
  : Lemma (requires (registered_psk i1) /\ (registered_psk i2))
    (ensures (equalBytes p1 p2) <==> (equalBytes i1 i2))
  = admit ()

// Agile "0" hash
private let zH h =
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  CoreCrypto.hash h zeroes

// Resumption context from PSK
let pskid_rc i:pskid{registered_psk i} =
  let c = get_psk_context i in
  match c.resumption_context with
  | Some b -> CoreCrypto.hash (c.early_hash) b
  | None -> zH h

// miTLS 0.9:
// ==========
// PRF (type pms) -> TLSInfo (type id) -> KEF (extract pms)
//                     \ StatefulLHAE (coerce id) / 
// TODO rework old 1.2 types
type ms = bytes
type pms = bytes 

// Early secrets are indexed by registered PSK identifiers
type esId = i:pskid{registered_psk i}
abstract type es (i:esId) =
  b:bytes{let c = get_psk_context i in length b = CoreCrypto.hashSize c.early_hash}

// Index of handshake secret
// Split between DHE, PSK_DHE, and pure PSK
type hsId =
  | HSID_PSK: i:esId -> hsId
  | HSID_PSK_DHE: i:esId -> initiator:CommonDH.share -> responder:CommonDH.share -> hsId
  | HSID_DHE: h:hashAlg -> initiator:CommonDH.share -> responder:CommonDH.share -> hsId

let hsId_hash = function
  | HSID_PSK i | HSID_PSK_DHE i _ _ -> let c = get_psk_context i in c.early_hash
  | HSID_DHE h _ _ -> h

// Get the hashed resumption context
let hsId_rc = function
  | HSID_DHE h _ _ -> zH h
  | HSID_PSK i | HSID_PSK_DHE i _ _ -> pskid_rc i

abstract type hs (i:hsId) =
  b:bytes{length b = CoreCrypto.hashSize (hsId_hash i)}

// Can be extended with e.g. MSID_staticDH hsid share
type msId13 =
  | MSID: hsId:hsId -> msId13

let msId_rc = function
  | MSID hsId -> hsId_rc hsId

let msId_hash = function
  | MSID hsId -> hsId_hash hsId

// TLS 1.3 master secret (abstract)
abstract type ms13 (i:msId13) =
  b:bytes{length b = CoreCrpyot.hashSize (msId_hash i)}

// Sum of the 3 secret index types
type secretId =
  | EarlySecret: i:aeId -> secretId
  | HandshakeSecret: i:hsId -> secretId
  | MasterSecret: i:msId13 -> secretId

let secretId_hash = function
  | EarlySecret i -> esId_hash i
  | HandshakeSecret i -> hsId_hash i
  | MasterSecret i -> msId_hash i

// Index of derived secrets
type derivedID = {
  underlying_secret: secretId;
  handshake_log: list HandshakeMessage.hs_msg;
  label: string;
}

// RMS index
type rmsId = i:derivedId {
  is_MasterSecret i.underlying_secret
  /\ i.label = "resumption master secret"}

abstract type rms (i:rmsId) =
  b:bytes{length b = CoreCrpyot.hashSize (secretId_hash i.underlying_secret)}

// Exporter Master Secret (public)
type exportId = i:derivedId {
  is_MasterSecret i.underlying_secret
  /\ i.label = "exporter master secret"}

type exportMS (i:exportId) =
  b:bytes{length b = CoreCrpyot.hashSize (secretId_hash i.underlying_secret)}

// Index of 1.3 record keys
type keyId13 = {
  derived_secret: derivedId;
  aeadAlg: aeadAlg; // => keySize, ivSize
  label: string;
  writer: role;
}

// Index of Finished keys
type macId13 = {
  derived_secret: derivedId;
  role: role;
}

// TODO this is superseeded by StAE.state i
// but I'm waiting for it to be tester to switch over
// TODO use the newer index types
type recordInstance =
| StAEInstance: #id:StreamAE.id -> StreamAE.reader id -> StreamAE.writer id -> recordInstance
| StLHAEInstance: #id:StatefulLHAE.id -> StatefulLHAE.reader id -> StatefulLHAE.writer id -> recordInstance

// Placeholder until new indexes are propagated outside KS
let badid ae h writer : TLSInfo.id = {
    msId = msId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p3;
    aeAlg = (AEAD ae h);
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_groups = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None
    };
    writer = writer
  }

// Note from old miTLS (in TLSInfo.fst)
// type id = {
//  msId   : msId;            // the index of the master secret used for key derivation
//  kdfAlg : kdfAlg_t;          // the KDF algorithm used for key derivation
//  pv     : protocolVersion; // should be part of aeAlg
//  aeAlg  : aeAlg;           // the authenticated-encryption algorithms
//  csrConn: csRands;         // the client-server random of the connection
//  ext: negotiatedExtensions;// the extensions negotiated for the current session
//  writer : role             // the role of the writer
//  }

// abstract type resumption_secret = b:bytes{}
//type resumption_secret = b:bytes{}

//type exporter_secret = b:bytes{}

// Agility parameters, extend as needed
// may be moved to TLSInfo for joint idealization with Handshake
type ks_alpha12 = pv:protocolVersion * cs:cipherSuite * ems:bool
type ks_alpha13 = ae:aeadAlg * h:CoreCrypto.hash_alg

type ks_client_state =
| C_Init: cr:random -> ks_client_state
| C_12_Resume_CH: cr:random -> si:sessionInfo -> msId:TLSInfo.msId -> ms:ms -> ks_client_state
| C_12_Full_CH: cr:random -> ks_client_state
| C_12_wait_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.pmsId -> pms:pms -> ks_client_state
| C_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_client_state
| C_13_wait_CH: cr:random -> i:pskid{registered_psk i} -> gs:list (namedGroup * CommonDH.key) -> ks_client_state
| C_13_wait_SH: cr:random -> es:option (| i:esId & es i & cfk:bytes |) -> gs:list (namedGroup * CommonDH.key) -> ks_client_state
| C_13_wait_SF: alpha:ks_alpha13 -> cfk:bytes -> sfk:bytes -> (| i:hsId & hs:hs i |) -> ks_client_state
| C_13_wait_CF: alpha:ks_alpha13 -> cfk:bytes -> late_cfk:bytes -> ms_derived:bytes -> (| i:msId13 & ms:ms13 i |) -> ks_client_state
| C_13_postHS: alpha:ks_alpha13 -> late_cfk:bytes -> i:msId13 -> ats:bytes -> rms:bytes -> ks_client_state
| C_Done

type ks_server_state =
| S_Init: sr:random -> ks_server_state
| S_12_wait_CKE_DH: csr:csRands -> alpha:ks_alpha12 -> our_share:CommonDH.key -> ks_server_state
| S_12_wait_CKE_RSA: csr: csRands -> alpha:ks_alpha12 -> ks_server_state
| S_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_server_state
| S_13_wait_SH: alpha:ks_alpha13 -> es:option (| i:pskid{registered_psk i} & es i|) -> ks_server_state
| S_13_wait_SF: alpha:ks_alpha13 -> cfk:bytes -> sfk:bytes -> (| i:hsId & hs:hs i |) -> ks_server_state
| S_13_wait_CF: alpha:ks_alpha13 -> cfk:bytes -> late_cfk:bytes -> ms_derived:bytes -> (| i:msId13 & ms:ms13 i|) -> ks_server_state
| S_13_postHS: alpha:ks_alpha13 -> late_cfk:bytes -> i:msId13 -> ats:bytes -> rm
s:bytes -> ks_server_state
| S_Done

// Reflecting state separation from HS
type ks_state =
| C: s:ks_client_state -> ks_state
| S: s:ks_server_state -> ks_state

// KeySchedule instances
type ks =
| KS: #region:rid -> state:rref region ks_state -> ks

<<<<<<< 003d4b9505f1cf83d5e4c27a0165bc13ffea3198
type recordInstance =
| StAEInstance: #id:StreamAE.id -> StreamAE.reader id -> StreamAE.writer id -> recordInstance
| StLHAEInstance: #id:StatefulLHAE.id -> StatefulLHAE.reader id -> StatefulLHAE.writer id -> recordInstance

// TODO replace constants (16, 12) with aeadAlg-derived values
private let expand_13 (h:CoreCrypto.hash_alg) (secret:bytes) (phase:string) (context:bytes) =
  let cekb = HKDF.hkdf_expand_label h
             secret (phase ^ ", client write key") context 16 in
  let civb = HKDF.hkdf_expand_label h
             secret (phase ^ ", client write iv") context 12 in
  let sekb = HKDF.hkdf_expand_label h
             secret (phase ^ ", server write key") context 16 in
  let sivb = HKDF.hkdf_expand_label h
             secret (phase ^ ", server write iv") context 12 in
=======
// Extract keys and IVs from a derived 1.3 secret
private let keygen_13 h secret phase ae =
  let kS = CoreCrypto.aeadKeySize ae in
  let iS = CoreCrypto.aeadRealIVSize ae in
  let f x y = HSCrypto.hkdf_expand_label h secret (phase ^ x) empty_bytes y in
  let cekb = f ", client write key" kS in
  let civb = f ", client write iv" iS in
  let sekb = f ", server write key" kS in
  let sivb = f ", server write iv" iS in
>>>>>>> Checkpoint to progress on new index types (also includes 0-RTT implentation)
  (cekb,civb,sekb,sivb)

// Extract finished keys
private let finished_13 h secret =
  let hL = CoreCrypto.hashSize h in
  let cfk = HSCrypto.hkdf_expand_label h ms "client finished" empty_bytes hL in
  let sfk = HSCrypto.hkdf_expand_label h ms "server finished" empty_bytes hL in
  cfk, sfk

val ks_client_random: ks:ks -> ST random
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_Init (C.s kss))
  (ensures fun h0 _ h1 -> h0 = h1)
let ks_client_random ks =
  let KS #rid st = ks in
  let C (C_Init cr) = !st in cr

val ks_server_random: ks:ks -> ST random
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_Init (S.s kss))
  (ensures fun h0 _ h1 -> h0 = h1)
let ks_server_random ks =
  let KS #rid st = ks in
  let S (S_Init sr) = !st in sr

// Create a fresh key schedule instance
// We expect this to be called when the Handshake instance is created
val create: #rid:rid -> role -> ST (ks * random)
  (requires fun h -> rid<>root)
  (ensures fun h0 (r,_) h1 ->
    let KS #ks_region state = r in
    fresh_region ks_region h0 h1
    /\ extends ks_region rid
    /\ modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref state} h0 h1)

let create #rid r =
  ST.recall_region rid;
  let ks_region = new_region rid in 
  let nonce = Nonce.mkHelloRandom r ks_region in
  let istate = match r with
    | Client -> C (C_Init nonce)
    | Server -> S (S_Init nonce) in
  (KS #ks_region (ralloc ks_region istate)), nonce

val ks_client_13_1rtt_init: ks:ks -> list (g:namedGroup{is_SEC g \/ is_FFDHE g}) -> ST (list (namedGroup * bytes))
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_Init (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_1rtt_init ks groups =
  let KS #rid st = ks in
  let C (C_Init cr) = !st in
  let kg x = x, (match x with
    | SEC ecg -> CommonDH.keygen (CommonDH.ECDH ecg)
    | FFDHE g -> CommonDH.keygen (CommonDH.FFDH (DHGroup.Named g))) in
  let gs = List.Tot.map kg groups in
  st := C (C_13_wait_SH cr None gs);
  let pub (x,y) = x, CommonDH.serialize_raw y in
  List.Tot.map pub gs

val ks_client_13_0rtt_init: ks:ks -> i:pskid{registered_psk i} -> list (g:namedGroup{is_SEC g \/ is_FFDHE g}) -> ST (list (namedGroup * bytes))
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_Init (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_0rtt_init ks pskid groups =
  let KS #rid st = ks in
  let C (C_Init cr) = !st in
  let kg x = x, (match x with
    | SEC ecg -> CommonDH.keygen (CommonDH.ECDH ecg)
    | FFDHE g -> CommonDH.keygen (CommonDH.FFDH (DHGroup.Named g))) in
  let gs = List.Tot.map kg groups in
  st := C (C_13_wait_CH cr pskid gs);
  let pub (x,y) = x, CommonDH.serialize_raw y in
  List.Tot.map pub gs

// Derive the early keys from the early secret
let ks_client_13_0rtt_ch ks log_hash
  : ST (recordInstance * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_Init (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1) =
  let KS #rid st = ks in
  let C (C_13_wait_CH cr pskid gs) = !st in
  let (psk, ctx, _) = Some.v (MM.sel psk_table pskid) in
  let h, ae = c.early_hash, c.early_ae in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  let es : es pskid = HSCrypto.hkdf_extract h zeroes psk in
  let sh_rctx = log_hash @| (pskid_rc pskid) in
  let es_derived = HSCrypto.hkdf_expand_label h hs "early traffic secret" sh_rctx hL in

  // Expand all keys from the derived early secret
  let (ck,civ, _, _) = keygen_13 h es_derived "early traffic key expansion" ae in
  let (ck',civ', _, _) = keygen_13 h es_derived "early application data key expansion" ae in
  let (cfk, _) = finished_13 h es_derived in

  let id = badid ae h Client in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StreamAE.coerce HyperHeap.root id ckv civ in
  let r = StreamAE.genReader HyperHeap.root rw in
  let early_hs = StAEInstance r w

  let id = badid ae h Client in
  let ckv: StreamAE.key id = ck' in
  let civ: StreamAE.iv id  = civ' in
  let rw = StreamAE.coerce HyperHeap.root id ckv civ in
  let r = StreamAE.genReader HyperHeap.root rw in
  let early_d = StAEInstance r w

  let (ck,civ, _, _) = keygen_13 h es_derived "early application data key expansion" ae in
  let (cfk, _) = finished_13 h es_derived in
 
  st := C (C_13_wait_SH cr (Some (pskid, es, cfk)) gs);
  (early_hs, early_d)

val ks_client_13_0rtt_finished: ks:ks -> log_hash:bytes -> ST (cvd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_wait_SH (C.s kss))
  (ensures fun h0 r h1 -> h0 = h1)

// Compute 0-RTT finished
let ks_client_13_0rtt_finished ks log_hash =
  let KS #rid st = ks in
  let C (C_13_wait_SH cr (Some (pskid, es, cfk)) gs) = !st in
  let (psk, ctx, _) = Some.v (MM.sel psk_table pskid) in
  let h = c.early_hash in
  CoreCrypto.hmac h cfk (log_hash |@ (pskid_rc pskid))

// Called before sending client hello
// (the external style of resumption may become internal to protect ms abstraction)
val ks_client_init_12: ks:ks -> ST (option sessionInfo)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_Init (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

// TODO resumption support
let ks_client_init_12 ks =
  let KS #rid st = ks in
  let C (C_Init cr) = !st in
  let osi, ns = None, (C (C_12_Full_CH cr)) in
//    match cfg.resuming with
//    | None -> None, (KS_C_12_Full_CH cr)
//    | Some shard ->
//      (match DB.lookup shard with TODO
//      | Some (si, msId, ms) -> (Some si), (KS_C_12_Resume_CH cr si msId ms)
//      | None -> None, (KS_C_12_Full_CH cr)) in
  (KS.state ks) := ns;
  osi

val ks_server_12_init_dh: ks:ks -> cr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> group:namedGroup -> ST CommonDH.key
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_Init (S.s kss)
    /\ is_CipherSuite cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_init_dh ks cr pv cs ems group =
  let KS #region st = ks in
  let S (S_Init sr) = !st in
  let group = (match group with 
      	       | SEC c -> CommonDH.ECDH c
	       | FFDHE f -> CommonDH.FFDH (DHGroup.Named f)) in
  let CipherSuite kex sa ae = cs in
  let our_share = CommonDH.keygen group in
  let csr = cr @| sr in
  st := S (S_12_wait_CKE_DH csr (pv, cs, ems) our_share);
  our_share

private let s13_dh gn gxb =
  let gx = match gn with
    | SEC ec ->
      let Some gx = CommonDH.parse (CommonDH.ECP (ECGroup.params_of_group ec)) gxb in gx
    | FFDHE ff ->
      let Some gx =  CommonDH.parse (CommonDH.FFP (DHGroup.params_of_group (DHGroup.Named ff))) gxb in gxi
  in let gy, gxy = CommonDH.dh_responder gx in
  (gy, 

val ks_server_13_0rtt_init: ks:ks -> cr:random -> i:pskid{registered_psk i} -> cs:cipherSuite -> gn:namedGroup -> gxb:bytes -> log_hash:bytes -> ST (recordInstance * recordInstance * our_share:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_Init (S.s kss)
    /\ is_CipherSuite cs /\ (let CipherSuite kex _ _ = cs in
       (kex = Kex_PSK_DHE \/ kex = Kex_PSK_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

// let ks_server13_0rtt_init ks cr pskid cs gn gxb log_hash = () // TODO

val ks_server_13_1rtt_init: ks:ks -> cr:random -> cs:cipherSuite -> gn:namedGroup -> gxb:bytes -> ST (our_share:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_Init (S.s kss)
    /\ is_CipherSuite cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_13_1rtt_init ks cr cs gn gxb =
  let KS #region st = ks in
  let S (S_Init sr) = !st in
  let CipherSuite _ _ (AEAD ae h) = cs in
  let our_share, gxy = s13_dh gn gxb in
  let hsId = HSID h 
  let hs = HSCrypto.hkdf_extract h zeroes gxy in
  st := S (S_13_wait_SH (ae, h) msId xES);
  CommonDH.serialize_raw our_share

val ks_server_13_sh: ks:ks -> log_hash:bytes -> ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_13_wait_SH (S.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_13_get_htk ks log_hash =
  let KS #region st = ks in
  let S (S_13_wait_SH (ae, h) es gxy) = !st in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in

  // Early secret: must derive zero here as hash is not known before
  let es, rctx =
    match es with
    // Application-PSK may have an empty resumption contexct
    | Some (i, es) ->
      let ctx = get_psk_context i in
      es, (match ctx.resumption_context with
      | None -> zeroes | Some rc -> rc)
    | None -> HSCrypto.hkdf_extract h zeroes zeroes, zH h
  in

  // Handshake secret
  let is = CommonDH.share_of_key gx in
  let rs = CommonDH.share_of_key gy in
  let hsId = match es with
    | None -> HSID h is rs
    | Some (pskid, _) -> HSID_PSK_DHE pskid is rs in

  let hs : hs hsId = HSCrypto.hkdf_extract h es gxy in
  let (ck,civ,sk,siv) = expand_13 h xES "handshake key expansion" log_hash in
  let id = badid ae h Server in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let w = StreamAE.coerce HyperHeap.root id skv siv in
  let rw = StreamAE.coerce HyperHeap.root id ckv civ in
  let r = StreamAE.genReader HyperHeap.root rw in
  st := S (S_13_wait_SF (ae, h) cfk sfk (hsId, hs));
  StAEInstance r w

// log is the raw HS log, used for EMS derivation
val ks_server_12_cke_dh: ks:ks -> peer_share:bytes -> log:bytes -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_12_wait_CKE_DH (S.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_cke_dh ks gxb log =
  let KS #region st = ks in
  let S (S_12_wait_CKE_DH csr alpha our_share) = !st in
  let dhp = CommonDH.key_params our_share in
  let Some gx = CommonDH.parse dhp gxb in
  let (pv, cs, ems) = alpha in
  let pmsb = CommonDH.dh_initiator our_share gx in

  let pms = PMS.DHPMS(dhp, our_share, gx, PMS.ConcreteDHPMS(pmsb)) in
  let pmsId = TLSInfo.SomePmsId(pms) in
  let kef = kefAlg pv cs ems in
  let msId, ms =
    if ems then
      let ms = TLSPRF.prf_hashed (pv,cs) pmsb (utf8 "extended master secret") log 48 in
      let msId = ExtendedMS pmsId log kef in
      (msId, ms)
    else
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS pmsId csr kef in
      (msId, ms) in
   st := S (S_12_has_MS csr alpha msId ms)

// Called after receiving server hello; server accepts resumption proposal
// This function only checks the agility paramaters compared to the resumed sessionInfo
// and returns to the handshake whether the resumption is permissible
val ks_client_12_resume: ks:ks -> random -> pv:protocolVersion -> cs:cipherSuite -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_12_Resume_CH (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_resume ks sr pv cs =
  let KS #region st = ks in
  let C (C_12_Resume_CH cr si msId ms) = !st in
  let csr = cr @| sr in
  let ems = si.extensions.ne_extended_ms in
  st := C (C_12_has_MS csr (pv, cs, ems) msId ms)

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguemtns
//   2. they use different return types
//   3. they are called at different locations

val ks_client_13_sh: ks:ks -> cs:cipherSuite -> gy:(namedGroup * bytes) -> accept_early_data:bool -> log_hash:bytes -> ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_wait_SH (C.s kss) /\ 
    // Ensure consistency of ae/h if 0-RTT data is accepted
    (let C_13_wait_SH _ ei _ = C.s kss in
     match ei with | None -> True | Some id, _, _ ->
       let CipherSuite _ _ (AEAD ae h) = cs in
       let ctxt = get_psk_context id in
       accept_early_data ==> ctxt.early_ae = ae /\ ctxt.early_hash = h))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

// ServerHello log breakpoint (client)
let ks_client_13_sh ks cs (gs, gyb) accept_ed log_hash =
  let KS #region st = ks in
  let C (C_13_wait_SH cr early_info gc) = !st in
  let Some (_, gx) = List.Tot.find (fun (gc,_) -> gc = gs) gc in
  let Some gy = CommonDH.parse (CommonDH.key_params gx) gyb in
  let gxy = CommonDH.dh_initiator gx gy in
  let CipherSuite _ _ (AEAD ae h) = cs in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in

  // Early secret: must derive zero here as hash is not known before
  let es =
    match early_info, accept_ed with
    | Some (_, es, _), true -> es
    | _ -> HSCrypto.hkdf_extract h zeroes zeroes in

  // Handshake secret
  let is = CommonDH.share_of_key gx in
  let rs = CommonDH.share_of_key gy in
  let hsId = match early_info with
    | None -> HSID h is rs
    | Some (pskid, _, _) -> HSID_PSK_DHE pskid is rs in
  let hs : hs hsId = HSCrypto.hkdf_extract h es gxy in

  // Derived handshake secret
  let sh_rctx = log_hash @| (hsId_rc hsId) in
  let hs_derived = HSCrypto.hkdf_expand_label h hs "handshake traffic secret" sh_rctx hL in
  let (ck,civ,sk,siv) = keygen_13 h hs_derived "handshake key expansion" ae in
  let (cfk, sfk) = finished_13 h hs_derived in

  let id = badid ae h Client in
  assume (~ (authId id));
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let w = StreamAE.coerce HyperHeap.root id ckv civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let rw = StreamAE.coerce HyperHeap.root id skv siv in
  let r = StreamAE.genReader HyperHeap.root rw in
  st := C (C_13_wait_SF (ae, h) cfk sfk (hsId, hs));
  StAEInstance r w

// Old KS: ms, cfk, sfk is up to CertificateVerify
// application keys use atk with context up to server finished
val ks_client_13_server_finished: ks:ks -> log_hash:bytes -> ST (svd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_wait_SF (C.s kss))
  (ensures fun h0 r h1 -> h0 = h1)

let ks_client_13_server_finished ks log_hash =
  let KS #region st = ks in
  let C (C_13_wait_SF alpha cfk sfk (hsId, hs)) = !st in
  let (ae, h) = alpha in
  CoreCrypto.hmac h sfk (log_hash @| (hsId_rc hsId))

val ks_client_13_client_finished: ks:ks -> log_hash:bytes -> ST (cvd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_wait_CF (C.s kss))
  (ensures fun h0 r h1 -> h0 = h1)

let ks_client_13_client_finished ks log_hash =
  let KS #region st = ks in
  let C (C_13_wait_CF (_, h) cfk _ _ (msId, _)) = !st in
  CoreCrypto.hmac h cfk (log_hash @| (msId_rc msId))

val ks_server_13_server_finished: ks:ks -> log_hash:bytes -> ST (svd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_13_1RTT_wait_HTK (S.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_13_server_finished ks log_hash =
  let KS #region st = ks in
  let S (S_13_1RTT_wait_HTK (ae, h) msId xES) = !st in
  let mSS = HKDF.hkdf_expand_label h xES "expanded static secret" log_hash 32 in
  let mES = HKDF.hkdf_expand_label h xES "expanded ephemeral secret" log_hash 32 in
  let ms = HKDF.hkdf_extract h mSS mES in

  let cfk = HKDF.hkdf_expand_label h ms "client finished" empty_bytes 32 in
  let sfk = HKDF.hkdf_expand_label h ms "server finished" empty_bytes 32 in
  let ts0 = HKDF.hkdf_expand_label h ms "traffic secret" log_hash 32 in
  let svd = CoreCrypto.hmac h sfk log_hash in
  st := S (S_13_TS (ae, h) cfk ts0);
  svd

val ks_server_13_client_finished: ks:ks -> log_hash:bytes -> ST (cvd:bytes * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_13_TS (S.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_13_client_finished ks log_hash =
  let KS #region st = ks in
  let S (S_13_TS alpha cfk ts0) = !st in
  let (ae, h) = alpha in
  let cvd = CoreCrypto.hmac h cfk log_hash in
  let (ck,civ,sk,siv) = expand_13 h ts0 "application data key expansion" log_hash in
  // TODO need to completely scrap and redo 1.3 index types
  let id = {
    msId = noMsId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p3;
    aeAlg = (AEAD ae h);
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_groups = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None
    };
    writer = Server
  } in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let w = StreamAE.coerce HyperHeap.root id skv siv in
  let rw = StreamAE.coerce HyperHeap.root id ckv civ in
  let r = StreamAE.genReader HyperHeap.root rw in
  st := S (S_Done);
  (cvd, StAEInstance r w)

val ks_client_13_sf: ks:ks -> log_hash:bytes -> ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_wait_SF (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_sf ks log_hash =
  let KS #region st = ks in
  let C (C_13_wait_SF alpha cfk _ (hsId, hs)) = !st in
  let (ae, h) = alpha in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in

  let msId = MSID hsId in
  let ms : ms13 msId = HSCrypto.hkdf_extract h hs zeroes in

  let sh_rctx = log_hash @| (hsID_rc hsId) in
  let ms_derived = HSCrypto.hkdf_expand_label h ms "application traffic secret" sh_rctx hL in
  let (ck,civ,sk,siv) = keygen_13 h ms_derived "application data key expansion" in
  let (late_cfk, _) = finished_13 h ms_derived in

  let id = badid ae h Client in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let w = StreamAE.coerce HyperHeap.root id ckv civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let rw = StreamAE.coerce HyperHeap.root id skv siv in
  let r = StreamAE.genReader HyperHeap.root rw in
  st := C (C_13_wait_CF alpha cfk late_cfk ms_derived (msId, ms));
  StAEInstance r w

val ks_client_13_cf: ks:ks -> log_hash:bytes -> ST (| i:msId & exportMS i |)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_wait_CF (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_cf ks log_hash =
  let KS #region st = ks in
  let C (C_13_wait_CF alpha cfk late_cfk ms_derived (msId, ms)) = !st in
  let (ae, h) = alpha in
  let hL = CoreCrypto.hashSize h in
  let sh_rctx = log_hash @| (msID_rc msId) in
  let rms = HSCrypto.hkdf_expand_label h ms "resumption master secret" sh_rctx hL in
  let ems : exportMS msId = HSCrypto.hkdf_expand_label h ms "resumption master secret" sh_rctx hL in
  let ts = HSCrypto.hkdf_expand_label h ms_derived "traffic secret" sh_rctx hL in
  st := C (C_13_postHS alpha late_cfk msId ts rms);
  (msId, ems)

// Called by Hanshake when DH key echange is negotiated
val ks_client_12_full_dh: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> peer_share:CommonDH.key -> ST CommonDH.key
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\
    (is_C_12_Full_CH (C.s st) \/ is_C_12_Resume_CH (C.s st) \/ is_C_13_1RTT_CH (C.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_full_dh ks sr pv cs ems peer_share =
  let KS #region st = ks in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_12_Resume_CH cr _ _ _) -> cr
    | C (C_13_1RTT_CH cr _ ) -> cr in
  let csr = cr @| sr in
  let alpha = (pv, cs, ems) in
  let our_share, pmsb = CommonDH.dh_responder peer_share in
  let dhp = CommonDH.key_params peer_share in
  let dhpms = PMS.DHPMS(dhp, our_share, peer_share, PMS.ConcreteDHPMS(pmsb)) in
  let dhpmsId = TLSInfo.SomePmsId(dhpms) in
  let ns = 
    if ems then
      C_12_wait_MS csr alpha dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS dhpmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; our_share

// Called by Handshake after server hello when a full RSA key exchange is negotiated
val ks_client_12_full_rsa: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> RSAKey.pk -> ST bytes
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\
    (is_C_12_Full_CH (C.s st) \/ is_C_12_Resume_CH (C.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_full_rsa ks sr pv cs ems pk =
  let KS #region st = ks in
  let alpha = (pv, cs, ems) in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_12_Resume_CH cr _ _ _) -> cr in
  let csr = cr @| sr in
  let rsapms = PMS.genRSA pk pv in
  let pmsb = PMS.leakRSA pk pv rsapms in
  let encrypted = CoreCrypto.rsa_encrypt (RSAKey.repr_of_rsapkey pk) CoreCrypto.Pad_PKCS1 pmsb in
  let rsapmsId = TLSInfo.SomePmsId(PMS.RSAPMS(pk, pv, rsapms)) in
  let ns =
    if ems then
      C_12_wait_MS csr alpha rsapmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS rsapmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; encrypted

val ks_client_12_set_session_hash: ks:ks -> log:bytes -> ST unit
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\ is_C_12_wait_MS (C.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_set_session_hash ks log =
  let KS #region st = ks in
  let C (C_12_wait_MS csr alpha pmsId pms) = !st in
  let (pv, cs, true) = alpha in
  let kef = kefAlg pv cs true in
  let ms = TLSPRF.prf_hashed (pv,cs) pms (utf8 "extended master secret") log 48 in
  let msId = ExtendedMS pmsId log kef in
  st := C (C_12_has_MS csr alpha msId ms)

// *********************************************************************************
//  All functions below assume that the MS is already computed (and thus they are
//  shared accross role, key exchange, handshake mode...)
// *********************************************************************************


// Will become private; public API will have
// ks_client_12_keygen: ks -> (i:id * w:StatefulLHAE.writer i)
// ks_server_12_keygen: ...
val ks_12_get_keys: ks:ks -> ST (wk:bytes * wiv:bytes * rk:bytes * riv:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    match st with
    | C (C_12_has_MS _ _ _ _) | S (S_12_has_MS _ _ _ _) -> true
    | _ -> false)
  (ensures fun h0 r h1 ->
    modifies Set.empty h0 h1)

(*private*) let ks_12_get_keys ks =
  let KS #region st = ks in
  let role, csr, alpha, msId, ms =
    match !st with
    | C (C_12_has_MS csr alpha msId ms) -> Client, csr, alpha, msId, ms
    | S (S_12_has_MS csr alpha msId ms) -> Server, csr, alpha, msId, ms in
  let cr, sr = split csr 32 in
  let (pv, cs, ems) = alpha in
  let ae_id = {
    msId = msId;
    kdfAlg = kdfAlg pv cs;
    pv = pv;
    aeAlg = get_aeAlg cs;
    csrConn = csr;
    ext = TLSInfo.ne_default; // TODO FIXME we don't have full NE anymore
    writer = role
  } in
  let expand = TLSPRF.kdf ae_id.kdfAlg ms (sr @| cr) 40 in
  let k1, expand = split expand 16 in
  let k2, expand = split expand 16 in
  let iv1, iv2 = split expand 4 in
  let wk, wiv, rk, riv =
    match role with
    | Client -> k1, iv1, k2, iv2
    | Server -> k2, iv2, k1, iv1 in
  (wk, wiv, rk, riv)

// VD functions split because we think the log agreement predicate may be different

val ks_client_12_client_verify_data: ks:ks -> log:bytes -> ST (vd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\ is_C_12_has_MS (C.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_client_verify_data ks log =
  let KS #region st = ks in
  let C (C_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
  TLSPRF.verifyData (pv,cs) ms Client log


val ks_server_12_client_verify_data: ks:ks -> log:bytes -> ST (vd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_S st /\ is_S_12_has_MS (S.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_client_verify_data ks log =
  let KS #region st = ks in
  let S (S_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
  TLSPRF.verifyData (pv,cs) ms Client log


val ks_server_12_server_verify_data: ks:ks -> log:bytes -> ST (vd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_S st /\ is_S_12_has_MS (S.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_server_verify_data ks log =
  let KS #region st = ks in
  let S (S_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
  st := S S_Done;
  TLSPRF.verifyData (pv,cs) ms Server log

val ks_client_12_server_verify_data: ks:ks -> log:bytes -> ST (vd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\ is_C_12_has_MS (C.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_server_verify_data ks log =
  let KS #region st = ks in
  let C (C_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
  st := C C_Done;
  TLSPRF.verifyData (pv,cs) ms Server log

