module KeySchedule (*SKETCH *)
(*the top level key schedule module, it should not expose secrets to Handshake *)

(* the goal is to keep ephemerals like eph_s and eph_c as currently defined 
   in Handshake local *)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
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
open HSCrypto

// TLSPRF.fst for TLS 1.2
// CoreCrypto.hkdf for TLS 1.3
// subsumes the idealized module PRF.fst


// LONG TERM GLOBAL SECRETS

abstract type master_secret = b:bytes{}
abstract type resumption_secret = b:bytes{}
type exporter_secret = b:bytes{}
abstract type pre_share_key = b:bytes{}

val cert_keys: ref RSAKey.RSA_PK; // 
val ticket_key: ref bytes // TODO

type schedule_state_13 =
| KXS13_INIT
| KXS13_HANDSHAKE
| KXS13_TRAFFIC

type schedule_state_12 =
| KXS12_INIT
| KXS12_COMMIT
| KXS12_KEYGEN
| KXS12_FINISHED

type schedule_state =
| KXS_13 of schedule_state_13
| KXS_12 of schedule_state_12

type kx_state = {
 role: role;
 pv: pv;
 g: dh_group;
 dh_secret: dh_priv;
 dh_peer: dh_public;
 dh_agreed: bytes;
 kx_state: schedule_state;
}

//| KX_server of (pv:pv) * (g:dh_group) * (y:dh_priv) * (gy:dh_public) * (st:schedule_state)
//| KX_client of (pv:pv) * (g:dh_group) * (x:dh_priv) * (gx:dh_pubic) * (st:schedule_state)

val internal_state: Map.t rid (ref kx_state)
let state_map = ref (const kx_state)

// Init functions
//val dh_server_init: #region:rid -> pv:pv -> ST unit (requires fun h->) (ensures contains (!state_map) rid)
//val dh_client_iinit: 

val kx_init: #region:rid -> role:role -> pv:pv -> g:dh_group -> gx:option dh_pub{gx=None <==> (pv=TLS_1p3 /\ role = Client) \/ (role = Server /\ pv<>TLS_1p3)} -> ST dh_pub

val kx_set_peer: #region:rid -> gx:dh_pub -> ST unit (requires (sel !state_map rid).kx_state = KX .... ) 

// New handshake interface:
//val dh_init_server_exchange: #region:rid -> g:dh_group -> ST (gy: dh_key)
//val dh_client_exchange: #region:rid -> g:

// TLS 1.2 + 1.3
// state-aware
val dh_next_key: #region:rid -> log:bytes -> 




// ADL: PROBLEM WITH RESUMPTION
// Currently if handshake has a set ri and server rejects resumption it will fail for no good reason
// We cannot commit to the pv and 
let kx_init_client #region:rid cfg:config k: =
    // create fresh sessionInfo
    // if cfg.resumption enabled
      // Lookup session DB for cfg.server_name
      // if valid session found fill in sessionInfo
    // otherwise geneate client random + client key share (if pv>=1.3) + session identifier
    // set KS state to Init

let kx_init_server #region:rid cfg:config cr:crandom ckx:option<dh_pub> pvcs:pv*cs index:option<either3<sid,psk_ids,ticket>> =
    // Create fresh sessionINfo
    // 





// OLD


assume val dh_commit
assume val dh_server_verify
assume val dh_client_verify

(* For TLS12 and below only the server keeps state concretely *)
type ks_12S =
    | KS_12S: #region: rid -> x: rref region (KEX_S_PRIV) -> ks_12S
    
  
(* For TLS13 both client and server keep state concretely *)    
type ks_13C
    | KS_13C: #region: rid -> x: rref region HSCrypto.dh_key -> ks_13C
    ...


(* for idealization we need a global log *)
type state =
  | Init
  | Committed of ProtocolVersion * aeAlg * negotiatedExtensions
  | Derived: a:id -> b:id -> derived a b -> state
  
type kdentry = CsRands * state 
let kdlog : ref<list<kdentry>> = ref [] 
  
(* TLS 1.2 *)
val dh_init_12S: #region:rid -> g:dh_group -> ST (state:ks_12S * gx:dh_key)

let dh_init_12S r g =
  let x = dh_keygen g
  let xref = ralloc r 0 in
  let xref := KEX_S_PRIV_DHE x
  KS_12S r xref, x.public
  
assume val derive_12C: gx:dh_key -> ... -> ST(gy:dh_key * (both i) * ms)

let derive12C gx cr sr log rd wr i = 
  let (y, gxy) = dh_shared_secret2 gx 
  y.public, derive_keys gxy cr sr log rd wr i


assume val derive_12S: state:ks_12S -> gy:dh_key -> ... -> ST ((both i) * ms)

let derive_12S state gy cr sr log rd wr i =
  let (KS_12S xref) = state 
  derive_keys (dh_shared_secret1 !xref) cr sr log rd wr i

(* TLS 1.3 *)

val dh_init_13S: #region:rid g:dh_group -> ST (state:ks_13S * gs:dh_key) //s
val dh_init_13C: #region:rid g:dh_group -> ST (state:ks_13C * gx:dh_key) //x

assume val derive_13S_1: state:ks_13S -> gx:dh_key -> ... -> ST(gy:dh_key * (both i)) //handshake
assume val derive_13S_2: state:ks_13S -> ... -> ST(cf:ms * sf:ms) //finished
assume val derive_13S_3: state:ks_13S -> ... -> ST(both i) //traffic

assume val derive_13C_1: state:ks_13C -> gy:dh_key -> ... -> ST(both i) //handshake
assume val derive_13C_2: state:ks_13C -> gs:dh_key -> ... -> ST(cf:ms * sf:ms) //finished
assume val derive_13C_3: state:ks_13C -> ... -> ST(both i) //traffic
