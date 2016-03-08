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

(* For TLS12 and below only the server keeps state concretely *)
type ks_12S =
    | KS_12S: #region: rid -> x: rref region (KEX_S_PRIV) -> ks_12S
    
  
(* For TLS13 both client and server keep state concretely *)    
type ks_13C
    | KS_13C: #region: rid -> x: rref region HSCrypto.dh_key -> ks_13C
    ...


(* for idealization we need a top level log *)
type state =
  | Init
  | Committed of ProtocolVersion * aeAlg * negotiatedExtensions
  | Derived: a:id -> b:id -> derived a b -> state
  
type kdentry = CsRands * state 
let kdlog : ref<list<kdentry>> = ref [] 
  
(* TLS 1.2 *)
val dh_init_12S: #region:rid g:dh_group -> ST (state:ks_12S * gx:dh_key)

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
