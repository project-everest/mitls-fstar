(**
Shared state for secret expansion and salt expansion
This file exists to break a cyclic module dependency:
KDF.Salt.* operates on the same secrets as KDF.Expand
but both cannot be implemented in a single module because
of the cyclic dependency.
*)
module KDF.Common
module HST = FStar.HyperStack.ST //Added automatically

/// 17-09-20 This file is an early experiment---not currently used.
/// 
open FStar.Heap

open FStar.HyperStack

open FStar.Bytes
open FStar.Error
open TLSError
open TLSConstants
open TLSInfo

module MM = FStar.Monotonic.Map


module HS = FStar.HyperStack

(*)
(* Source index is a secret index *)
type id = secretId

(* The kind of expansion, either salt of expanded secret *)
type expand_kind (i:id) =
  | ExpandSalt: expand_kind i
  | ExpandBinder: expand_kind i
  | ExpandBinderResumption: expand_kind i
  | ExpandEarlyExporter: log:hashed_log -> li:logInfo{LogInfo_CH? li /\ log_info li log} -> expand_kind i
  | ExpandEarlyTrafffic: log:hashed_log -> li:logInfo{LogInfo_CH? li /\ log_info li log} -> expand_kind i
  | ExpandClientHandshakeTraffic: log:hashed_log -> li:logInfo{LogInfo_SH? li /\ log_info li log} -> expand_kind i
  | ExpandServerHandshakeTraffic: log:hashed_log -> li:logInfo{LogInfo_SH? li /\ log_info li log} -> expand_kind i
  | ExpandClientApplicationTraffic: log:hashed_log -> li:logInfo{LogInfo_SF? li /\ log_info li log} -> expand_kind i
  | ExpandServerApplicationTraffic: log:hashed_log -> li:logInfo{LogInfo_SF? li /\ log_info li log} -> expand_kind i
  | ExpandExporter: log:hashed_log -> li:logInfo{LogInfo_SF? li /\ log_info li log} -> expand_kind i
  | ExpandResumption: log:hashed_log -> li:logInfo{LogInfo_CF? li /\ log_info li log} -> expand_kind i

// Conceptually, this is either a KDF.Salt.X.state i or KDF.Expand.state i
// However, the table stores actual key values, and the proper interface for
// accessing it is spread between KDF.Salt.X and KDF.Expand
type extracted_secret (#i:id) (x:expand_kind i) =
  lbytes (Hashing.Spec.tagLen (secretId_hash i))
*)

type ideal_log (dt:Type0) (rt:dt -> Tot Type0) (r:rgn) =
  MM.t r dt rt (fun _ -> True)
type expand_log (dt:Type0) (rt:dt -> Tot Type0) (r:rgn) =
  (if Flags.ideal_KEF then ideal_log dt rt r else unit)

abstract noeq type prf (#it:Type0) (i:it) =
  | PRF:
    r:rgn ->
    hashAlg: (it -> Tot Hashing.Spec.alg) ->
    honest_prf: bool ->
    key: Hashing.Spec.tag (hashAlg i) ->
    domain: (t:Type0{hasEq t}) ->
    range: (domain -> Tot Type0) ->
    format: (domain -> Tot bytes) ->
    log: expand_log domain range r ->
    pre: (domain -> expand_log domain range r -> h:HS.mem -> GTot Type0) ->
    post: (d:domain -> range d -> expand_log domain range r -> h0:HS.mem -> h1:HS.mem -> GTot Type0) ->
    honestT: (p:(domain -> GTot Type0){not Flags.ideal_KEF ==> (forall (d:domain).~(p d))}) ->
    is_honest: (d:domain -> ST bool
      (requires fun h0 -> True)
      (ensures fun h0 b h1 -> h0 == h1 /\ b <==> honestT d)) ->
    gen: (d:domain -> ST (range d)
      (requires fun h -> honestT d /\ (Flags.ideal_KEF ==> pre d log h))
      (ensures fun h0 o h1 -> Flags.ideal_KEF ==> post d o log h0 h1)) ->
    coerce: (d:domain -> Hashing.Spec.tag (hashAlg i) -> ST (range d)
      (requires fun h -> ~(honestT d) /\ (Flags.ideal_KEF ==> pre d log h))
      (ensures fun h0 o h1 -> Flags.ideal_KEF ==> post d o log h0 h1)) ->
    prf #it i

// Create an honest PRF instance at index i of type it
let create (#it:Type0) (i:it) (r:rgn) (hashAlg: it -> Tot Hashing.Spec.alg)
  (domain:Type0{hasEq t}) (range:domain -> Tot Type0) (format: domain -> Tot bytes)
  (pre: domain -> expand_log domain range r -> h:HS.mem -> GTot Type0)
  (post: d:domain -> range d -> expand_log domain range r -> h0:HS.mem -> h1:HS.mem -> GTot Type0)
  (honestT: p:(domain -> GTot Type0){not Flags.ideal_KEF ==> (forall (d:domain).~(p d))})
  : ST (prf #it i)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
  =
  admit()


let random (len:nat) : ST (lbytes len)
  (requires fun h0 -> True) (ensures fun h0 _ h1 -> h0 == h1)
  = assume false; CoreCrypto.random len

#set-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"
let expand (#it:Type0) (#i:it) (prf:prf #it i) (input:PRF?.domain prf)
  : ST (output: (PRF?.range prf) input)
  (requires (fun h0 ->
    Flags.ideal_KEF ==> (PRF?.pre prf) input (PRF?.log prf) h0))
  (ensures (fun h0 r h1 -> True))
  =
  let ha = (PRF?.hashAlg prf) i in
  if Flags.ideal_KEF then
    let h0 = get() in
    cut((PRF?.pre prf) input (PRF?.log prf) h0);
    let log : ideal_log (PRF?.domain prf) (PRF?.range prf) (PRF?.r prf) = PRF?.log prf in
    HST.recall log;
    match MM.lookup log input with
    | Some v -> v
    | None ->
      cut(MM.sel (HS.sel h0 log) input == None);
      let h1 = get() in
      cut(h0 == h1);
      let key =
        if PRF?.honest_prf prf then random (Hashing.Spec.tagLen ha)
        else HKDF.expand ha (PRF?.key prf) ((PRF?.format prf) input) (Hashing.Spec.tagLen ha) in
      let h2 = get() in
      assume(h2 == h1);
      cut((PRF?.pre prf) input (PRF?.log prf) h2);
      let h5 = get () in
      let b = (PRF?.is_honest prf) input in
      let h3 = get() in
      assume (h3 == h5); // Why?
      let output =
        if b then (PRF?.gen prf) input
        else (PRF?.coerce prf) input key in
      let h4 = get() in
      assume(h0 == h4);
      cut(MM.sel (HS.sel h4 log) input == None);
      MM.extend log input output;
      output
  else
    let k = HKDF.expand ha (PRF?.key prf) ((PRF?.format prf) input) (Hashing.Spec.tagLen ha) in
    (PRF?.coerce prf) input k
