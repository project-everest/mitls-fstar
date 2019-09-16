module Idx

open Mem

module G = FStar.Ghost
module T = TLS.Handshake.Transcript
module B = LowStar.Buffer
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module HSM = HandshakeMessages

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30" 

/// TLS-specific Key Indices

/// We provide an instance of ipkg to track key derivation (here using constant labels)
/// These labels are specific to HKDF, for now strings e.g. "e exp master"
type label = s:string{Bytes.length (Bytes.bytes_of_string s) < 250}

/// The middle extraction takes an optional DH secret, identified by this triple
/// We use our own datatype to simplify typechecking
type id_dhe =
  | NoIDH
  | IDH: gX: CommonDH.dhi -> gY: CommonDH.dhr gX -> id_dhe

// The "ciphersuite hash algorithms" eligible for TLS 1.3 key derivation.
// We will be more restrictive.
type kdfa = EverCrypt.HMAC.supported_alg

/// Runtime key-derivation parameters, to be adjusted.
///
/// HKDF defines an injective function from (label * context) to bytes,
/// to be used as KDF indices
type context =
  | Extract: context // TLS extractions have no label and no context; we may separate Extract0 and Extract2
  | ExtractDH: v:id_dhe -> context // This is Extract1 (the middle extraction)
  | Expand: context // TLS expansion with default hash value
  | ExpandTranscript: tx:T.transcript_t -> context

/// Underneath, HKDF takes a "context" and a required length, with
/// disjoint internal encodings of the context:
/// [HKDF.format #ha label digest len]

type id_psk = nat // external application PSKs only; we may also set the usage's maximal recursive depth here.

// The `[@ Gc]` attribute instructs Kremlin to translate the `pre_id` field as a pointer,
// otherwise it would generate an invalid type definition.
[@ Gc]
type pre_id =
  | Preshared:
      a:kdfa (* fixing the hash algorithm *) ->
      id_psk  ->
      pre_id
  | Derive:
      i:pre_id (* parent index *) ->
      l:label (* static part of the derivation label *) ->
      context (* dynamic part of the derivation label *) ->
      pre_id

#push-options "--max_ifuel 1"

// Always bound by the index (and also passed concretely at creation-time).
val ha_of_id: pre_id -> kdfa
let rec ha_of_id = function
  | Preshared a _ -> a
  | Derive i lbl ctx -> ha_of_id i

private let hash_of_cs (cs:CipherSuite.cipherSuiteName) =
  match CipherSuite.cipherSuite_of_name cs with
  | Some (CipherSuite.CipherSuite13 _ ha) -> Some ha
  | _ -> None

// This function ensures that the hash of indexes derived
// with a transcript is consistent with the negotiated value
let consistent_transcript_hash (a:kdfa) (tx:T.transcript_t) =
  let open Parsers.ServerHello in
  let open Parsers.ServerHello_is_hrr in
  let open Parsers.SHKind in
  match tx with
  | T.ClientHello _ ch ->
    let open Parsers.ClientHello in
    let halgs = List.Tot.choose hash_of_cs ch.cipher_suites in
    List.Tot.memP a halgs
  | T.Transcript13 _ _ sh _ ->
    let ServerHello_is_hrr_false v = sh.is_hrr in
    (match hash_of_cs v.value.cipher_suite with
    | Some ha -> ha == a
    | _ -> False)
  | _ -> False

/// Stratified definition of id required.
///
/// We will enforce
/// * consistency on the hash algorithm
/// * monotonicity of the log infos (recursively including earlier resumption logs).
/// * usage restriction: the log after DH must include the DH identifier of the parent.
///   (Hence, we should either forbid successive DHs or authenticate them all.)
///
val pre_wellformed_id: pre_id -> Type0
let rec pre_wellformed_id = function
  | Preshared a _ -> True
  | Derive i l ctx ->
    pre_wellformed_id i /\
    (match ctx with
    | ExpandTranscript tx -> consistent_transcript_hash (ha_of_id i) tx
    | _ -> True)

#pop-options

/// Indexes are used concretely in model code, so we
/// erase them conditionally on model
let id: Type0 = 
  if model then i:pre_id {pre_wellformed_id i} else unit

unfold 
let wellformed_id (i:id) : Type0 =
  if model then pre_wellformed_id i else True

unfold 
let wellformed_derive (i:id) (l:label) (ctx:context) : Type0 =
  if model then pre_wellformed_id (Derive i l ctx) else True

unfold 
let derive (i:id) (l:label) (ctx:context{wellformed_derive i l ctx}) : id =
  if model then Derive i l ctx else ()

type honest_idh (c:context) =
  ExtractDH? c /\ 
  IDH? (ExtractDH?.v c) /\
  (let ExtractDH (IDH gX gY) = c in CommonDH.honest_dhr gY)

/// We use a global honesty table for all indexes. Inside ipkg, we
/// assume all index types are defined in the table below. We assume
/// write access to this table is public, but the following global
/// invariant must be enforced: if i is corrupt then all indexes
/// derived from i are also corrupt
/// ---EXCEPT if ctx is ExtractDH g gx gy with CommonDH.honest_dhr gy
///
type honesty_invariant (m:DM.t id (MDM.opt (fun _ -> bool))) =
  (forall (i:id) (l:label) (c:context{wellformed_derive i l c}).
  {:pattern (DM.sel m (derive i l c))}
  (match DM.sel m i, DM.sel m (derive i l c) with
  | Some false, Some true -> honest_idh c // DH-based idealization
  //| Some false, None -> honest_idh c
  | None, Some _ -> False // Can't define honesty of index derived from unregistered parent
  | _ -> True))

//Intentionally non-private because we need to recall it in ODH
type i_honesty_table =
  MDM.t tls_honest_region id (fun (t:id) -> bool) honesty_invariant

let h_table = if model then i_honesty_table else unit

let honesty_table: h_table =
  if model then
    MDM.alloc #id #(fun _ -> bool) #honesty_invariant #tls_honest_region ()
  else ()

(* 2019.06.05 SZ: this doesn't quite work and stalls proofs if marked as unfold
let honesty_loc =
  if model then B.loc_region_only true tls_honest_region
  else B.loc_none
*)

// Registered is monotonic
let registered (i:id) : Type0 =
  if model then
    let log : i_honesty_table = honesty_table in
    witnessed (MDM.defined log i)
  else True

type regid = i:id{registered i}

let honest (i:id) : Type0 =
  if model then
    let log: i_honesty_table = honesty_table in
    witnessed (MDM.contains log i true)
  else False

let corrupt (i:id) : Type0 =
  if model then
    let log : i_honesty_table = honesty_table in
    witnessed (MDM.contains log i false)
  else True

///  Lemmata relating registered, honest, and corrupt

// TODO: move to ulib?
private
val lemma_witnessed_true (p:mem_predicate) :
  Lemma (requires forall h. p h) (ensures witnessed p)
let lemma_witnessed_true p =
  lemma_witnessed_constant True;
  weaken_witness (fun _ -> True) p

val lemma_honest_registered (i:id) : Lemma
  (requires honest i)
  (ensures  registered i)
  [SMTPat (honest i)]
let lemma_honest_registered i = 
  if model then
    begin
    let log: i_honesty_table = honesty_table in
    let p = MDM.contains log i true in
    let q = MDM.defined log i in
    lemma_witnessed_impl p q;
    lemma_witnessed_true (fun h -> p h ==> q h)
    end
    
val lemma_corrupt_registered (i:id) : Lemma
  (requires corrupt i)
  (ensures  registered i)
  [SMTPat (corrupt i)]
let lemma_corrupt_registered i =
  if model then
    begin
    let log: i_honesty_table = honesty_table in
    let p = MDM.contains log i false in
    let q = MDM.defined log i in
    lemma_witnessed_impl p q;
    lemma_witnessed_true (fun h -> p h ==> q h)
    end

val lemma_honest_not_corrupt: i:regid -> Lemma (honest i ==> ~(corrupt i))
let lemma_honest_not_corrupt i =
  if model then
    begin
    let log: i_honesty_table = honesty_table in
    lemma_witnessed_and (MDM.contains log i true) (MDM.contains log i false);
    lemma_witnessed_impl (fun h -> MDM.contains log i true h /\ MDM.contains log i false h) (fun _ -> False);
    lemma_witnessed_true (fun h -> MDM.contains log i true h /\ MDM.contains log i false h ==> False);
    lemma_witnessed_constant False
    end

#push-options "--max_ifuel 1"

val lemma_corrupt_invariant (i:regid) (lbl:label) (ctx:context) : Lemma
  (requires 
    wellformed_derive i lbl ctx /\ 
    ~(honest_idh ctx) /\
    registered (derive i lbl ctx) /\
    corrupt i)
  (ensures corrupt (derive i lbl ctx))
let lemma_corrupt_invariant i lbl ctx =
  if model then
    begin
    let log: i_honesty_table = honesty_table in
    let p1 = fun h -> honesty_invariant (MDM.repr (sel h log)) in
    let p2 = MDM.contains log i false in
    let p3 = MDM.defined log (derive i lbl ctx) in
    let q  = MDM.contains log (derive i lbl ctx) false in
    lemma_witnessed_true p1; // From monotonicity of honesty_table
    assert (witnessed p2);   // From corrupt i
    lemma_witnessed_and p1 p2;
    lemma_witnessed_and (fun h -> p1 h /\ p2 h) p3;
    lemma_witnessed_impl (fun h -> p1 h /\ p2 h /\ p3 h) q; // From honesty_invariant and ~(honest_idh ctx)
    lemma_witnessed_true (fun h -> (p1 h /\ p2 h /\ p3 h) ==> q h);
    assert (witnessed q) // Modus ponens
    end

// 2019.06.05 SZ
// This isn't provable from the monotonicity API:
//
//  val lemma_not_corrupt_honest: i:regid -> Lemma (honest i \/ corrupt i)
//
// The following stateful variant
//
//  val lemma_honest_or_corrupt (i:regid) : ST unit 
//    (requires fun _ -> True) 
//    (ensures  fun h0 _ h1 -> h0 == h1 /\ (honest i \/ corrupt i))
//
// is provable adding this benign-looking axiom:
//
//  val bind_squash_st: #a:Type -> #b:Type -> #pre:(mem -> Type) ->
//    squash a ->
//    $f:(a -> ST (squash b) (requires fun h0 -> pre h0) (ensures fun h0 _ h1 -> h0 == h1)) ->
//    ST (squash b) (requires fun h0 -> pre h0) (ensures fun h0 _ h1 -> h0 == h1)
//
// See git history from an actual proof. 
// Together with lemma_honest_not_corrupt above it implies
//
//  val lemma_honest_corrupt_st (i:regid) : ST unit 
//    (requires fun _ -> True) 
//    (ensures  fun h0 _ h1 -> h0 == h1 /\ (honest i <==> ~(corrupt i)))
//
// However, it looks like this lemma is unnecessary and we don't need 
// to introduce any axioms.

inline_for_extraction noextract
val get_honesty (i:regid) : ST bool
  (requires fun h0 -> True)
  (ensures  fun h0 b h1 -> h0 == h1 /\ (b <==> honest i))
let get_honesty i =  
  if model then
    let log : i_honesty_table = honesty_table in
    testify (MDM.defined log i);
    match MDM.lookup log i with
    | Some true -> true
    | Some false -> lemma_honest_not_corrupt i; false
  else false
 
val lemma_honesty_update (m:DM.t id (MDM.opt (fun _ -> bool)))
  (i:regid) (l:label) (c:context) (b:bool) : Lemma
    (requires 
      wellformed_derive i l c /\
      honesty_invariant m /\
      Some? (DM.sel m i) /\ // Parent honesty is defined
      None? (DM.sel m (derive i l c)) /\ // Derived honesty is not yet defined
      // To derive honest, the parent is honest or the derivation uses honest shares
      (b ==> (honest_idh c \/ DM.sel m i == Some true)))
    (ensures honesty_invariant (DM.upd m (derive i l c) (Some b)))
let lemma_honesty_update m i l c b =
  let j = derive i l c in
  let m' = DM.upd m j (Some b) in
  let wit (i0:id) (l0:label) (c0:context{wellformed_derive i0 l0 c0})
    : Lemma (match DM.sel m' i0, DM.sel m' (derive i0 l0 c0) with
      | Some false, Some true -> honest_idh c0
      | None, Some _ -> False | _ -> True)
    =
    let j0 = derive i0 l0 c0 in
    if j = j0 then (
      if i0 <> j then DM.sel_upd_other m j (Some b) i0;
      DM.sel_upd_same m j (Some b)
    ) else (
      if i0 <> j then DM.sel_upd_other m j (Some b) i0;
      DM.sel_upd_other m j (Some b) j0
    )
    in
  FStar.Classical.forall_intro_3 wit

#push-options "--max_ifuel 1"

inline_for_extraction noextract
let register_derive (i:regid) (l:label) (c:context) : ST (regid * bool)
  (requires fun h0 -> wellformed_derive i l c)
  (ensures  fun h0 (i', b) h1 ->
    (if model then B.modifies (B.loc_region_only true tls_honest_region) h0 h1
     else h0 == h1) /\
    i' == derive i l c /\ 
    (b <==> honest i'))
  =
  if model then
    let h0 = get() in
    let i' = Derive i l c in
    let log : i_honesty_table = honesty_table in
    recall log;
    match MDM.lookup log i' with
    | Some true ->
      begin
      lemma_honest_registered i';
      lemma_honest_not_corrupt i'; 
      (i', true)
      end
    | Some false ->
      begin
      lemma_corrupt_registered i';
      lemma_honest_not_corrupt i'; 
      (i', false)
      end
    | None ->
      begin
      let h = get() in
      testify (MDM.defined log i);
      match MDM.lookup log i with
      | Some true ->
        begin
        assert (honest i);
        lemma_honesty_update (MDM.repr (sel h log)) i l c true;
        MDM.extend log i' true;
        lemma_honest_registered i';
        let h1 = get() in
        // Compatibility lemma to bridge between LowStar and HST modifies 
        B.modifies_loc_regions_intro (Set.singleton tls_honest_region) h0 h1;
        (i', true)
        end
      | Some false ->
        begin
        assert (corrupt i);
        lemma_honesty_update (MDM.repr (sel h log)) i l c false;
        MDM.extend log i' false;
        lemma_corrupt_registered i';
        lemma_honest_not_corrupt i';
        let h1 = get() in
        // Compatibility lemma to bridge between LowStar and HST modifies 
        B.modifies_loc_regions_intro (Set.singleton tls_honest_region) h0 h1;
        (i', false)
        end
      end
  else ((), false)


// 17-10-21 WIDE/NARROW INDEXES (old)
//
// We'd rather keep wide indexes secret.  Internally, for each salt
// index, we maintain a table from (g, gX, gY) to PRFs, with some
// sharing.  (The sharing may be public, but not wide indexes values
// are not.)  Informally this is sound because our limited use of the
// tables does not depend on their sharing.
//
// The danger of overly precise indexes is that, ideally, we may
// separate instances that use the same concrete keys---in our case
// this does not matter because security does not depend on their
// sharing.

noextract
let ii: Pkg.ipkg = // (#info:Type0) (get_info: id -> info) =
  Pkg.Idx id registered honest get_honesty
