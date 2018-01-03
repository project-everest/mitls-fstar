module Idx

open Mem
open Pkg

module MM = FStar.Monotonic.Map

// 17-12-08 we considered separating "honesty" from the more ad hoc parts of this file.

/// TLS-SPECIFIC KEY INDICES
/// --------------------------------------------------------------------------------------------------
///
/// We provide an instance of ipkg to track key derivation (here using constant labels)
/// these labels are specific to HKDF, for now strings e.g. "e exp master".
type label = string

/// the middle extraction takes an optional DH secret, identified by this triple
/// we use our own datatype to simplify typechecking
type id_dhe =
  | NoIDH
  | IDH:
    gX: CommonDH.dhi ->
    gY: CommonDH.dhr gX -> id_dhe

// The "ciphersuite hash algorithms" eligible for TLS 1.3 key derivation.
// We will be more restrictive.
type kdfa = Hashing.Spec.alg

/// Runtime key-derivation parameters, to be adjusted.
///
/// HKDF defines an injective function from label * context to bytes, to be used as KDF indexes.
///
type context =
  | Extract: context // TLS extractions have no label and no context; we may separate Extract0 and Extract2
  | ExtractDH: v:id_dhe -> context // This is Extract1 (the middle extraction)
  | Expand: context // TLS expansion with default hash value
  | ExpandLog: // TLS expansion using hash of the handshake log
    info: TLSInfo.logInfo (* ghost, abstract summary of the transcript *) ->
    hv: Hashing.Spec.anyTag (* requires stratification *) -> context

/// Underneath, HKDF takes a "context" and a required length, with
/// disjoint internal encodings of the context:
/// [HKDF.format #ha label digest len]

type id_psk = nat // external application PSKs only; we may also set the usage's maximal recursive depth here.
type pre_id =
  | Preshared:
      a: kdfa (* fixing the hash algorithm *) ->
      id_psk  ->
      pre_id
  | Derive:
      i:pre_id (* parent index *) ->
      l:label (* static part of the derivation label *) ->
      context (* dynamic part of the derivation label *) ->
      pre_id

// always bound by the index (and also passed concretely at creation-time).
val ha_of_id: i:pre_id -> kdfa
let rec ha_of_id = function
  | Preshared a _ -> a
  | Derive i lbl ctx -> ha_of_id i

// placeholders
assume val idh_of_log: TLSInfo.logInfo -> id_dhe
assume val summary: bytes -> TLSInfo.logInfo

// concrete transcript digest
let digest_info (a:kdfa) (info:TLSInfo.logInfo) (hv: Hashing.Spec.anyTag) =
  exists (transcript: bytes).
    // Bytes.length hv = tagLen a /\
    hv = Hashing.Spec.hash a transcript /\
    Hashing.CRF.hashed a transcript /\
    info = summary transcript

/// stratified definition of id required.
///
/// we will enforce
/// * consistency on the hash algorithm
/// * monotonicity of the log infos (recursively including earlier resumption logs).
/// * usage restriction: the log after DH must include the DH identifier of the parent.
///   (Hence, we should either forbid successive DHs or authenticate them all.)
///
val wellformed_id: pre_id -> Type0
let rec wellformed_id = function
  | Preshared a _ -> True
  | Derive i l (ExpandLog info hv) -> wellformed_id i /\ digest_info (ha_of_id i) info hv
  | Derive i lbl ctx ->
      //TODO "ctx either extends the parent's, or includes its idh" /\
      wellformed_id i

type id = i:pre_id {wellformed_id i}

type honest_idh (c:context) =
  ExtractDH? c /\ IDH? (ExtractDH?.v c) /\
  (let ExtractDH (IDH gX gY) = c in CommonDH.honest_dhr gY)

/// We use a global honesty table for all indexes Inside ipkg, we
/// assume all index types are defined in the table below We assume
/// write access to this table is public, but the following global
/// invariant must be enforced: if i is corrupt then all indexes
/// derived from i are also corrupt
/// ---EXCEPT if ctx is ExtractDH g gx gy with CommonDH.honest_dhr gy
///
type honesty_invariant (m:MM.map' id (fun _ -> bool)) =
  (forall (i:id) (l:label) (c:context{wellformed_id (Derive i l c)}).
  {:pattern (m (Derive i l c))}
  Some? (m (Derive i l c)) ==> Some? (m i) /\
  (m i = Some false ==> (honest_idh c \/ m (Derive i l c) = Some false)))

//17-12-08 removed [private] twice, as we need to recall it in ODH :(
type i_honesty_table =
  MM.t tls_honest_region id (fun (t:id) -> bool) honesty_invariant
let h_table = if model then i_honesty_table else unit

let honesty_table: h_table =
  if model then
    MM.alloc #tls_honest_region #id #(fun _ -> bool) #honesty_invariant
  else ()

// Registered is monotonic
type registered (i:id) =
  (if model then
    let log : i_honesty_table = honesty_table in
    witnessed (MM.defined log i)
  else True)

type regid = i:id{registered i}

type honest (i:id) =
  (if model then
    let log: i_honesty_table = honesty_table in
    witnessed (MM.contains log i true)
  else False)

type corrupt (i:id) =
  (if model then
    let log : i_honesty_table = honesty_table in
    witnessed (MM.contains log i false)
  else True)

// ADL: difficult to prove, relies on an axiom outside the current formalization of FStar.Monotonic
let lemma_honest_corrupt (i:regid)
  : Lemma (honest i <==> ~(corrupt i)) =
  admit()

let lemma_corrupt_invariant (i:regid) (lbl:label)
  (ctx:context {wellformed_id (Derive i lbl ctx) /\ registered (Derive i lbl ctx)})
  : ST unit
  (requires fun h0 -> ~(honest_idh ctx))
  (ensures fun h0 _ h1 ->
    corrupt i ==> corrupt (Derive i lbl ctx) /\ h0 == h1)
  =
  lemma_honest_corrupt i;
  lemma_honest_corrupt (Derive i lbl ctx);
  if model then
    let log : i_honesty_table = honesty_table in
    recall log;
    testify (MM.defined log i);
    match MM.lookup log i with
    | Some true -> ()
    | Some false ->
      let m = !log in
      // No annotation, but the proof relies on the global log invariant
      testify (MM.defined log (Derive i lbl ctx));
      MM.contains_stable log (Derive i lbl ctx) false;
      mr_witness log (MM.contains log (Derive i lbl ctx) false)
  else ()

assume val bind_squash_st:
  #a:Type ->
  #b:Type ->
  squash a ->
  $f:(a -> ST (squash b) (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))) ->
  ST (squash b) (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))

let get_honesty (i:id {registered i}) : ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> honest i))
  =
  lemma_honest_corrupt i;
  if model then
    let log : i_honesty_table = honesty_table in
    recall log;
    testify (MM.defined log i);
    match MM.lookup log i with
    | Some b ->
      (*
       * AR: 03/01
       *     We need to show b <==> honest i
       *     The direction b ==> honest i is straightforward, from the postcondition of MM.lookup
       *     For the other direction, we need to do a recall on the witnessed predicate in honest i
       *     One way is to go through squash types, using a bind_squash_st axiom above
       *)
      let aux () :ST (squash (honest i ==> b2t b)) (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))
        = let f :(c_or (honest i) (~ (honest i))) -> ST (squash (honest i ==> b2t b))
	                                               (requires (fun _ -> True))
						       (ensures  (fun h0 _ h1 -> h0 == h1))
	    = fun x ->
	      match x with
	      | Left h  -> Squash.return_squash h; testify (MM.contains log i true)
	      | Right h -> Squash.return_squash h; assert (honest i ==> b2t b)
	  in
	  //y:l_or (honest i) (~ (honest i))
	  let y = Squash.bind_squash (Squash.get_proof (l_or (honest i) (~ (honest i)))) (fun y -> y) in
	  bind_squash_st y f
      in
      aux ();
      b
  else false

// TODO(adl) preservation of the honesty table invariant
let rec lemma_honesty_update (m:MM.map id (fun _ -> bool) honesty_invariant)
  (i:regid) (l:label) (c:context{wellformed_id (Derive i l c)}) (b:bool{b <==> honest i})
  : Lemma (honesty_invariant (MM.upd m (Derive i l c) b))
// : Lemma (requires Some? (m i ) /\ None? (m (Derive i l c)) /\ m i == Some false ==> not b)
//         (ensures honesty_invariant (MM.upd m (Derive i l c) b))
  = admit() // easy

let register_derive (i:id{registered i}) (l:label) (c:context{wellformed_id (Derive i l c)})
  : ST (i:id{registered i} * bool)
  (requires fun h0 -> True)
  (ensures fun h0 (i', b) h1 ->
    (if model then modifies_one tls_honest_region h0 h1 else h0 == h1)
    /\ (i' == Derive i l c)
    /\ (b2t b <==> honest i'))
  =
  let i':id = Derive i l c in
  if model then
    let log : i_honesty_table = honesty_table in
    recall log;
    match MM.lookup log i' with
    | Some b -> lemma_honest_corrupt i'; (i', b)
    | None ->
      let b = get_honesty i in
      let h = get () in
      lemma_honesty_update (sel h log) i l c b;
      MM.extend log i' b;
      lemma_honest_corrupt i';
      (i', b)
  else (i', false)

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

let ii: ipkg = // (#info:Type0) (get_info: id -> info) =
  Idx id registered honest get_honesty
