module API

module F = Flags
module G = FStar.Ghost
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = FStar.Bytes
module LB = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module M = LowStar.Modifies
module I = FStar.Integers
module S = FStar.Seq
module L = FStar.List.Tot
module MS = FStar.Monotonic.Seq

unfold type uint8_p = LB.buffer UInt8.t
unfold type uint32_t = UInt32.t
unfold type uint32_p = LB.pointer uint32_t

(*
(* Re-export crypto algorithm names from EverCrypt *)
include EverCrypt.Alg

(* Configuration *)
include TLS.Config
*)

val config: Type0
type role = | Client | Server
val get_role: config -> role

(* Utility missing from Modifies *)
(* Saves writing manual unfolding of loc_union *)
private let rec loc_of_list' (x:list M.loc) : GTot M.loc =
  match x with
  | [] -> M.loc_none
  | h::t -> M.loc_union h (loc_of_list' t)
unfold let loc_of_list (x:list M.loc) = normalize_term (loc_of_list' x)
unfold let loc_of_region_list (x:list HS.rid) = normalize_term (M.loc_regions true (Set.as_set x))

(*** TLS API ***)

(**
Connection state is kept abstract to keep the API stabe.
All connection-local state is kept in the indexed region.
**)
[@CAbstractStruct]
val tls_s: HS.rid -> Type0

(**
The connection-specific part of the invariant. We explicitly
separate it from the tls_global_invariant to make it easier
to frame the tls_invariant in two cases:
 - modifies to locations disjoint from the footprint
 - modifies caused by operations on a different connection
**)
val tls_s_local_inv: #r:HS.rid -> tls_s r -> HS.mem -> Type0

(**
Framing of the connection-local invariant,
only requires disjointness with the connection's region
**)
val lemma_tls_frame_local_inv: #r:HS.rid -> s:tls_s r ->
  h0:HS.mem -> l:M.loc -> h1:HS.mem -> Lemma
  (requires tls_s_local_inv s h0
    /\ M.loc_disjoint l (M.loc_region_only true r)
    /\ M.modifies l h0 h1)
  (ensures tls_s_local_inv s h1)

(**
Global region and global invariant (implemented as
as walk over the connection table, but kept abstract
in the interface), used for the security model.
**)
val tls_global_region: HS.rid
val tls_global_invariant: h:HS.mem -> Type0

(**
Connection state is internally allocated and accessed
through an immutable pointer, avoiding an unnecessary
invariant (but at the cost of an erased argument)
**)
let tls_state (r:HS.rid) (*s:G.erased tls_s*) =
  p:IB.ipointer (tls_s r) {
    IB.frameOf p == r /\ LB.freeable p
//    /\ IB.witnessed p (fun x -> x == S.create 1 (G.reveal s))
  }

(**
Ghost dereferencing of the connection state pointer,
does not require liveness **)
let tls_deref (#r:HS.rid) (p:tls_state r) (m:HS.mem) : GTot (tls_s r)
  = IB.get m p 0

(**
We reveal a region-based footprint to the users of the API.
This allows TLS to perform further allocations during the
lifetime of the connection without requiring the footprint
to be a stateful function.
**)
let tls_footprint (#r:HS.rid) (p:tls_state r) =
  loc_of_region_list [r; tls_global_region]

(**
The full invariant of live connections, which include
the liveness of the state pointer, the connection-local
invariant and the global invariant
**)
let tls_invariant (#r:HS.rid) (p:tls_state r) (h:HS.mem) =
  IB.live h p /\ tls_s_local_inv (tls_deref p h) h /\ tls_global_invariant h

val lemma_frame_tls_invariant: #r:HS.rid -> p:tls_state r ->
  h0:HS.mem -> l:M.loc -> h1:HS.mem -> Lemma
  (requires tls_invariant p h0 /\
    M.modifies l h0 h1 /\
    M.loc_disjoint (tls_footprint p) l)
  (ensures tls_invariant p h1)

val lemma_frame_tls_invariant2: #r:HS.rid -> p:tls_state r ->
  h0:HS.mem -> #r':HS.rid -> p':tls_state r' -> h1:HS.mem -> Lemma
  (requires tls_invariant p h0 /\
    M.modifies (tls_footprint p') h0 h1 /\
    M.loc_disjoint (M.loc_region_only true r) (M.loc_region_only true r') /\
    tls_invariant p' h1)
  (ensures tls_invariant p h1)

(** Ghost state machine to control access to API functions **)
type tls_stm =
  | InError // Can only call get_error
  | InHandshake // Can only call do_handshake
  | InHandshakeReadable // Can only call read
  | InHandshakeWritable // Can call do_handshake and write
  | HandshakeComplete // Can call read, write and close
  | LocalClosed // Can only call read
  | RemoteClosed // Can only call write
  | FullClosed // Can only call free

// ADL: it would be nicer if we could use witnesses here
// but there is a problem with 0-RTT: the connection stops
// being writable before the handshake is complete, i.e.
// InHandshake -> InHandshakeWritable -> InHandshake
// is a valid transition sequence...
val tls_get_stm: #r:HS.rid -> s:tls_state r -> m:HS.mem -> GTot tls_stm

// Since get_stm is not monotonic, we need framing
val lemma_frame_tls_stm: #r:HS.rid -> s:tls_state r ->
  h0:HS.mem -> l:M.loc -> h1:HS.mem -> Lemma
  (requires M.loc_disjoint (M.loc_region_only true r) l /\ M.modifies l h0 h1)
  (ensures tls_get_stm s h0 == tls_get_stm s h1)

// Since get_stm is not monotonic, we need framing
val lemma_frame_tls_stm2: #r:HS.rid -> s:tls_state r ->
  h0:HS.mem -> #r':HS.rid -> s':tls_state r' -> h1:HS.mem -> Lemma
  (requires M.modifies (tls_footprint s') h0 h1 /\
    M.loc_disjoint (M.loc_region_only true r) (M.loc_region_only true r'))
  (ensures tls_get_stm s h0 == tls_get_stm s h1)

(** Read configuration **)
val tls_get_configT: #r:HS.rid -> s:tls_s r -> GTot config
val tls_get_config: #r:HS.rid -> p:tls_state r ->
  ST.ST config
  (requires fun h0 -> tls_invariant p h0)
  (ensures fun h0 cfg h1 -> M.modifies M.loc_none h0 h1 /\
    cfg == tls_get_configT (tls_deref p h0))

(**
Ghostly read the current active index, after
the handshake is complete (does not work for 0-RTT)
**)
type rw = | Reader | Writer
let peer_rw = function | Reader -> Writer | Writer -> Reader
let peer_role = function | Client -> Server | Server -> Client
val role_of: i:Idx.id -> role

let tls_get_role (#r:HS.rid) (s:tls_state r) (h:HS.mem) =
  get_role (tls_get_configT (tls_deref s h))

(**
Plaintext interface, part of AppPlain.fsti that
must be implemented by the application.

Alternatively, we could parametrize plaintext
at instanciation (as we do internally in quic_model)
but this complicates extraction significantly.
**)

type eid : Type0 = G.erased (Idx.id)
type app_fragment (*i:Idx.id*) = s:S.seq UInt8.t {
  S.length s <= TLSConstants.max_TLSPlaintext_fragment_length }
type plen = x:UInt32.t{UInt32.v x <= TLSConstants.max_TLSPlaintext_fragment_length}

// In implementation for extraction: LB.buffer UInt8.t
// We are forced to erase the index manually
val plain: eid -> plen -> t:Type0

// For liveness ... annoying
val plain_pred: #i:eid -> #l:plen -> p:plain i l -> m:HS.mem -> Type0

val ghost_repr: #i:eid -> #l:plen -> p:plain i l
  -> GTot (f:app_fragment (*G.reveal i*){S.length f == UInt32.v l})

// The whole AEAD stack should be parametric, e.g.
// AEADPlain.create -> StAEPlain.create -> DataStream.create
// -> AppPlain.plain_create inside AEAD.decrypt

// If we had a higher-order parametrization this could
// be implemented as a blit rather than an allocation+copy
val plain_create: i:eid -> l:plen -> ST.ST (plain i l)
  (requires fun h0 -> b2t F.ideal_AEAD /\ Idx.honest (G.reveal i))
  (ensures fun h0 p h1 -> plain_pred p h1)

// Is this identity or a copy?
val plain_coerce: i:eid -> l:plen ->
  v: LB.buffer UInt8.t -> ST.ST (plain i l)
  (requires fun h0 -> UInt32.v l <= LB.length v /\ (~(b2t F.ideal_AEAD) \/ Idx.corrupt (G.reveal i)))
  (ensures fun h0 p h1 -> plain_pred p h1)

// Discussion: safety
// ------------------
// In previous versions we used to separate
// safeId i and authId i. Since the new version
// of this interface is based on AEAD, it is very
// difficult to separate the two, unless we expose
// the deep internals of the AEAD security proof.
// Even then, we currently require an indeal PRF
// before idealizing the MAC, as we are keying the
// UFCMA game with the first block of the PRF.
// In the AEAD setting, safeId guarantees both
// confidentiality and integrity of plaintexts.

(**
Main AEAD safety predicate
**)
val safeId: i:Idx.id -> t:Type0{t ==> F.model}
val is_safeId: i:Idx.id -> ST.ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 ->
    M.modifies M.loc_none h0 h1 /\
    (b ==> safeId i))

// Discussion: epoch log
// ----------------------
// The stateful epoch_log function is somewhat cumbersome
// An alternaive approach that we consider is to
// pre-compute the expected index sequence from the
// authenticated mode. There are technical problems
// with this method - for instance, the fact that the
// computed indexes would not yet be registered.
// It may be possible to use provide security for the
// top-level interface against a weaker attacker model
// and offer a coarse-grained notion of honesty - for 
// instance, connection-level honnesty (possibly, up to
// a compromise point if we want to capture forward
// secrecy).

(**
The epoch log of a connection is simply a sequence
of indexes (under-specified).
**)
//val writer_epoch_log: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
//  GTot (S.seq Idx.id)
//let writer_epoch_log #r (s:tls_state r) h : GTot (list Idx.id) =
//  L.map (fun (| i, _ |) -> i) (writer_log s h)
val epoch_log: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
  GTot (S.seq Idx.id)


// Discussion: Writer log
// ----------------------
// There are many ways to specify stream security.
// In previous attempts, we have tried to write
// duplex stream models, but this does not work
// well with 0-RTT and one-sided re-keying. Instead,
// in the spirit of the MultiStrea.AE.fsti draft,
// and in contrast to the current design of Epoch.fst, 
// we use a ghost log of byte sequences to specify
// the writer log, and a counter value to specify
// the position of the reader in the writer log.
//
// In order to model the fact that some keys can
// be installed before they are activated, the
// sequence of epochs is separated from the sequence
// of fragments. Note that the fragments are no longer
// indexed (in contrast to previous attempts). It used
// to be the case because the ghost logged values were
// at the same type as the concrete arguments of read
// and write. In the buffer world, we need secure/abstract
// indexed buffers in the read/write interface, but their
// value can be specified in terms of seq U8.t.
//
// An interesting problem for the top-level API is how
// much to reveal to the application about the internal
// handshake epoch, and the associated internal fragments.
// Since we are not currently trying to prove any 
// confidentiality or integrity of handshake message fragments,
// I am tempted to completely hide the handshake epoch to the
// application. However, Cedric points out that we can no longer
// prove the integrity of remote errors during the handshake -
// a property that is very marginally useful for typical apps.
//
// Currently, writer_log remains a function of the connection.
// I experimented with a style where the writer_log is an
// under-specified function of any index. However, this
// made it very difficult for applications to prove that
// operations on a connection do not affect the writer_log of
// indexes outside the epoch_log of the connection. Proving this
// requires detailed knowledge of the global stateful invariant,
// and the style does not tolerate multiple corrupt connections
// that end up using the same index.

(**
Tries to find a connection that contains a writer
epoch at index i and returns a filter of its log,
only keeping application data fragments. Returns
an empty sequence if no connection defines a writer
at index i.
**)
val writer_log: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
  Ghost (S.seq (S.seq app_fragment)) (requires True)
  (ensures fun l -> S.length l <= S.length (epoch_log s h))

type not_plaintext #r (s:tls_state r) h =
  S.length (writer_log s h) > 0

(**
Read the log for index i (underspecified).
Returns Seq.empty if i is not an installed index
or of it is not enabled yet.
**)
let writer_epoch_log #r (s:tls_state r) (i:Idx.id) h
  : GTot (S.seq app_fragment)
  =
  let epochs = epoch_log s h in
  let log = writer_log s h in
  if S.length epochs = 0 then S.empty else
  let rec aux (j:nat) : GTot (S.seq app_fragment)
    (decreases (S.length epochs - j)) =
    if j >= S.length epochs then S.empty else
      if S.index epochs j = i then
        (if j < S.length log then S.index log j
	else S.empty)
      else aux (j+1) in
  aux 0

(* Older attempt when log is (i:Idx.id & S.seq (app_fragment i))
let writer_epoch_log #r (s:tls_state r) i h
  : GTot (S.seq app_fragment) =
  match S.find_l (fun j->j=i) (epoch_log s h) with
  | Some (i, _) -> True
  | _ -> Seq.empty
*)

//ADL: I spent some time trying a connection-independent
// writer log definition - this causes a lot of problems
// because of the universal quantification of connections
// when framing the writer_log. 
//val writer_log: i:Idx.id{safeId i} -> h:HS.mem -> GTot (S.seq (app_fragment i))

(**
We do not reveal the monotonic reference that stores
the log - instead we must re-expose the monotonicity
abstractly
**)
val lemma_frame_writer_log: #r:HS.rid -> s:tls_state r ->
  h0:HS.mem -> l:M.loc -> h1:HS.mem -> Lemma
  (requires M.modifies l h0 h1 /\
    M.loc_disjoint l (M.loc_region_only true r))
  (ensures writer_log s h0 == writer_log s h1 /\
    epoch_log s h0 == epoch_log s h1)

(**
Returns the index of the key for the
other direction of communication
**)
val peerId: i:Idx.id -> Ghost Idx.id (requires True)
  (ensures fun j -> role_of j == peer_role (role_of i))

val lemma_peerId_idempotent: i:Idx.id ->
  Lemma (peerId (peerId i) == i)
  [SMTPat (peerId (peerId i))]

(*
val find_peer_writer: i:Idx.id -> h:HS.mem ->
  Ghost (option (r:HS.rid & c:tls_state r))
  (requires tls_global_invariant h)
  (ensures fun ow ->
    (match ow with
    | None -> True
    | Some (|r, s|) -> S.mem i (epoch_log s h)))
*)

(**
The sequence of epochs contains keys that
have been generated but not enabled yet.
The last entry in the writer_log defines
the currently active writer index
**)
let currentId (#r:HS.rid) (s:tls_state r) (h:HS.mem)
  : Ghost Idx.id 
  (requires F.model /\ not_plaintext s h)
  (ensures fun i -> S.mem i (epoch_log s h)) =
  let j = S.length (writer_log s h) - 1 in
  S.index (epoch_log s h) j

// N.B. requires F.model because of peerId.
// If the "if model" is moved to the index type,
// it may be possible to specify this function for
// any index (see wiki notes)

(**
The ideal state of a reader is the position
of the last received message in the writer log
(for reliable stream)
**)
val reader_counter: #r:HS.rid -> s:tls_state r -> i:Idx.id -> h:HS.mem -> Ghost nat
  (requires F.model /\ S.mem (peerId i) (epoch_log s h))
  (ensures fun _ -> True)

(*
  (requires tls_global_invariant h)
  (ensures fun on ->
    (match on with
    | None -> True
    | Some n ->
      let opeer = find_peer_writer i h in
      Some? opeer /\
      n < S.length (writer_epoch_log
        (dsnd (Some?.v opeer)) (peerId i) h)))
*)

// Discussion: authentication
// --------------------------
// For the application, the main outcome of handshake
// completion is (conditional) mode authentication.
// For Low* reasons (and also, for callback reasons
// related to certificates) the concrete mode is
// a noeq type -- however, there exists a pure specification
// of it that defines mode equality.
//
// We need separate variants of authentication for the finished
// (mode authentication) and binders (offer authentication),
// which is why the types are duplicated.

(** Value spec of offer / mode **)
val earlyInfoT: eqtype
val conInfoT: eqtype
// include QD.Parse_clientHello
// include Negotiation.Spec

(** Low-level type of connection info, defined in API **)
val earlyInfo: Type0
val earlyInfo_repr: earlyInfo -> GTot earlyInfoT
val conInfo: Type0
val conInfo_repr: conInfo -> GTot conInfoT
// include TLSInfo

(**
Witness of the negotiation state defining
offer and mode - required for accessing
get_info and get_early_info
**)
val early_complete: #r:HS.rid -> s:tls_state r -> t:Type0
val complete: #r:HS.rid -> s:tls_state r -> t:Type0

val get_early_info: #r:HS.rid -> s:tls_state r ->
  Ghost earlyInfoT (requires early_complete s) (ensures fun _ -> True)

val get_info: #r:HS.rid -> s:tls_state r ->
  Ghost conInfoT (requires complete s) (ensures fun _ -> True)

// Safety predicate for negotiation security
val safeEarlyMode: earlyInfoT -> Type0
val safeMode: conInfoT -> Type0

val tls_get_early_info: #r:HS.rid -> s:tls_state r ->
  ST.ST earlyInfo
  (requires fun h0 -> early_complete s /\ tls_invariant s h0)
  (ensures fun h0 si h1 ->
    M.modifies M.loc_none h0 h1 /\
    earlyInfo_repr si == get_early_info s /\
    tls_invariant s h1)

val tls_get_info: #r:HS.rid -> s:tls_state r ->
  ST.ST conInfo
  (requires fun h0 -> complete s /\ tls_invariant s h0)
  (ensures fun h0 si h1 ->
    M.modifies M.loc_none h0 h1 /\
    conInfo_repr si == get_info s /\
    tls_invariant s h1)

val is_safeMode: #r:HS.rid -> s:tls_state r -> ST.ST bool
  (requires fun h0 -> complete s)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b ==> safeMode (get_info s)))
val is_safeEarlyMode: #r:HS.rid -> s:tls_state r -> ST.ST bool
  (requires fun h0 -> early_complete s)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b ==> safeEarlyMode (get_early_info s)))


(**
Ghost access to the peer connection object requires:
  1. the global TLS invariant
  2. a witnessed authentication predicate
**)
val get_peer: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
  Ghost (r':HS.rid & tls_state r')
  (requires tls_global_invariant h /\
    ((early_complete s /\ safeEarlyMode (get_early_info s))
     \/ (complete s /\ safeMode (get_info s))))
  (ensures fun (| _, s' |) ->
    (early_complete s ==> 
      (early_complete s' /\ get_early_info s' = get_early_info s)) /\
    (complete s ==>
      (complete s' /\ get_info s' = get_info s)))

(**
Initialization of the library.
**)
val tls_init: unit ->
  ST.ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 ->
    M.modifies (M.loc_region_only true tls_global_region) h0 h1 /\
    (b ==> tls_global_invariant h1))

(**
Allocates a new connection state and returns
a pointer to it, or NULL if the allocation failed

FIXME(adl) for now I return an option to avoid
dealing with the NULL case in the type of tls_state
**)
val tls_create: r:HS.rid -> cfg:config ->
  ST.ST (option (tls_state r))
  (requires fun h0 -> tls_global_invariant h0)
  (ensures fun h0 out h1 ->
    match out with
    | None -> M.modifies M.loc_none h0 h1
    | Some p ->
      M.modifies (tls_footprint p) h0 h1 /\
      tls_invariant p h1 /\
      tls_get_stm p h1 == InHandshake /\
      epoch_log p h1 == S.empty /\
      writer_log p h1 == S.empty /\
      IB.frameOf p == r /\
      tls_get_configT (tls_deref p h1) == cfg)

(**
Get detailed error information
**)
val tls_get_error: #r:HS.rid -> p:tls_state r ->
  ST.ST (UInt16.t * string)
  (requires fun h0 -> tls_invariant p h0 /\ 
    tls_get_stm p h0 == InError)
  (ensures fun h0 _ h1 -> M.modifies M.loc_none h0 h1)

(**
Free the state of a connection. This invalidates the
connection invariant but preserves the TLS global one
**)
val tls_free: #r:HS.rid -> p:tls_state r ->
  ST.ST unit
  (requires fun h0 -> tls_invariant p h0)
  (ensures fun h0 _ h1 ->
    M.modifies (tls_footprint p) h0 h1 /\
    tls_global_invariant h1)

(** Information about handshke progress returned to application **)
type tls_hsresult =
  | HS_Blocked            // Waiting for more input data or output space
  | HS_LocalError         // An error was generated locally and should be reported to peer
  | HS_RemoteError        // Handshake failed due to remote error
  | HS_EarlyDataReady     // Can write (client) or read (server) early data
  | HS_EarlyDataRejected  // 0-RTT data has been rejected
  | HS_Complete           // Handshake is complete

(**
Function to make progress in the handshake by
processing input data and producing output data to
sent to the peer.
**)
val tls_do_handshake: #r:HS.rid -> p:tls_state r ->
  input:uint8_p -> in_len:uint32_p ->
  output:uint8_p -> out_len:uint32_p ->
  ST.ST (tls_hsresult)
  (requires fun h0 ->
    tls_invariant p h0 /\
    LB.live h0 input /\ LB.live h0 output /\
    LB.live h0 in_len /\ LB.live h0 out_len /\
    UInt32.v (LB.get h0 in_len 0) <= LB.length input /\
    UInt32.v (LB.get h0 out_len 0) <= LB.length output /\
    tls_get_stm p h0 == InHandshake)
  (ensures fun h0 r h1 ->
    let s = tls_deref p h1 in
    let l = [M.loc_buffer output;
      M.loc_buffer in_len;
      M.loc_buffer out_len;
      tls_footprint p] in
    let stm = tls_get_stm p h0 in
    let stm' = tls_get_stm p h1 in
    let inl = UInt32.v (LB.get h0 in_len 0) in
    let inl' = UInt32.v (LB.get h1 in_len 0) in
    let outl' = UInt32.v (LB.get h1 out_len 0) in
    let role = get_role (tls_get_configT s) in
    M.modifies (loc_of_list l) h0 h1 /\
    tls_invariant p h1 /\
    inl' <= inl /\
    outl' <= LB.length output /\
    (match r with
    | HS_EarlyDataRejected -> stm' == stm /\
//      F.model /\ role == Server ==>
//        writer_log p h1 == S.snoc (writer_log p h0) S.empty
      (F.model /\ role == Client ==>
        writer_log p h1 == S.empty)
    | HS_Blocked -> stm' == stm
    | HS_Complete -> complete p /\
      not_plaintext p h1 /\
      stm' == HandshakeComplete /\
      (safeMode (get_info p) ==>
        (let (| _, p'|) = get_peer p h1 in
	get_info p' = get_info p)) /\
      (F.model ==>
        (let i = currentId p h1 in
	epoch_log p h1 == S.snoc (epoch_log p h0) i /\
	safeId i ==>
	  (reader_counter p (peerId i) h1 == 0 /\
          writer_log p h1 == S.snoc (writer_log p h0) S.empty)))
    | HS_EarlyDataReady -> not_plaintext p h1 /\
      F.model ==> (
        let i = currentId p h1 in
        epoch_log p h1 == S.snoc (epoch_log p h0) i /\
        (safeId i ==> (
          writer_log p h1 == S.snoc (writer_log p h0) S.empty /\
	  reader_counter p (peerId i) h1 == 0)) /\
        (match role with
        | Client -> stm' == InHandshakeWritable
        | Server -> early_complete p /\
	  stm' == InHandshakeReadable /\
	  (safeEarlyMode (get_early_info p) ==>
	    (let (| _, p' |) = get_peer p h1 in
	    get_early_info p' = get_early_info p))))
    | HS_LocalError
    | HS_RemoteError -> stm' == InError
  ))

noeq type tls_iresult =
  | R_Error
  | R_Blocked
  | R_Fragment: i:eid -> l:plen -> plain i l -> tls_iresult
  | R_KeyUpdate: bool -> tls_iresult
  | R_Closed
// | R_CantRead // Alternatively, dynamically fail if not readable

type authCon (#r:HS.rid) (p:tls_state r) =
  (early_complete p /\ safeEarlyMode (get_early_info p))
  \/ (complete p /\ safeMode (get_info p))

val tls_read: #r:HS.rid -> p:tls_state r ->
  input:uint8_p -> in_len:uint32_p ->
  output:uint8_p -> out_len:uint32_p ->
  ST.ST (tls_iresult)
  (requires fun h0 ->
    tls_invariant p h0 /\
    not_plaintext p h0 /\
    LB.live h0 input /\ LB.live h0 output /\
    LB.live h0 in_len /\ LB.live h0 out_len /\
    UInt32.v (LB.get h0 in_len 0) <= LB.length input /\
    UInt32.v (LB.get h0 out_len 0) <= LB.length output /\
    // Or, allow function call but return R_CantRead
    // auth p \/ early_auth p is required to ensure that
    // there exists a unique peer writer
    (match tls_get_stm p h0 with
    | InHandshakeReadable -> early_complete p
    | HandshakeComplete
    | LocalClosed -> complete p
    | _ -> False))
  (ensures fun h0 r h1 ->
    let s = tls_deref p h1 in
    let l = [ M.loc_buffer in_len;
      M.loc_buffer output; M.loc_buffer out_len;
      tls_footprint p] in
    let stm = tls_get_stm p h0 in
    let stm' = tls_get_stm p h1 in
    let inl = UInt32.v (LB.get h0 in_len 0) in
    let inl' = UInt32.v (LB.get h1 in_len 0) in
    let outl = UInt32.v (LB.get h0 out_len 0) in
    let outl' = UInt32.v (LB.get h1 out_len 0) in    
    let role = get_role (tls_get_configT s) in
    M.modifies (loc_of_list l) h0 h1 /\
    tls_invariant p h1 /\
    not_plaintext p h1 /\
    inl' <= inl /\ outl' <= outl /\
    writer_log p h0 == writer_log p h1 /\
    (not (R_KeyUpdate? r) ==> epoch_log p h0 == epoch_log p h1) /\
    (match r with
    | R_Blocked -> inl' == inl /\ stm' == stm
    | R_Error -> stm' == InError
    | R_KeyUpdate b -> stm' == stm
    | R_Fragment ei l f -> stm' = stm
    | R_Closed ->
      (match stm with
      | InHandshakeReadable ->
        stm' == InHandshake
      | HandshakeComplete ->
        stm' == RemoteClosed
      | LocalClosed ->
        stm' == FullClosed) /\
    (F.model ==>
      (let i = peerId (currentId p h0) in
      let i' = peerId (currentId p h1) in
      let ri = reader_counter p i h0 in
      let ri' = reader_counter p i' h1 in
      match r with
      | R_Blocked -> i' == i /\ ri == ri'
      | R_KeyUpdate b ->
        epoch_log p h0 == S.snoc (epoch_log p h1) i' /\
        ri' == 0 /\
	((safeId i /\ authCon p) ==>
	  (let (| r', p' |) = get_peer p h0 in
            ri == S.length (writer_epoch_log p' i h0))) /\
	(b /\ safeId i' ==>
	  (writer_log p h1 == S.snoc (writer_log p h0) S.empty))
      | R_Fragment ei l f ->
        G.reveal ei == i /\
        ((safeId i /\ authCon p) ==>
          (let fb = ghost_repr f in
	  let (| r', p' |) = get_peer p h1 in
	  // Alternatively, this could be folded into the
	  // definition of reader_counter
          ri < S.length (writer_epoch_log p' i h1) /\
          i' == i /\ ri' == ri + 1 /\
          S.index (writer_epoch_log p' i h1) ri == fb))
      | R_Closed ->
        (safeId i /\ authCon p) ==>
	  (let (| _, p' |) = get_peer p h1 in
	  S.length (writer_epoch_log p' i h0) == ri)
      | _ -> True))
  ))

type tls_oresult =
  | W_Error
  | W_Blocked
  | W_Success
// | W_CantWrite // Alternatively, dynamically fail if con not writable

#set-options "--z3rlimit 20"
val tls_write: #r:HS.rid -> p:tls_state r ->
  #ei:G.erased (Idx.id) -> #l:plen -> f:plain ei l ->
  output:uint8_p -> out_len:uint32_p ->
  ST.ST (tls_oresult)
  (requires fun h0 ->
    tls_invariant p h0 /\ not_plaintext p h0 /\
    (F.model ==> currentId p h0 == G.reveal ei) /\
    LB.live h0 output /\ LB.live h0 out_len /\
    UInt32.v (LB.get h0 out_len 0) <= LB.length output /\
    (match tls_get_stm p h0 with
    | InHandshakeWritable
    | HandshakeComplete
    | RemoteClosed -> True
    | _ -> False))
  (ensures fun h0 r h1 ->
    let s = tls_deref p h1 in
    let l = [ M.loc_buffer output;
      M.loc_buffer out_len; tls_footprint p] in
    let stm = tls_get_stm p h0 in
    let stm' = tls_get_stm p h1 in
    let outl' = UInt32.v (LB.get h1 out_len 0) in    
    M.modifies (loc_of_list l) h0 h1 /\
    tls_invariant p h1 /\
    not_plaintext p h1 /\
    outl' <= LB.length output /\
    epoch_log p h1 == epoch_log p h0 /\
    (~(W_Success? r /\ F.model) ==>
      writer_log p h1 == writer_log p h0) /\
    (match r with
    | W_Error -> stm' == InError
    | W_Blocked -> stm' == stm
    | W_Success -> stm' == stm /\
      (F.model ==>
        (let log0 = writer_log p h0 in
	let cur0 = S.last log0 in
	writer_log p h1 == S.upd log0 (S.length log0 - 1)
	  (S.snoc cur0 (ghost_repr f))))
  ))

val tls_rekey: #r:HS.rid -> p:tls_state r -> b:bool ->
  output:uint8_p -> out_len:uint32_p ->
  ST.ST (tls_oresult)
  (requires fun h0 ->
    tls_invariant p h0 /\ not_plaintext p h0 /\
    LB.live h0 output /\ LB.live h0 out_len /\
    UInt32.v (LB.get h0 out_len 0) <= LB.length output /\
    tls_get_stm p h0 == HandshakeComplete)
  (ensures fun h0 r h1 ->
    let s = tls_deref p h1 in
    let l = [ M.loc_buffer output;
      M.loc_buffer out_len; tls_footprint p] in
    let stm = tls_get_stm p h0 in
    let stm' = tls_get_stm p h1 in
    let outl' = UInt32.v (LB.get h1 out_len 0) in    
    M.modifies (loc_of_list l) h0 h1 /\
    tls_invariant p h1 /\
    not_plaintext p h1 /\
    outl' <= LB.length output /\
    (match r with
    | W_Error -> stm' == InError
    | W_Blocked -> False
    | W_Success -> stm' == stm /\
      (F.model ==>
        (let log0 = writer_log p h0 in
	let i' = currentId p h1 in
	epoch_log p h1 == S.snoc (epoch_log p h0) i' /\
	writer_log p h1 == S.snoc log0 S.empty))
  ))

val tls_close: #r:HS.rid -> p:tls_state r ->
  output:uint8_p -> out_len:uint32_p ->
  ST.ST (tls_oresult)
  (requires fun h0 ->
    tls_invariant p h0 /\ not_plaintext p h0 /\
    LB.live h0 output /\ LB.live h0 out_len /\
    UInt32.v (LB.get h0 out_len 0) <= LB.length output /\
    // Alternatively, allow the call but return W_CantWrite
    (match tls_get_stm p h0 with
    | InHandshakeWritable | HandshakeComplete
    | RemoteClosed -> True | _ -> False))
  (ensures fun h0 r h1 ->
    let s = tls_deref p h1 in
    let l = [ M.loc_buffer output;
      M.loc_buffer out_len; tls_footprint p] in
    let stm = tls_get_stm p h0 in
    let stm' = tls_get_stm p h1 in
    let outl' = UInt32.v (LB.get h1 out_len 0) in    
    M.modifies (loc_of_list l) h0 h1 /\
    tls_invariant p h1 /\
    not_plaintext p h1 /\
    outl' <= LB.length output /\
    epoch_log p h1 == epoch_log p h0 /\
    writer_log p h1 == writer_log p h0 /\
    (match r with
    | W_Error -> stm' == InError
    | W_Blocked -> False //
    | W_Success ->
      (match stm with
      | InHandshakeWritable ->
        stm' == InHandshake // Sent EOED, not writable anymore
      | HandshakeComplete -> 
        stm' == LocalClosed // Sent close_notify
      | RemoteClosed ->
        stm' == FullClosed) // Both close_notify have been exchanged
  ))

(***** Test application *****)

open LowStar.BufferOps

#reset-options "--z3rlimit 40 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"

let test (ccfg:config{get_role ccfg = Client})
  (scfg:config{get_role scfg = Server})
  : ST.ST unit
  (requires fun h0 -> True)
  (ensures fun h0 () h1 -> True)
  =
  ST.push_frame ();
  let rc = ST.new_region HS.root in
  let rs = ST.new_region HS.root in
  let _ = assert(M.loc_disjoint (M.loc_region_only true rc) (M.loc_region_only true rs)) in
  let _ = assume(M.loc_disjoint (M.loc_region_only true rc) (M.loc_region_only true tls_global_region)) in
  let _ = assume(M.loc_disjoint (M.loc_region_only true rs) (M.loc_region_only true tls_global_region)) in
  let b = tls_init () in
  let r =
  match b with
  | false -> ()
  | true ->
  match tls_create rc ccfg with
  | None -> ()
  | Some c ->
  let h0 = ST.get() in
  match tls_create rs scfg with
  | None -> ()
  | Some s ->
    let h1 = ST.get() in
    lemma_frame_tls_invariant2 c h0 s h1;
    lemma_frame_tls_stm2 c h0 s h1;
    let cl = LB.alloca 65535ul 1ul in
    let sl = LB.alloca 65535ul 1ul in
    let cb = LB.alloca 0uy 65535ul in
    let sb = LB.alloca 0uy 65535ul in
    let cl0, sl0 = !*cl, !*sl in
    let h2 = ST.get () in
    lemma_frame_tls_invariant c h1 M.loc_none h2;
    lemma_frame_tls_stm c h1 M.loc_none h2;
    lemma_frame_tls_invariant s h1 M.loc_none h2;
    lemma_frame_tls_stm s h1 M.loc_none h2;
    (match tls_do_handshake c cb cl sb sl with
    | HS_EarlyDataReady ->
      let h3 = ST.get () in
      lemma_frame_tls_invariant2 s h2 c h3;
      lemma_frame_tls_stm2 s h2 c h3;
      let ei = G.hide (currentId c h3) in
      let cl' = UInt32.sub cl0 !*cl in
      let sl' = UInt32.sub sl0 !*sl in
      let cb = LB.sub cb !*cl cl' in
      cl.(0ul) <- cl'; sl.(0ul) <- sl';
      let early_data = LB.alloca 255uy 3ul in
      let f = plain_coerce ei 3ul early_data in
      let cl0, sl0 = !*cl, !*sl in
      let h4 = ST.get () in
      lemma_frame_tls_invariant c h3 M.loc_none h4;
      lemma_frame_tls_stm c h3 M.loc_none h4;
      (match tls_write c f sb sl with
      | W_Success -> ()
        (*
        let cl' = UInt32.sub cl0 !*cl in
        let cb = LB.sub cb !*cl cl' in
        cl.(0ul) <- cl';
        sl.(0ul) <- UInt32.sub sl0 !*sl;
	(match tls_do_handshake s sb sl cb cl with
	| HS_EarlyDataReady ->
	  assert(False)
	| _ -> ()) *)
      | _ -> ())
    | _ -> ())
  in ST.pop_frame()


