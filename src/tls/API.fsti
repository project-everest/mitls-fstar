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
let loc_of_region_list (x:list HS.rid) = normalize_term (M.loc_regions true (Set.as_set x))

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
val lemma_tls_s_local_inv: #r:HS.rid -> s:tls_s r ->
  h0:HS.mem -> l:M.loc -> h1:HS.mem -> Lemma
  (requires tls_s_local_inv s h0
    /\ M.loc_disjoint l (M.loc_region_only true r)
    /\ M.modifies l h0 h1)
  (ensures tls_s_local_inv s h1)

(**
Global region and global invariant (implemented as
as walk over the connection table, but kept abstract
in the interface)
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
val lemma_frame_tls_get_stm: #r:HS.rid -> s:tls_state r ->
  h0:HS.mem -> l:M.loc -> h1:HS.mem -> Lemma
  (requires M.loc_disjoint l (M.loc_region_only true r) /\ M.modifies l h0 h1)
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
val idx_role: i:Idx.id -> role
let tls_get_role (#r:HS.rid) (s:tls_state r) (h:HS.mem) =
  get_role (tls_get_configT (tls_deref s h))

let idx_role_rw (r:role) (rw:rw) =
  match r, rw with
  | Client, Writer -> Client
  | Client, Reader -> Server
  | Server, Writer -> Server
  | Server, Reader -> Client

val currentId: #r:HS.rid -> s:tls_state r -> rw:rw -> m:HS.mem ->
  Ghost Idx.id
  (requires (match tls_get_stm s m with
    | InError | InHandshake -> False
    | InHandshakeReadable -> rw == Reader
    | InHandshakeWritable -> rw == Writer
    | _ -> True))
  (ensures fun i -> idx_role i == idx_role_rw (tls_get_role s m) rw)

val peerId: i:Idx.id -> GTot (j:Idx.id {
  idx_role j == peer_role (idx_role i)})

(**
Plaintext interface, part of AppPlain.fsti that
must be implemented by the application.

Alternatively, we could parametrize plaintext
at instanciation (as we do internally in quic_model)
but this complicates extraction significantly.
**)

type eid : Type0 = G.erased (Idx.id)
type app_fragment (i:Idx.id) = S.seq UInt8.t
type plen = x:UInt32.t{UInt32.v x <= TLSConstants.max_TLSPlaintext_fragment_length}

// In implementation for extraction: LB.buffer UInt8.t
// We are forced to erase the index manually
val plain: eid -> plen -> t:Type0

// For liveness ... annoying
val plain_pred: #i:eid -> #l:plen -> p:plain i l -> m:HS.mem -> Type0

val ghost_repr: #i:eid -> #l:plen -> p:plain i l
  -> GTot (f:app_fragment (G.reveal i){S.length f == UInt32.v l})

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

let not_plaintext (#r:HS.rid) (s:tls_state r) (h:HS.mem) =
  match tls_get_stm s h with
  | InError | InHandshake -> False | _ -> True

val tls_writer_log: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
  Ghost (list (i:Idx.id & (S.seq (app_fragment i))))
  (requires F.model)
  (ensures fun log -> True)

let tls_writer_log_epoch (#r:HS.rid) (s:tls_state r)
  (i:Idx.id) (h:HS.mem)
  : Ghost (S.seq (app_fragment i))
  (requires F.model)
  (ensures fun _ -> True) =
  match L.find (fun (| i', _ |) -> i' = i) (tls_writer_log s h) with
  | None -> S.empty
  | Some (| _, log |) -> log

val tls_seqn: #r:HS.rid -> s:tls_state r -> rw:rw -> h:HS.mem ->
  Ghost nat
  (requires (match tls_get_stm s h with
    | InError | InHandshake -> False
    | InHandshakeReadable -> rw == Reader
    | InHandshakeWritable -> rw == Writer
    | _ -> True))
  (ensures fun seqn ->
    F.model ==> (
      let loglen = S.length (tls_writer_log_epoch s (currentId s rw h) h) in
      match rw with
      | Writer -> loglen == seqn
      | Reader -> loglen >= seqn))

// What is authenticated in a session,
// includes mode, identities (PSK, cert, nonce),
// session hash (binder)
val sessionInfoT: eqtype
val peer_sessionInfoT: sessionInfoT -> sessionInfoT
val lemma_peer_idempotent: s:sessionInfoT ->
  Lemma (peer_sessionInfoT (peer_sessionInfoT s) = s)

val sessionInfo: Type0
val sessionInfo_repr: sessionInfo -> GTot sessionInfoT

val tls_session_info: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
  Ghost sessionInfoT
  (requires tls_invariant s h /\ not_plaintext s h)
  (ensures fun si -> True)

val tls_get_session_info: #r:HS.rid -> s:tls_state r ->
  ST.ST sessionInfo
  (requires fun h0 -> tls_invariant s h0 /\ not_plaintext s h0)
  (ensures fun h0 si h1 ->
    M.modifies M.loc_none h0 h1 /\
    sessionInfo_repr si == tls_session_info s h0 /\
    tls_invariant s h1)

let tls_peered (#r1:HS.rid) (s1:tls_state r1)
  (#r2:HS.rid) (s2:tls_state r2) (h:HS.mem) : Ghost Type0
  (requires tls_invariant s1 h /\ tls_invariant s2 h /\
    not_plaintext s1 h /\ not_plaintext s2 h)
  (ensures fun _ -> True) =
  tls_session_info s1 h
    = peer_sessionInfoT (tls_session_info s2 h)

val auth: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
  Ghost Type0 (requires not_plaintext s h)
  (ensures fun auth -> auth ==> F.model)

val get_peer: #r:HS.rid -> s:tls_state r -> h:HS.mem ->
  Ghost (r':HS.rid & tls_state r')
  (requires not_plaintext s h /\ tls_invariant s h /\ auth s h)
  (ensures fun (|_, s'|) -> tls_invariant s' h /\
    not_plaintext s' h /\ tls_peered s s' h)

let not_plaintext_or_0rtt_client (#r:HS.rid) (s:tls_state r) (h:HS.mem) =
  match tls_get_stm s h with
  | InError | InHandshake | InHandshakeWritable -> False
  | _ -> True

(**
Initialization of the library.
**)
val init: unit ->
  ST.ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 ->
    M.modifies (M.loc_region_only true tls_global_region) h0 h1 /\
    b ==> tls_global_invariant h1)

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
      IB.frameOf p == r /\
      tls_get_configT (tls_deref p h1) == cfg)

(** Get detailed error information **)
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
    (match tls_get_stm p h0 with
    | InHandshake | InHandshakeWritable -> True
    | _ -> False))
  (ensures fun h0 r h1 ->
    let s = tls_deref p h1 in
    let l = [M.loc_buffer input; M.loc_buffer output;
      M.loc_buffer in_len; M.loc_buffer out_len;
      tls_footprint p] in
    let stm = tls_get_stm p h0 in
    let stm' = tls_get_stm p h1 in
    let inl = UInt32.v (LB.get h0 in_len 0) in
    let outl = UInt32.v (LB.get h0 out_len 0) in
    let inl' = UInt32.v (LB.get h1 in_len 0) in
    let outl' = UInt32.v (LB.get h1 out_len 0) in
    let role = get_role (tls_get_configT s) in
    M.modifies (loc_of_list l) h0 h1 /\
    tls_invariant p h1 /\
    (match r with
    | HS_EarlyDataRejected ->
      stm' == InHandshake // Can't write anymore
    | HS_Blocked ->
      stm' == stm /\ inl' < inl
    | HS_Complete ->
      stm' == HandshakeComplete /\
      auth p h1 ==> (
        let (|r', p'|) = get_peer p h1 in
	tls_session_info p h1
	 == peer_sessionInfoT (tls_session_info p' h1))
    | HS_EarlyDataReady ->
      (match role with
      | Client ->
        stm' == InHandshakeWritable
      | Server ->
        stm' == InHandshakeReadable)
    | HS_LocalError
    | HS_RemoteError ->
      stm' == InError
  ))

noeq type tls_iresult =
  | R_Blocked
  | R_Error
  | R_Fragment: i:eid -> l:plen -> plain i l -> tls_iresult
  | R_Closed

val tls_read: #r:HS.rid -> p:tls_state r ->
  input:uint8_p -> in_len:uint32_p ->
  ST.ST (tls_iresult)
  (requires fun h0 ->
    tls_invariant p h0 /\
    LB.live h0 input /\
    LB.live h0 in_len /\
    UInt32.v (LB.get h0 in_len 0) <= LB.length input /\
    (match tls_get_stm p h0 with
    | InHandshakeReadable | HandshakeComplete | LocalClosed -> True
    | _ -> False))
  (ensures fun h0 r h1 ->
    let s = tls_deref p h1 in
    let l = [M.loc_buffer input; M.loc_buffer in_len;
      tls_footprint p] in
    let stm = tls_get_stm p h0 in
    let stm' = tls_get_stm p h1 in
    let inl = UInt32.v (LB.get h0 in_len 0) in
    let inl' = UInt32.v (LB.get h1 in_len 0) in
    let role = get_role (tls_get_configT s) in
    let rctr = tls_seqn p Reader h0 in
    let rctr' = tls_seqn p Reader h1 in
    M.modifies (loc_of_list l) h0 h1 /\
    tls_invariant p h1 /\ inl' <= inl /\
    (match r with
    | R_Blocked ->
      inl' == inl /\ rctr == rctr' /\
      LB.as_seq h0 input == LB.as_seq h1 input
    | R_Error -> stm' == InError
    | R_Fragment ei l f -> stm' = stm /\
      auth p h0 ==>
        (let (|r', p'|) = get_peer p h1 in
	let i' = peerId (currentId p Reader h0) in
	let log = tls_writer_log_epoch p' i' h0 in
	S.index log rctr' == ghost_repr f
	/\ auth p h1)
    | R_Closed ->
      rctr' == rctr + 1 /\
      (match stm with
      | InHandshakeReadable ->
        stm' == InHandshake /\
	auth p h0 ==>
	  (let (| r', p'|) = get_peer p h0 in
	  rctr' == tls_seqn p' Writer h0)
      | HandshakeComplete ->
        stm' == RemoteClosed
      | LocalClosed ->
        stm' == FullClosed)
  ))


let test () : ML unit =
  let ccfg : config = magic() in
  assume(get_role ccfg = Client); 
  let scfg : config = magic () in
  assume(get_role scfg = Server);
  let rc = HS.new_region HS.root in
  let rs = HS.new_region HS.root in
  let cli = tls_create rc ccfg in
  let srv = tls_create rs scfg in
  match cli, srv with
  | Some c, Some s ->
    let cb = LB.alloca 0uy 16000ul in
    let sb = LB.alloca 0uy 16000ul in
    ()
  | _ -> ()

