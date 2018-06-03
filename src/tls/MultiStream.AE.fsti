module MultiStream.AE

open Range // cwinter: module name clash with FStar.Range when referring to Range.*

let ( ++ ) = Seq.snoc


(*! refactoring Epochs, with a narrower, more abstract
    interface. WIP. *)

// Consider switching to Low*? Intuitively it would not affect much
// our crypto modelling, which will remain based on ghost/ideal bytes
// contents.

/// Multistreams provide authenticated encryption with rekeying.
///
/// Although they are not TLS-specific, they provide the AE interface
/// for TLS record protection: each connection uses one multistream
/// for reading and one for writing; its handshake extends them with
/// fresh derived keys, and separately signals when to switch to the
/// next key.
/// 
/// Each multistream instance is specified
/// using two ghost monotonic views
///
/// 1. A sequence of authenticated ghost bytes sent/received, grouped
///    by successive keys; no abstraction, no indexing, possibly no
///    need for range.
///
///   Logs grow either by appending an empty sequence (as we start
///   using the next key) or by appending a record in the last
///   sub-sequence (as we send/receive).
/// 
///   It seems convenient to have both reader and writer logs, but
///   that's a global choice.
/// 
///   The TLS API will specify a projection of that log.
// We still don't know what's most convenient for the receiver
// application. Going ahead with ghost abstract logs at both ends.
//
// HOW TO SYNCHRONIZE INDEXES? 

// We could abstractly require that the appended index be a stable
// function of the current state. Assuming 0RTT-rejecting servers know
// what index they are skipping.
//
// PARTIAL COMPROMISE? 
//
// Adaptive key-based model. Separate dynamic integrity from more
// static confidentiality? Difficulty: the indexes may get out of
// sync. Property: 1st successful decryption at a honest index
// guarantees synchronization.
//
// HOW TO MODEL STREAM & SUB-STREAM TERMINATION?
//
// Each multistream is parametrized by an application-defined sender
// update condition, both for appending to the current sub-stream and
// for switching to the next empty stream. (The preorder will require
// an explicit transitive closure.)
//
// At the receivers's, we can't locally enforce it as we decrypt: if
// the sender is corrupt, the receiver's current sub-stream may extend
// beyond terminators. In contrast, the receiver application enforces
// that key switches happen only when the current substream is
// terminated.
//
// Tricky cases: 
//
// * trial decryption, formally Ok as we decrypt only with the current
// * key.
//
// * rejected 0RTT. The server never installs the 0RTT key, and
//   instead immediately installs the next key. It will know that the
//   client has stopped 0RTT once it decrypts the first HS message,
//   but the gap between the two streams will persist.
//
// * out-of-order decryption for DTLS/QUIC. This will require a
// * generalized receiver API, with explicit erasure of old keys.
//
// A sub-stream is complete (stable, terminated) once the sender
// update condition disables any update.
//
// At the receiver, we give no such guarantee. 
// Instead, the receiver may deduce it from the stream contents.
// 
// The receiver application decides when to switch keys.
//
//
// Use lists instead of sequences? Note StreamAE uses FStar.Monotonic.Seq 
// Revert them for syntactic convenience? 
//
//
// How to prevent confusion between multiple instances? This will be
// required internally to prove framing etc. This is index-based, e.g.
// disjoint indexes between different connections, directions,
// position in stream.

type ghost_record = (rg:range & b:Bytes.bytes{Bytes.length b <= snd rg})

open FStar.Seq 

type log = seq ghost_record
type logs = seq log

// let empty_logs xs = Seq.for_all (fun x -> Seq.length x = 0 ) xs 

// Several properties to consider
// [Correctness]     Senders/receivers local updates are as specified in the pre/posts of encrypt, decrypt, switch,...
// [Integrity]       If the sender is honest, her state evolves according to a (parametric) update preorder.
// [Authenticity]    For each honest index, the sub-stream received is a prefix of the sub-stream sent. 
// [Confidentiality] IND for sub-stream contents sent at honest indexes 


let rec prefix (rs ws:log): Tot _ (decreases (length rs + length ws)) = 
  length rs = 0 \/ 
  (length ws > 0 /\ head rs == head ws /\ prefix (tail rs)(tail ws))

let rec empty_tail (rs:logs): Tot _ (decreases (length rs)) = 
  length rs = 0 \/ 
  (head rs == createEmpty /\ empty_tail (tail rs))

#set-options "--z3rlimit 100"
let rec prefixes (rs ws:logs): Tot _ (decreases (length rs + length ws)) =
  empty_tail rs \/ 
  (length rs > 0 /\ length ws > 0 /\ prefix (head rs) (head ws) /\ prefixes (tail rs) (tail ws))

// clarify ghost vs ideal for [logs]

/// ... and
/// 
/// * a sequence of StAE indexes, controlling idealization and plaintext
///   abstraction; since keys are added before being used, [idxs] is
///   at least as long as [logs]. It grows by appending StAE keys in
///   their initial state.
///
///   TLS will maintain an invariant relating these indexes to the
///   connection, enabling reasoning about their conditional safety.

type id = TLSInfo.id // for now, compatible with StAE
type rw = TLSConstants.rw 

type idxs = seq id

type t (role:rw) (* stateful, monotonic, intuitively indexed by [idxs] *)

let rec snoc2 (xs:logs{length xs > 0}) (r:ghost_record): Tot (xs':logs) (decreases (length xs)) =
  if length xs = 1 then create #log 1 (head #log xs ++ r) else cons (head xs) (snoc2 (tail xs) r)
  

// footprint
val region:   #role:rw -> x:t role -> HyperStack.rid  
val sel_logs: #role:rw -> x:t role -> HyperStack.mem -> logs 
val sel_idxs: #role:rw -> x:t role -> HyperStack.mem -> idxs

// TODO framing and monotonicity; clarify where AE states vs AE logs
// are allocated.

let empty_log: log = createEmpty 

/// We use multiple regions:
/// - one for local control (modified by installing or changing keys)
/// - one for local data (modified by reading or writing)
/// - one for writer data (for peer authentication)

/// For AEAD, we already had two regions:
/// - one for the PRF state (shared; hidden by the AEAD interface and invariant)
/// - one for the writer state (local to its connection)
///
/// For StreamAE, we need additional, concrete local state for both readers and writers.
/// 
/// Here, we use those local states, and additional concrete local
/// state for the installed keys.
///
/// The whole memory shape is recorded as a strong invariant (see epochs)
/// with a special case for remotely-allocated writers. 

open FStar.HyperStack.All

/// Internally, the state consists of
/// - a list of (| i, StAE role i |)
/// - a current integer index within the list (starting at -1, sadly)
/// 
/// The list of StAE instances *before* the current index is ghost.
// TODO extract [logs] and [idxs] from those.

/// Concretely, we only keep one current key and a few future
/// keys. This matters for forward secrecy.  We may statically bound
/// the number of live keys (3 for TLS?) so that future keys can be
/// stored in a small buffer, or use the current Handshake state.

/// registering a future key
val extend: #role:rw -> x:t role -> i:TLSInfo.id -> k:StAE.state i role -> ST unit 
  (requires fun h0 -> 
    // only on the sender side? 
    TLSConstants.Writer? role /\ TLSInfo.authId i ==> 
    length (StAE.fragments k h0) = 0)
  (ensures fun h0 _ h1 -> 
    HyperStack.modifies_one (region x) h0 h1 /\
    sel_idxs x h1 == sel_idxs x h0 ++ i /\ 
    sel_logs x h1 == sel_logs x h0)

/// ensuring local forward secrecy
val next: #role:rw -> x:t role -> i:id -> k:StAE.state i role -> ST unit 
  (requires fun h0 -> 
    length (sel_logs x h0) < length (sel_idxs x h0))
  (ensures fun h0 _ h1 -> 
    HyperStack.modifies_one (region x) h0 h1 /\
    sel_idxs x h1 == sel_idxs x h0 /\ 
    sel_logs x h1 == sel_logs x h0 ++ empty_log)

val read: x: t TLSConstants.Reader -> i: id -> ST (result (rg:Range.range & StreamPlain.plain i (admit())))
  (requires fun h0 -> 
    // live h0 x /\
    length (sel_logs x h0) <> 0 /\
    i = index (sel_idxs x h0) (length (sel_logs x h0) - 1))
  (ensures fun h0 r h1 -> 
    // live h1 x /\ 
    HyperStack.modifies_one (region x) h0 h1 /\
    sel_idxs x h1 == sel_idxs x h0 /\
    (let l0 = sel_logs x h0 in 
     let l1 = sel_logs x h1 in 
     match r with 
     | Error.Correct (| rg, p |) -> l1 == snoc2 l0 (StreamPlain.goodrepr p)
     | Error.Error _             -> l1 == l0
     ))

val write: x: t TLSConstants.Writer -> i: id -> rg: Range.range -> plain:StreamPlain.plain i (admit()) -> ST (result cipher)
  (requires fun h0 -> 
    live h0 x /\ 
    length (sel_logs x h0) > 0 /\
    i = index (sel_idxs x h0) (length (sel_logs x h0) - 1))
  (ensures fun h0 r h1 -> 
    // live h1 x /\ // although write errors should be fatal
    HyperStack.modifies_one (region x) h0 h1 /\
    sel_idxs x h1 == sel_idxs x h0 /\
    (let logs0 = sel_logs x h0 in 
     let logs1 = sel_logs x h1 in 
     let logs_correct = snoc2 (sel_logs x h0) (StreamPlain.v p) in 
     match r with 
     | Correct cipher -> logs1 == logs_correct 
     | Error _    -> logs1 == logs_correct \/ logs1 == logs0))

val create: role: rw -> r:rid -> ST (t role) 
  (requires fun h0 -> True)
  (ensures fun h0 x h1 -> 
    modifies_none h0 h1 /\ // to be adjusted
    live x /\ 
    fresh_subregion (region x) r /\ 
    length (sel_idxs x h1) = 0 /\
    length (sel_logs x h1) = 0)

/// scrubs and deallocates all concrete state
/// (formally leaving ghost state unchanged)
val free: #role: rw -> x:t role -> ST unit
  (requires fun h0 -> live h0 x)
  (ensures fun h0 r h1 -> 
    modifies_one (region x) h0 h1 /\
    sel_idxs x h1 == sel_idxs x h0 /\
    sel_logs x h1 == sel_logs x h0)
    
// what about closure and forward-secrecy for the last key? 
// we do not represent failure or termination (client-specific)

/// Multistream integrity as a stateful lemma:
///
/// 1. for each rw, sel_idxs are pairwise-distinct, *ordered*, and
///    associated with the enclosing connection (by its local nonce).
///
/// 2. for each i, authId i ==> the reader log is a prefix of the writer log
///
/// Shall we rely more explicitly on monotonicity?
/// Shall we have NULL streamAEs for uniformity? unclear. 
/// How to deal with the log type dependency? Record only the actual plaintexts!
///
/// Honest instances can be trusted to install keys in a synchronized
/// manner; for TLS, the indexes are clearly ordered, and the stream
/// contents are clearly terminated, hence the whole AppData
/// multi-stream is authenticated. (We may even get some duplex
/// correspondence properties.)


/// What are the consequences of droping duplex epochs?
///
/// At the TLS interface, the client knew it was getting the same
/// security in both directions, but that's not so useful, and
/// challenging to maintain with 0RTT. Separating the two will
/// simplify the "increment logic" between HS and TLS.
///
/// What about dropping the HS context? This is for the handshake to
/// maintain.
///
/// What about exporter keys? They are already ad hoc, can in
/// principle be separately stored in the HS state (rather than in
/// epochs).
///
/// Hopefully we can adapt the design above to QUIC. The main
/// difference is on the reader side: reads can occur out-of-order,
/// concurrently using multiple keys (but we probably still want to
/// retire old keys once key-change is acknowledged, to gain forward
/// secrecy).


/// TLS invariants?
///
/// - The handshake owns the sequence of registered indexes and the
///   current record index; it precisely tracks their state as part of
///   its invariant, itself cryptographically authenticated by signing
///   and finishing.
///
/// - The handshake *never* reads or writes StAE instances.
///   Who increments? Unclear how to use regions for this.
///   Recall that TLS should not be exposed to the key schedule.
///
/// - The ability to carry application data is a TLS-specific property
///   of the index.
///
/// - Stream termination is also a TLS-specific property: TLS writers
///   never write after a terminator.
///
/// - The top-level API simply filters out HS traffic and signals from
///   the logs. For instance, as the client completes the handshake
///   its state is
///
///             Reader [ []; [] ]    Writer: [ log0; []; [] ]
///
///   (We may also record some handshake details in the log,
///   such as the CertificateRequest and Certificate messages).
///
/// We may also record handshake completions as special events
///   in the log, e.g. Reader
///
///   By convention, refused 0RTT is represented as an empty 0RTT stream,
///   and absent 0RTT as one fewer client stream.
/// 
