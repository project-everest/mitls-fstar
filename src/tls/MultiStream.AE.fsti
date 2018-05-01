module MultiStream.AE

open Range // cwinter: module name clash with FStar.Range when referring to Range.*


(*! refactoring Epochs, with a narrower, more abstract
    interface. WIP. *)

// Consider switching to Low*? Intuitively is does not change much
// crypto modelling, which will remain based on ghost/ideal bytes.

/// Multistreams provide authenticated encryption with rekeying.
///
/// Although they are not TLS-specific, they provide the AE interface
/// for TLS record protection: each connection uses one multistream
/// for reading and one for writing; its handshake extends them with
/// fresh derived keys, and separately signals when to switch to the
/// next key.
/// 
/// Each multistream instance is specified
/// using two ghost monotonic views:
///
/// * a sequence of authenticated ghost bytes sent/received, grouped
///   by successive keys; no abstraction, no indexing, possibly no
///   need for range.
///
///   Logs grow either by appending an empty sequence (as we start
///   using the next key) or by appending a record in the last
///   sub-sequence (as we send/receive).
/// 
///   It seems convenient to have both reader and writer logs, but
///   that's a global choice.
/// 
///   The TLS API will specify a projection of that log.

// Use lists instead of sequences?
// Revert them for syntactic convenience? 

type ghost_record = (rg:range & b:Bytes.bytes{Bytes.length b <= snd rg})
type logs = Seq.seq (Seq.seq ghost_record) 

let empty_logs xs = Seq.for_all (fun x -> x == []) xs 
let rec extends_logs xs ys =
  let open FStar.Seq in 
  match length xs with 
  | 0 -> empty_logs ys
  | 1 -> head xs `prefix_of` head ys /\ empty_logs ys
  | _ -> head xs = head ys /\ extends_logs (tail xs) (tail ys)

// clarify ghost vs ideal for [logs]

/// * a sequence of StAE indexes, controlling idealization and plaintext
///   abstraction; since keys are added before being used, [idxs] is
///   at least as long as [logs]. It grows by appending StAE keys in
///   their initial state.
///
///   TLS will maintain an invariant relating these indexes to the
///   connection, enabling reasoning about their conditional safety.

type idxs = Seq.seq id 


noeq type t (role:rw) (* stateful, monotonic, intuitively indexed by [idxs] *)

// footprint
val region:   #role:rw -> x:t role -> rid 
val sel_logs: #role:rw -> x:t role -> mem -> logs 
val sel_idxs: #role:rw -> x:t role -> mem -> idxs

// TODO framing and monotonicity; clarify where AE states vs AE logs
// are allocated.

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



/// Internally, the state consists of
/// - a list of (| i, StAE role i |)
/// - a current integer index within the list (starting at -1)
/// 
/// The list *before* the current index is ghost.
// TODO extract [logs] and [idxs] from those.

/// Concretely, we only keep one current key and a few future
/// keys. This matters for forward secrecy.  We may statically bound
/// the number of live keys (3 for TLS?) so that future keys can be
/// stored in a small buffer.

/// registering a future key
val extend: #role:rw -> x:t role -> i:id -> k:StAE.t role -> ST unit 
  (requires fun h0 -> StAE.sel h0 k = [])
  (ensures fun h0 _ h1 -> 
    modifies_one h0 h1 (region x) /\
    sel_idxs h1 x == sel_idxs h0 x ++ i /\ 
    sel_logs h1 x == sel_logs h0 x)

/// ensuring local forward secrecy
val next: #role:rw -> x:t role -> i:id -> k:StAE.t role -> ST unit 
  (requires fun h0 -> 
    length (sel_logs h0 x) < length (sel_idxs h0 x))
  (ensures fun h0 _ h1 -> 
    modifies_one h0 h1 (region x) /\
    sel_idxs h1 x == sel_idxs h0 /\ 
    sel_logs h1 x == sel_logs h0 x ++ [])

val read: x: t Reader -> i: id -> ST (result (rg:Range.range & Plain.t i rg))
  (requires fun h0 -> 
    live h0 x /\
    sel_logs h0 x <> [] /\
    i = index (sel_idxs h0 x) (length (sel_logs h0 x) - 1))
  (ensures fun h0 r h1 -> 
    live h1 x /\ 
    modifies_one h0 h1 (region x) /\
    sel_idxs h1 x == sel_idxs h0 x /\
    (let l0 = sel_logs h0 x in 
     let l1 = sel_logs h1 x in 
     match r with 
     | Correct (| rg, p |) -> l1 == snoc2 l0 (Plain.v p)
     | Error _             -> l1 == l0))

val write: x: t Writer -> i: id -> rg: Range.range -> plain:Plain.t i rg -> ST (result cipher)
  (requires fun h0 -> 
    live h0 x /\ 
    sel_logs h0 x <> [] /\
    i = index (sel_idxs h0 x) (length (sel_logs h0 x) - 1))
  (ensures fun h0 r h1 -> 
    live h1 x /\ // although write errors should be fatal
    modifies_one h0 h1 (region x) /\
    sel_idxs h1 x == sel_idxs h0 x /\
    (let logs0 = sel_logs h0 x in 
     let logs1 = sel_logs h1 x in 
     let logs_correct = snoc2 (sel_logs h0 x) (Plain.v p) in 
     match r with 
     | Correct cipher -> logs1 == logs_correct 
     | Error _    -> logs1 == logs_correct \/ logs1 == logs0))

val create: role: rw -> r:rid -> ST (t role) 
  (requires fun h0 -> True)
  (ensures fun h0 x h1 -> 
    modifies_none h0 h1 /\ // to be adjusted
    live x /\ 
    fresh_subregion (region x) r /\ 
    sel_idxs h1 x == [] /\
    sel_logs h1 x == [])

/// scrubs and deallocates all concrete state
/// (formally leaving ghost state unchanged)
val free: #role: rw -> x:t role -> ST unit
  (requires fun h0 -> live h0 x)
  (ensures fun h0 r h1 -> 
    modifies_one h0 h1 (region x) /\
    sel_idxs h1 x == sel_idxs h0 x /\
    sel_logs h1 x == sel_logs h0 x)
    
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
