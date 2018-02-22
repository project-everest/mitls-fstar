module MultiStream.AE

(*! refactoring Epochs, with a narrower, more abstract
    interface. WIP. *)


type ghost_record = (rg:Range.range & b:bytes{Bytes.length b <= snd rg})

/// To avoid dependent lists, the log records concrete bytes;
/// we may also record parsed records.

type logs = Seq.seq (Seq.seq ghost_record) 
type idxs = Seq.seq id 

// use sequences or lists? 

/// Indexes grow adding fresh StAE instances.
/// 
/// Logs grow either by adding an empty sequence, or by extending
///
/// register: xs ~> xs ++ [] 
/// install:  

let empty_logs xs = Seq.forall (fun x -> x == []) xs 
  
let rec extends_logs xs ys = 
  if Seq.length xs = 0 then empty_logs ys
  else if Seq.length xs > 1 then 

  Seq.length xs <= Seq.length ys /\


  if Seq.length xs > 1 
  then Seq.head xs = Seq.head ys /\ extends_log (Seq.tail xs) (Seq.tail ys) 
  else if Seq.length

  if Seq.length xs > 1 then 
  Seq.length ys 
  Seq.head 
  
  if Seq.length xs = 1 then 
    Seq.length ys >= 1 /\
    Seq.prefix xs (Seq.head ys) /\
    Seq.forall 


  match v0, v1 with 
  | x::v 


val region: #role:rw -> x:t role -> rid 
val sel_logs: mem -> #role:rw -> x:t role -> logs 
val sel_idxs: mem -> #role:rw -> x:t role -> indexes

// TODO framing and monotonicity; clarify where AE states vs AE logs are allocated. 



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

// - region x is the footprint for all writing of allthe reregion is the footprint for both  logs and indexes 



/// We could statically bound the difference of the two lengths,
/// i.e. the number of live keys (3 for TLS), so that the concrete
/// state may be represented as a buffer of keys.

type t (role:rw) (* stateful, monotonic *)

/// The state consists of
/// - a list of (| i, StAE role i |)
/// - a current index within the list (starting at -1)
/// 
/// The list *before* the current index is ghost.

/// The concrete state consists of sequence of (i: id & StreamAE role i ) 

val extend: #role:rw -> x:t role -> i:id -> k:StAE.t role -> ST unit 
  (requires fun h0 -> StAE.sel h0 k = [])
  (ensures fun h0 _ h1 -> 
    modifies_one h0 h1 (region x) /\
    sel_idxs h1 x == sel_idxs h0 x ++ i /\ 
    sel_logs h1 x == sel_logs h0 x)

/// guaranteeing local forward secrecy
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
    let l0 = sel_logs h0 x in 
    let l1 = sel_logs h1 x in 
    match r with 
    | Correct (| rg, p |) -> l1 == snoc2 l0 (Plain.v p)
    | Error _             -> l1 == l0 )

val write: x: t Writer -> i: id -> rg: Range.range -> plain:Plain.t i rg -> ST (result cipher)
  (requires fun h0 -> 
    live h0 x /\ 
    sel_logs h0 x <> [] /\
    i = index (sel_idxs h0 x) (length (sel_logs h0 x) - 1))
  (ensures fun h0 r h1 -> 
    live h1 x /\ // although write errors should be fatal
    modifies_one h0 h1 (region x) /\
    sel_idxs h1 x == sel_idxs h0 x /\
    let logs0 = sel_logs h0 x in 
    let logs1 = sel_logs h1 x in 
    let logs_correct = snoc2 (sel_logs h0 x) (Plain.v p) in 
    match r with 
    | Correct cipher -> logs1 == logs_correct 
    | Error _    -> logs1 == logs_correct \/ logs1 == logs0)

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

// it seems convenient to use the same ghost state for readers and writers.

/// Integrity as a stateful lemma:
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
/// Consider immediately switching to Low* ?

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
