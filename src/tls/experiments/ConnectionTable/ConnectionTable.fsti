module ConnectionTable

open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

open ConnectionTable_Aux

noeq
type connection =
  | Init: cfg:configuration -> connection
  | Sent_HRR: random:UInt32.t -> ch:client_hello -> connection
  | Sent_ServerHello: random:UInt32.t -> ch:client_hello -> id1:connection_id -> connection
  | Complete: random:UInt32.t -> ch:client_hello -> id1:connection_id -> connection

let nonce_of (c:connection{~(Init? c)}) =
  match c with
  | Sent_HRR r _ | Sent_ServerHello r _ _ | Complete r _ _ -> r

let step (s1 s2:connection) : Type0 =
  match s1, s2 with
  | Init _, Sent_HRR _ _ -> True
  | Init _, Sent_ServerHello _ _ _ -> True
  | Sent_ServerHello r ch id1, Complete r' ch' id1' -> r == r' /\ ch == ch' /\ id1 == id1'
  | _, _ -> False

let rel : Preorder.preorder connection = closure step

let connection_ref (id:connection_id) = r:mmmref connection rel{frameOf r `extends` rgn}

val minv: partial_dependent_map connection_id connection_ref -> Type0

let connection_table = t rgn connection_id connection_ref minv

inline_for_extraction noextract
val empty: m:imap connection_id connection_ref minv{m == T.empty}

val inv: connection_table -> mem -> Type0

val alloc: unit -> ST (connection_table)
  (requires fun _ -> witnessed (region_contains_pred rgn))
  (ensures  fun h0 t h1 -> ralloc_post rgn empty h0 t h1 /\ inv t h1)

val create:
    t:connection_table
  -> id:connection_id
  -> cfg:configuration
  -> ST (connection_ref id)
  (requires fun h0 ->
    inv t h0 /\ ~(T.defined t id h0))
  (ensures  fun h0 c h1 ->
    inv t h1 /\
    mods [Ref t] h0 h1 /\
    T.defined t id h1 /\
    sel h1 t == T.upd (sel h0 t) id c /\
    ~(h0 `contains` c) /\
    h1 `contains` c /\
    sel h1 c == Init cfg)

val free_connection:
    t:connection_table
  -> id:connection_id
  -> ST unit
  (requires fun h0 ->
    inv t h0 /\ T.defined t id h0 /\
    T.value_of t id h0 `is_live_for_rw_in` h0)
  (ensures  fun h0 _ h1 ->
    inv t h1 /\
    h0 `contains` (T.value_of t id h0) /\
    h1 == HyperStack.free (T.value_of t id h0) h0)

val receive_client_hello1:
    t:connection_table
  -> id:connection_id
  -> ch:client_hello{~(has_cookie ch)}
  -> ST unit
  (requires fun h0 ->
    inv t h0 /\
    T.defined t id h0 /\
    h0 `contains` T.value_of t id h0 /\
    Init? (sel h0 (T.value_of t id h0)))
  (ensures  fun h0 _ h1 ->
    inv t h1 /\
    T.defined t id h1 /\
    mods [Ref (T.value_of t id h0)] h0 h1 /\
    (if ch_compatible ch (Init?.cfg (sel h0 (T.value_of t id h0))) then
      sel h1 (T.value_of t id h1) == Sent_ServerHello (ch_random ch) ch 0ul
    else
      sel h1 (T.value_of t id h1) == Sent_HRR (ch_random ch) ch))

val receive_client_hello2:
    t:connection_table
  -> id:connection_id
  -> ch:client_hello
  -> ST bool
  (requires fun h0 ->
    inv t h0 /\
    T.defined t id h0 /\ h0 `contains` T.value_of t id h0 /\
    Init? (sel h0 (Some?.v (T.sel (sel h0 t) id))) /\ has_cookie ch)
  (ensures  fun h0 b h1 ->
    inv t h1 /\
    T.defined t id h1 /\
    mods [Ref (T.value_of t id h0)] h0 h1 /\
    (let c' = sel h1 (T.value_of t id h1) in
    b ==>
      Sent_ServerHello? c' /\
      Sent_ServerHello?.random c' == ch_random ch /\
      Sent_ServerHello?.ch c' == ch))

val receive_client_finished:
    t:connection_table
  -> id:connection_id
  -> ST unit
  (requires fun h0 ->
    inv t h0 /\
    T.defined t id h0 /\ h0 `contains` T.value_of t id h0 /\
    Sent_ServerHello? (sel h0 (Some?.v (T.sel (sel h0 t) id))))
  (ensures  fun h0 b h1 ->
    inv t h1 /\
    T.defined t id h1 /\
    mods [Ref (T.value_of t id h0)] h0 h1 /\
    (let c0 = sel h0 (T.value_of t id h0) in
     let c1 = sel h1 (T.value_of t id h1) in
     Complete? c1 /\
     Complete?.random c1 == Sent_ServerHello?.random c0 /\
     Complete?.ch c1 == Sent_ServerHello?.ch c0))
