module ConnectionTable

open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

open ConnectionTable_Aux

inline_for_extraction
val model: bool

let maybe_id = if model then connection_id else unit

noeq
type connection =
  | Init: cfg:configuration -> connection
  | Sent_HRR: random:UInt32.t -> ch:client_hello -> connection
  | Sent_ServerHello: random:UInt32.t -> ch:client_hello -> id1:maybe_id -> connection
  | Complete: random:UInt32.t -> ch:client_hello -> id1:maybe_id -> connection

let nonce_of (c:connection{~(Init? c)}) =
  match c with
  | Sent_HRR r _ | Sent_ServerHello r _ _ | Complete r _ _ -> r

let step (s1 s2:connection) : Type0 =
  match s1, s2 with
  | Init _, Sent_HRR _ _ -> True
  | Init _, Sent_ServerHello _ _ _ -> True
  | Sent_ServerHello r ch id1, Complete r' ch' id1' -> 
    r == r' /\ ch == ch' /\ id1 == id1'
  | _, _ -> False

let rel : Preorder.preorder connection = closure step

let connection_ref (id:maybe_id) = 
  r:mmmref connection rel{frameOf r `extends` rgn}

val minv: partial_dependent_map maybe_id connection_ref -> Type0

unfold
let _connection_table = t rgn maybe_id connection_ref minv

unfold
let connection_table = if model then _connection_table else unit

inline_for_extraction noextract
val empty: m:imap maybe_id connection_ref minv{m == T.empty}

val inv: _connection_table -> mem -> Type0

inline_for_extraction
val alloc: unit -> ST (connection_table)
  (requires fun _ -> 
    if model then witnessed (region_contains_pred rgn)
    else True)
  (ensures  fun h0 t h1 -> 
    if model then ralloc_post #_ #T.grows rgn empty h0 t h1 /\ inv t h1
    else h0 == h1)

inline_for_extraction
val create:
    t:connection_table
  -> id:maybe_id
  -> cfg:configuration
  -> ST (connection_ref id)
  (requires fun h0 ->
    if model then
      let t:_connection_table = t in
      inv t h0 /\ 
      ~(T.defined t id h0)
    else True)
  (ensures  fun h0 c h1 ->
    (if model then 
      let t:_connection_table = t in
      inv t h1 /\
      mods [Ref t] h0 h1 /\
      T.defined t id h1 /\
      sel h1 t == T.upd (sel h0 t) id c
    else mods [] h0 h1) /\
     frameOf c `extends` rgn /\
     fresh_region (frameOf c) h0 h1 /\
     ~(h0 `contains` c) /\
     h1 `contains` c /\
     sel h1 c == Init cfg)

inline_for_extraction
val free_connection:
    t:connection_table
  -> id:maybe_id
  -> c:connection_ref id
  -> ST unit
  (requires fun h0 ->
    c `is_live_for_rw_in` h0 /\
    (if model then
      let t:_connection_table = t in
      inv t h0 /\ 
      T.defined t id h0 /\
      T.value_of t id h0 == c
    else True))
  (ensures  fun h0 _ h1 -> 
    (if model then 
      let t:_connection_table = t in
      inv t h1 /\
      T.defined t id h1 /\
      T.value_of t id h0 == c
    else True) /\
    h0 `contains` c /\
    h1 == HyperStack.free c h0)

val receive_client_hello1:
    t:connection_table
  -> id:maybe_id
  -> c:connection_ref id
  -> ch:client_hello{~(has_cookie ch)}
  -> ST unit
  (requires fun h0 ->
    (if model then
       let t:_connection_table = t in
       inv t h0 /\
       T.defined t id h0 /\
       T.value_of t id h0 == c
    else True) /\
    h0 `contains` c /\
    Init? (sel h0 c))
  (ensures  fun h0 _ h1 ->
    mods [Ref c] h0 h1 /\
    (if model then
       let t:_connection_table = t in
       inv t h1 /\
       T.defined t id h1
     else True) /\
     (if ch_compatible ch (Init?.cfg (sel h0 c)) then
       sel h1 c == Sent_ServerHello (ch_random ch) ch (if model then 0ul else ())
     else
       sel h1 c == Sent_HRR (ch_random ch) ch))

(*
   Validates a cookie in a second ClientHello.
   In the model, if the cookie is valid we get the connection ID 
   where the cookie was originally sent.
   When using appropriate integrity protection, valid cookies must have
   been created and sent in an early HelloRetryRequest.
*)
val validate_cookie: t:connection_table -> ch2:client_hello
  -> ST (option maybe_id)
  (requires fun h0 -> 
    has_cookie ch2 /\
    (if model then 
      let t:_connection_table = t in 
      inv t h0
     else True))
  (ensures  fun h0 o h1 ->
    h0 == h1 /\
    (match o with
    | None -> True
    | Some id1 ->
      if model then
        let t:_connection_table = t in
        T.defined t id1 h0 /\
        (let c' = T.value_of t id1 h0 in
           token_p c' (fun h0 ->
             Sent_HRR? (sel h0 c') /\
             nonce_of (sel h0 c') == ch_random ch2 /\
             ch_of_cookie ch2 == Sent_HRR?.ch (sel h0 c')))
      else True))

val receive_client_hello2:
    t:connection_table
  -> id:maybe_id
  -> c:connection_ref id
  -> ch2:client_hello
  -> ST bool
  (requires fun h0 ->
    (if model then
      let t:_connection_table = t in
      inv t h0 /\
      T.defined t id h0 /\ 
      T.value_of t id h0 == c
    else True) /\
    h0 `contains` c /\
    Init? (sel h0 c) /\ 
    has_cookie ch2)
  (ensures  fun h0 b h1 ->
    (if model then
      let t:_connection_table = t in
      inv t h1 /\
      T.defined t id h1
    else True) /\
    (let c' = sel h1 c in
     if b then
       mods [Ref c] h0 h1 /\
       Sent_ServerHello? c' /\
       Sent_ServerHello?.random c' == ch_random ch2 /\
       Sent_ServerHello?.ch c' == ch2
     else 
       mods [] h0 h1))

val receive_client_finished:
    t:connection_table
  -> id:maybe_id
  -> c:connection_ref id
  -> ST unit
  (requires fun h0 ->
    (if model then
      let t:_connection_table = t in
      inv t h0 /\
      T.defined t id h0 /\ 
      T.value_of t id h0 == c
    else True) /\
    h0 `contains` c /\
    Sent_ServerHello? (sel h0 c))
  (ensures  fun h0 b h1 ->
    mods [Ref c] h0 h1 /\
    (if model then
      let t:_connection_table = t in
      inv t h1 /\
      T.defined t id h1
    else True) /\
    (let c0 = sel h0 c in
     let c1 = sel h1 c in
     Complete? c1 /\
     Complete?.random c1 == Sent_ServerHello?.random c0 /\
     Complete?.ch c1 == Sent_ServerHello?.ch c0))
