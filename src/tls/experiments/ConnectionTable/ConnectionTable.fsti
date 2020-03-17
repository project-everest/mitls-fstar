module ConnectionTable

open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

open ConnectionTable_Aux

(*
  The connection table and ids are model artifacts that do not exist
  in concrete code. So functions that modify the connection state 
  do it through a connection reference rather than looking up in the table.

- API functions take (id:maybe_id) (c:connection_ref id) as arguments.
  There is no real dependency on id in connection_ref and maybe_id is
  just unit and discarded in concrete code.
  Note that we cannot store the id in the connection reference to avoid
  having to pass it as argument, because we need to use it in specifications.
  We could still store it and keep a witness that the id is the same
  as the index, but this is of little use.

- We could add an API layer that allocates a single global connection table
  and uses it throughout. We could eliminate that layer by doing this from 
  the beginning, but avoiding top-level effects is cleaner for an experiment.

- In miTLS, we'll use

  type connection_id = random // Unique across clients and server connections

  Always sampled fresh upon connection creation

  type connection = TLS.Handshake.Machine.tt

  and the table will map r:random -> connection

  TLS.Handshake.Machine defines

  type state =
  | Client:
    client_rgn: rgn ->
    client_cfg: client_config ->
    client_state: client_mref client_rgn client_cfg -> state

  | Server:
    server_rgn: rgn ->
    server_cfg: server_config ->
    server_state: server_mref server_rgn server_cfg -> state
 
  let tt =
    | Connection: 
      nonce: if model then TLSInfo.random else unit -> 
      state: t {token_p st (fun h -> nonce_of st h == nonce)}
*)

inline_for_extraction
val model: bool

let maybe_id = if model then connection_id else unit

noeq
type connection =
  | Init: cfg:configuration -> connection
  | Sent_HRR: ch:client_hello -> connection
  | Sent_ServerHello: ch:client_hello -> id1:maybe_id -> connection
  | Complete: ch:client_hello -> id1:maybe_id -> connection

let step (s1 s2:connection) : Type0 =
  match s1, s2 with
  | Init _, Sent_HRR _ -> True
  | Init _, Sent_ServerHello _ _ -> True
  | Sent_ServerHello ch id1, Complete ch' id1' -> ch == ch' /\ id1 == id1'
  | _, _ -> False

let rel : Preorder.preorder connection = closure step

// Store the ID rather than making it a parameter?
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
       sel h1 c == Sent_ServerHello ch (if model then 0ul else ())
     else
       sel h1 c == Sent_HRR ch))

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
     Complete?.ch c1 == Sent_ServerHello?.ch c0))
