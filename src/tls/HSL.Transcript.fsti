module HSL.Transcript

(* Main issue:

   We need a way to add messages to the transcript without setting the
   hash alg.

   Once the hash alg is set, we need to "catch up" and hash the
   unhashed messages accumulated so far.

   For this, we need some auxiliary state.
*)
open FStar.Integers
open FStar.HyperStack.ST
module List = FStar.List.Tot
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13

module PV = Parsers.ProtocolVersion
module LP = LowParse.Low.Base
module IncHash = EverCrypt.Hash.Incremental

module R = MITLS.Repr
module R_HS = MITLS.Repr.Handshake

module R_CH = MITLS.Repr.ClientHello
module CH = Parsers.ClientHello

module R_SH = MITLS.Repr.ServerHello
module SH = Parsers.ServerHello

type bytes = FStar.Seq.seq uint_8

type alg = Spec.Hash.Definitions.hash_alg


let hs_ch = ch:HSM.handshake{HSM.M_client_hello? ch}
let hs_sh = sh:HSM.handshake{HSM.M_server_hello? sh}
// assume
val is_hrr (sh:hs_sh) : bool

inline_for_extraction
let hello_retry_request : Type0 = 
  s:hs_sh { is_hrr s }

type retry =
  hs_ch
  & hello_retry_request

/// `transcript_t`: Transcript for 1.2 and 1.3 have a shared prefix
/// and then fork to version-specific message types
///
///   Note, HSM.handshake is the type of messages before the version
///   is negotiated and so does not contain either HSM12 or HSM13
///   messages. The three types are disjoint and parsed independently.
///
/// Does not yet cover Hello retry request (?)
///
/// Question: How much refinement do we need in this type?  e.g.,
/// number and shape of the h-prefix of the last two cases

unfold
let max_transcript_size : pos = 15

let bounded_list 'a n = l:list 'a{List.length l < n}

let can_extend_bounded_list #a #n (l:bounded_list a n) = List.length l + 1 < n

open Parsers.ClientHello
let client_hello_has_psk (ch:CH.clientHello) =
  exists (ext:_). 
    List.memP ext ch.extensions /\
    Parsers.ClientHelloExtension.CHE_pre_shared_key? ext /\
    True (* what else do we need? e.g., that it has as many binders as ids? *)

noeq
type transcript_t =
  | Start: retried:option retry ->
           transcript_t

  | Hello: retried:option retry ->
           ch:hs_ch ->
           transcript_t

  | Transcript12: ch:hs_ch ->
                  sh:hs_sh -> //Should prescribe the protocol version
                  rest:bounded_list HSM12.handshake12 max_transcript_size ->
                  transcript_t

  | Transcript13: retried:option retry ->
                  ch:hs_ch ->
                  sh:hs_sh -> //Should prescribe the protocol version
                  rest:bounded_list HSM13.handshake13 max_transcript_size -> //but requires a dependence on Nego
                  transcript_t
      
let transcript_n (n:nat{n < max_transcript_size}) =
  t:transcript_t{
    match t with
    | Start _
    | Hello _ _ -> True
    | Transcript12 _ _ rest -> List.length rest < n
    | Transcript13 _ _ _ rest -> List.length rest < n
  }

/// `transcript_bytes`: The input of the hash algorithm computed by
/// concatenated the message formatting of the messages
///
/// Note, new messages are cons'd to the front of the transcript so
/// formatting is a fold right. This is convenient here, but is
/// potentially contentious since other parts of the code
/// use snoc
///
/// Note: we want this to be in Tot

// should be at least 
//   max (handshake12_parser_kind.parser_kind_high,
//        handshake13_parser_kind.parser_kind_high,
//        handshake_parser_kind.parser_kind_high)
unfold // to recover Z3 linearity
let max_message_size = 16777219 

val transcript_bytes (t:transcript_t) 
: GTot (b: bytes { 
       Seq.length b <= (max_transcript_size + 4) * max_message_size 
  })


/// `state`: Abstract state of the module
///
/// It maintains the transcript in mutable state.
///
/// We may need a way to free the state also
val state (a:alg) : Type0

val invariant (#a: _) (s:state a) (t:transcript_t) (h:HS.mem) : Type0  

val footprint (#a:_) (s:state a) : GTot B.loc

val elim_invariant (#a: _) (s:state a) (t:transcript_t) (h:HS.mem) 
  : Lemma 
    (requires invariant s t h)
    (ensures B.loc_not_unused_in h `B.loc_includes` footprint s)

val region_of (#a: _) (s:state a)
  : GTot HS.rid

val frame_invariant (#a:_) (s:state a) (t: transcript_t) (h0 h1:HS.mem) (l:B.loc)
  : Lemma
    (requires
      invariant s t h0 /\
      B.loc_disjoint l (footprint s) /\
      B.modifies l h0 h1)
    (ensures
      invariant s t h1)
    [SMTPat (invariant s t h1);
     SMTPat (B.modifies l h0 h1)]

/// `create`:
///
///   -- Caller provides a region `r` in which to allocate a
///      transcript instance
///
///   -- The instance is allocated in fresh state (so `modifies none`)
///
///   -- The transcript's initial state is empty and the hash alg is
///      not chosen yet
val create (r:Mem.rgn) (a:alg)
  : ST (state a & Ghost.erased transcript_t)
       (requires fun _ -> True)
       (ensures fun h0 (s, tx) h1 ->
         let tx = Ghost.reveal tx in
         tx == Start None /\
         invariant s tx h1 /\
         region_of s == r /\
         B.loc_region_only true r `B.loc_includes` footprint s /\
         B.modifies B.loc_none h0 h1 /\
         B.fresh_loc (footprint s) h0 h1)

unfold
let extend_hash_pre_common
  #a
  (s:state a)
  (#rrel #rel: _) (#b:LP.slice rrel rel) (#x:_) (r:R.repr x b)
  (t:transcript_t)
  (h:HS.mem)
  = invariant s t h /\
    R.valid r h /\
    B.loc_disjoint (B.loc_buffer LP.(b.base)) (footprint s)

unfold
let extend_hash_post_common
  #a
  (s:state a)
  (t:transcript_t)
  (h0 h1:HS.mem)
  = invariant s t h1 /\
    B.modifies (footprint s) h0 h1

// assume 
val nego_version (ch:CH.clientHello)
                 (sh:SH.serverHello)
       : PV.protocolVersion

let extend_with_hsm 
      (t:transcript_t)
      (m:HSM.handshake)
  : GTot (option transcript_t)
= match t, m with
  | Start retry, HSM.M_client_hello ch ->
    //Missing: consistency between retry and ch
    Some (Hello retry m)

  | Hello retry ch, HSM.M_server_hello sh ->
    if None? retry
    && is_hrr m
    then None
    else
      begin
      match nego_version 
             (HSM.M_client_hello?._0 ch)
             sh,
            retry
      with
      | PV.TLS_1p2, None ->
        Some (Transcript12 ch m [])

      | PV.TLS_1p3, _ ->
        Some (Transcript13 retry ch m [])

      | _ -> None
      end

  | _ ->
    None

let extend_with_hsm12 (t:transcript_n (max_transcript_size - 1)) (m:HSM12.handshake12)
  : option transcript_t
  = match t with
    | Transcript12 ch sh rest ->
      List.append_length rest [m];
      Some (Transcript12 ch sh (List.snoc (rest, m)))
  
    | _ -> None


let extend_with_hsm13 (t:transcript_n (max_transcript_size - 1)) (m:HSM13.handshake13)
  : option transcript_t
  = match t with
    | Transcript13 retry ch sh rest ->
      List.append_length rest [m];
      Some (Transcript13 retry ch sh (List.snoc (rest, m)))
  
    | _ -> None

val extend_hash_hsm
  (#a:_) (s:state a)
  (#p #q: _) (#b:LP.slice p q) (r:R_HS.repr b)
  (tx:G.erased (transcript_n (max_transcript_size - 1)))
  : Stack (G.erased transcript_t)
       (requires fun h ->
         let tx = G.reveal tx in
         extend_hash_pre_common s r tx h /\
         Some? (extend_with_hsm tx (R.value r)))
       (ensures fun h0 tx' h1 ->
         let tx' = G.reveal tx' in
         tx' == Some?.v (extend_with_hsm (G.reveal tx) (R.value r)) /\
         extend_hash_post_common s tx' h0 h1)

//TODO: move to a separate module
let repr_hs12  (#rrel #rel: _) (b:LP.slice rrel rel) =
  R.repr_p _ b HSM12.handshake12_parser

val extend_hash_hsm12
  (#a:_) (s:state a)
  (#p #q: _) (#b:LP.slice p q) (r:repr_hs12 b)
  (tx:G.erased (transcript_n (max_transcript_size - 1)))
  : Stack (G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      extend_hash_pre_common s r tx h /\
      Some? (extend_with_hsm12 tx (R.value r)))
    (ensures fun h0 tx' h1 ->
      let tx = G.reveal tx in
      let tx' = G.reveal tx' in
      tx' == Some?.v (extend_with_hsm12 tx (R.value r)) /\
      extend_hash_post_common s tx' h0 h1)


//TODO: move to a separate module
let repr_hs13  (#rrel #rel: _) (b:LP.slice rrel rel) =
  R.repr_p _ b HSM13.handshake13_parser

val extend_hash_hsm13
  (#a:_) (s:state a)
  (#p #q: _) (#b:LowParse.Low.Base.slice p q) (r:repr_hs13 b)
  (tx:G.erased (transcript_n (max_transcript_size - 1)))
  : Stack (G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      extend_hash_pre_common s r tx h /\
      Some? (extend_with_hsm13 tx (R.value r)))
    (ensures fun h0 tx' h1 ->
      let tx = G.reveal tx in       
      let tx' = G.reveal tx' in
      tx' == Some?.v (extend_with_hsm13 tx (R.value r)) /\
      extend_hash_post_common s tx' h0 h1)

val extend_ch_with_psk
  (#a:_) (s:state a)
  (#p #q: _) (#b:LowParse.Low.Base.slice p q) (r:R_HS.repr b)
  (tx:G.erased transcript_t)
  : StackInline 
      (Hacl.Hash.Definitions.hash_t a &
       G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      let hs = R.value r in
      extend_hash_pre_common s r tx h /\
      Start? tx /\         
      HSM.M_client_hello? hs /\
      client_hello_has_psk (HSM.M_client_hello?._0 hs))
    (ensures fun h0 (hash, tx') h1 ->
      let tx = G.reveal tx in
      let tx' = G.reveal tx' in
      B.fresh_loc (B.loc_buffer hash) h0 h1 /\
      B.live h1 hash /\
      tx' == Hello (Start?.retried tx) (R.value r) /\
      extend_hash_post_common s tx' h0 h1)

let extend_with_hrr 
       (t:transcript_t)
       (ch:HSM.handshake)
       (sh:HSM.handshake) =
  match t, ch, sh with       
  | Start None, HSM.M_client_hello _, HSM.M_server_hello _ ->
    if is_hrr sh
    then Some (Start (Some (ch, sh)))
    else None
  | _ ->
    None
    
val extend_hrr
  (#a:_) (s:state a)
  (#p #q:_) (#b:LP.slice p q) (r_ch:R_HS.repr b)
  (#p' #q':_) (#b':LP.slice p' q') (r_sh:R_HS.repr b')  
  (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
      (requires fun h ->
         let tx = G.reveal tx in
         extend_hash_pre_common s r_sh tx h /\
         Some? (extend_with_hrr tx (R.value r_ch) (R.value r_sh)))
       (ensures fun h0 tx' h1 ->                                     
         let tx = G.reveal tx in
         let tx' = G.reveal tx' in
         tx' == Some?.v (extend_with_hrr tx (R.value r_ch) (R.value r_sh)) /\
         extend_hash_post_common s tx' h0 h1)         


let max_message_size_lt_max_input_length (a: alg) : Lemma
  (max_transcript_size * max_message_size < Spec.Hash.Definitions.max_input_length a)
  [SMTPat (Spec.Hash.Definitions.max_input_length a)] 
 =
  assert_norm (max_transcript_size * max_message_size < pow2 61);
  assert_norm (max_transcript_size * max_message_size < pow2 125)

val extract_hash
  (#a:alg) (s:state a)
  (tag:Hacl.Hash.Definitions.hash_t a)
  (tx:G.erased transcript_t)
  : ST unit
    (requires (fun h0 ->
      let tx = G.reveal tx in
      invariant s tx h0 /\
      B.live h0 tag /\
      B.loc_disjoint (footprint s) (B.loc_buffer tag)))
    (ensures (fun h0 _ h1 ->
      let open B in
      let tx = G.reveal tx in
      invariant s tx h1 /\
      modifies (loc_union (footprint s) (loc_buffer tag)) h0 h1 /\
      B.live h1 tag /\
      B.as_seq h1 tag == Spec.Hash.hash a (transcript_bytes tx)))


(*
val free
*)

(* We need some form of collision resistance adapted to transcripts.
   i.e., if the hashes of two transcripts match then the transcripts
   themselves do.
*)
