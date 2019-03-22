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

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

open Parsers.Handshake13

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13
module PV = Parsers.ProtocolVersion
module LP = LowParse.Low.Base
open HSL.Common
module IncHash = EverCrypt.Hash.Incremental

type bytes = Spec.Hash.Definitions.bytes

type alg = Spec.Hash.Definitions.hash_alg

// assume
val is_hrr (sh:Parsers.ServerHello.serverHello)
       : bool

inline_for_extraction
let hello_retry_request : Type0 = (s: Parsers.ServerHello.serverHello { is_hrr s } )
//TODO: This does not yet seem to be modeled in Parsers.rfc

type retry = Parsers.ClientHello.clientHello
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
let client_hello_has_psk (ch:Parsers.ClientHello.clientHello) =
  exists (ext:_). 
    List.memP ext ch.extensions /\
    Parsers.ClientHelloExtension.CHE_pre_shared_key? ext /\
    True (* what else do we need? e.g., that it has as many binders as ids? *)
  
let client_hello_with_psk =
  ch:Parsers.ClientHello.clientHello{
    client_hello_has_psk ch
  }

let is_truncated_client_hello_bytes (b:bytes) =
     exists (suffix:bytes).
      Seq.length b > 0 /\
      Seq.length suffix > 0 /\
      (match LP.parse HSM.handshake_parser (b `Seq.append` suffix) with
       | Some (HSM.M_client_hello ch, _) ->
         client_hello_has_psk ch
       | _ -> False)
 
let truncated_client_hello_bytes = 
  b:bytes{ is_truncated_client_hello_bytes b }


noeq
type transcript_t =
  | Start: retried:option retry ->
           transcript_t

  | Hello: retried:option retry ->
           ch:Parsers.ClientHello.clientHello ->
           transcript_t

  | Transcript12: ch:Parsers.ClientHello.clientHello ->
                  sh:Parsers.ServerHello.serverHello -> //Should prescribe the protocol version
                  rest:bounded_list HSM12.handshake12 max_transcript_size ->
                  transcript_t

  | Transcript13: retried:option retry ->
                  ch:Parsers.ClientHello.clientHello ->
                  sh:Parsers.ServerHello.serverHello -> //Should prescribe the protocol version
                  rest:bounded_list HSM13.handshake13 max_transcript_size -> //but requires a dependence on Nego
                  transcript_t
                  
  | TruncatedClientHello:
      retried:option retry ->
      tch_b:truncated_client_hello_bytes ->
      transcript_t
      
let transcript_n (n:nat{n < max_transcript_size}) =
  t:transcript_t{
    match t with
    | Start _
    | Hello _ _ -> True
    | Transcript12 _ _ rest -> List.length rest < n
    | Transcript13 _ _ _ rest -> List.length rest < n
    | TruncatedClientHello _ _ -> True
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

unfold // to recover Z3 linearity
let max_message_size = 16777219 // should be at least max (handshake12_parser_kind.parser_kind_high, handshake13_parser_kind.parser_kind_high, handshake_parser_kind.parser_kind_high)

val transcript_bytes (t:transcript_t) : GTot (b: bytes { Seq.length b < max_transcript_size `Prims.op_Multiply` max_message_size })


/// `state`: Abstract state of the module
///
/// It maintains the transcript in mutable state.
/// It is allocated before knowing what the hash algorithm is
/// The API provides a way to set the hash algorithm later
///
/// We may need a way to free the state also
val state (a:alg) : Type0

val invariant (#a: _) (s:state a) (t:transcript_t) (h:HS.mem) : Type0

val footprint (#a:_) (s:state a) (h:HS.mem) : GTot B.loc

val region_of (#a: _) (s:state a)
  : GTot HS.rid

val frame_invariant (#a:_) (s:state a) (t: transcript_t) (h0 h1:HS.mem) (l:B.loc)
  : Lemma
    (requires
      invariant s t h0 /\
      B.loc_disjoint l (footprint s h0) /\
      B.modifies l h0 h1)
    (ensures
      invariant s t h1 /\
      footprint s h0 == footprint s h1)


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
  : ST (state a)
       (requires fun _ -> True)
       (ensures fun h0 s h1 ->
         invariant s (Start None) h1 /\
         region_of s == r /\
         B.loc_region_only true r `B.loc_includes` footprint s h1 /\
         B.modifies B.loc_none h0 h1 /\
         B.fresh_loc (footprint s h1) h0 h1)

unfold
let extend_hash_pre_common
  #a
  (s:state a)
  (#rrel #rel: _)
  (b:LP.slice rrel rel)
  (t:transcript_t)
  (h:HS.mem)
  = invariant s t h /\
    LP.live_slice h b /\
    B.loc_disjoint (B.loc_buffer LP.(b.base)) (footprint s h)

unfold
let extend_hash_post_common
  #a
  (s:state a)
  (#rrel #rel: _)
  (b:LP.slice rrel rel)
  (t:transcript_t)
  (h0 h1:HS.mem)
  = invariant s t h1 /\
    B.modifies (footprint s h1) h0 h1 /\
    footprint s h1 == footprint s h0

// assume 
val nego_version (ch:Parsers.ClientHello.clientHello)
                        (sh:Parsers.ServerHello.serverHello)
       : Parsers.ProtocolVersion.protocolVersion

let extend_with_hsm 
      (t:transcript_t)
      (m:HSM.handshake)
  : GTot (option transcript_t)
= match t, m with
  | Start retry, HSM.M_client_hello ch ->
    //Missing: consistency between retry and ch
    Some (Hello retry ch)

  | Hello retry ch, HSM.M_server_hello sh ->
    if None? retry
    && is_hrr sh
    && nego_version ch sh = PV.TLS_1p3
    then Some (Start (Some (ch, sh)))
    else
      begin
      match nego_version ch sh, retry with
      | PV.TLS_1p2, None ->
        Some (Transcript12 ch sh [])

      | PV.TLS_1p3, _ ->
        Some (Transcript13 retry ch sh [])

      | _ -> None
      end

  | _ ->
    None

let extend_with_tch (t:transcript_t) (tch_b:truncated_client_hello_bytes)
  : GTot (option transcript_t) =
  match t with
  | Start retry ->
    Some (TruncatedClientHello retry tch_b)

  | _ -> None

let extend_with_binders (t:transcript_t) (binder_b:bytes)
  : GTot (option transcript_t) =
  match t with
  | TruncatedClientHello retry tch_b ->
    (match LP.parse HSM.handshake_parser (tch_b `Seq.append` binder_b) with
     | Some (HSM.M_client_hello ch, len) ->
       if len = Seq.length tch_b + Seq.length binder_b
       then Some (Hello retry ch)
       else None
     | _ -> None)
  | _ -> None

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

val extend_tch 
  (#a:_)
  (s:state a)
  (#rrel #rel: _)
  (b:LowParse.Low.Base.slice rrel rel)
  (p0:uint_32)
  (p1:uint_32{p0 < p1})
  (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
       (requires fun h ->
         let tx = G.reveal tx in
         extend_hash_pre_common s b tx h /\
         Start? tx /\
         LP.valid HSM.handshake_parser h b p0 /\
         (let msg = LP.contents HSM.handshake_parser h b p0 in
          let len = LP.content_length HSM.handshake_parser h b p0 in
          HSM.M_client_hello? msg /\
          client_hello_has_psk (HSM.M_client_hello?._0 msg) /\
          UInt32.v p1 < UInt32.v p0 + len
       ))
       (ensures fun h0 tx' h1 ->
         let tx = G.reveal tx in
         let tx' = G.reveal tx' in
         let msg = LP.contents HSM.handshake_parser h0 b p0 in
         let tch = LP.bytes_of_slice_from_to h0 b p0 p1 in
         is_truncated_client_hello_bytes tch /\
         Some? (extend_with_tch tx tch) /\
         tx' == Some?.v (extend_with_tch tx tch) /\
         extend_hash_post_common s b tx' h0 h1)

val extend_tch_binders
  (#a:_)
  (s:state a)
  (#rrel #rel: _)
  (b:LowParse.Low.Base.slice rrel rel)
  (p0:uint_32)
  (p1:uint_32)
  (p2:uint_32{p0 < p1 /\ p1 < p2})
  (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
       (requires fun h ->
         let tx = G.reveal tx in
         extend_hash_pre_common s b tx h /\
         TruncatedClientHello? tx /\
         LP.valid_pos HSM.handshake_parser h b p0 p2 /\
         (let msg = LP.contents HSM.handshake_parser h b p0 in
          let tch_b = LP.bytes_of_slice_from_to h b p0 p1 in
          TruncatedClientHello?.tch_b tx `Seq.equal` tch_b /\
          HSM.M_client_hello? msg /\
          client_hello_has_psk (HSM.M_client_hello?._0 msg)
       ))
       (ensures fun h0 tx' h1 ->
         let tx = G.reveal tx in
         let tx' = G.reveal tx' in
         let msg = LP.contents HSM.handshake_parser h0 b p0 in
         let binder_b = LP.bytes_of_slice_from_to h0 b p1 p2 in
         Some? (extend_with_binders tx binder_b) /\
         tx' == Some?.v (extend_with_binders tx binder_b) /\
         extend_hash_post_common s b tx' h0 h1)

val extend_hash_hsm
  (#a:_)
  (s:state a)
  (#rrel #rel: _)
  (b:LowParse.Low.Base.slice rrel rel)
  (p0:uint_32)
  (p1:uint_32)
  (tx:G.erased (transcript_n (max_transcript_size - 1)))
  : Stack (G.erased transcript_t)
       (requires fun h ->
         let tx = G.reveal tx in
         extend_hash_pre_common s b tx h /\
         LP.valid_pos HSM.handshake_parser h b p0 p1 /\
         (let msg = LP.contents HSM.handshake_parser h b p0 in
          Some? (extend_with_hsm tx msg)))
       (ensures fun h0 tx' h1 ->
         let tx' = G.reveal tx' in
         let msg = LP.contents HSM.handshake_parser h0 b p0 in
         tx' == Some?.v (extend_with_hsm (G.reveal tx) msg) /\
         extend_hash_post_common s b tx' h0 h1)

val extend_hash_hsm12
  (#a:_)
  (s:state a)
  (#rrel #rel: _)
  (b:LowParse.Low.Base.slice rrel rel)
  (p0:uint_32)
  (p1:uint_32)
  (tx:G.erased (transcript_n (max_transcript_size - 1)))
  : Stack (G.erased transcript_t)
       (requires fun h ->
         let tx = G.reveal tx in
         extend_hash_pre_common s b tx h /\
         LP.valid_pos HSM12.handshake12_parser h b p0 p1 /\
         (let msg = LP.contents HSM12.handshake12_parser h b p0 in
          Some? (extend_with_hsm12 tx msg)))
       (ensures fun h0 tx' h1 ->
         let tx' = G.reveal tx' in
         let msg = LP.contents HSM12.handshake12_parser h0 b p0 in
         tx' == Some?.v (extend_with_hsm12 (G.reveal tx) msg) /\
         extend_hash_post_common s b tx' h0 h1)

val extend_hash_hsm13
  (#a:_)
  (s:state a)
  (#rrel #rel: _)
  (b:LowParse.Low.Base.slice rrel rel)
  (p0:uint_32)
  (p1:uint_32)
  (tx:G.erased (transcript_n (max_transcript_size - 1)))
  : Stack (G.erased transcript_t)
       (requires fun h ->
         let tx = G.reveal tx in
         extend_hash_pre_common s b tx h /\
         LP.valid_pos HSM13.handshake13_parser h b p0 p1 /\
         (let msg = LP.contents HSM13.handshake13_parser h b p0 in
          Some? (extend_with_hsm13 tx msg)))
       (ensures fun h0 tx' h1 ->
         let tx' = G.reveal tx' in
         let msg = LP.contents HSM13.handshake13_parser h0 b p0 in
         tx' == Some?.v (extend_with_hsm13 (G.reveal tx) msg) /\
         extend_hash_post_common s b tx' h0 h1)


let max_message_size_lt_max_input_length (a: alg) : Lemma
  (max_transcript_size `Prims.op_Multiply` max_message_size < Spec.Hash.Definitions.max_input_length a)
  [SMTPat (Spec.Hash.Definitions.max_input_length a)] 
 =
  assert_norm (max_transcript_size `Prims.op_Multiply` max_message_size < pow2 61);
  assert_norm (max_transcript_size `Prims.op_Multiply` max_message_size < pow2 125)

val extract_hash
  (#a:alg)
  (s:state a)
  (tag:Hacl.Hash.Definitions.hash_t a)
  (tx:G.erased transcript_t)
  : ST unit
       (requires (fun h0 ->
         let tx = G.reveal tx in
         invariant s tx h0 /\
         B.live h0 tag /\
         B.loc_disjoint (footprint s h0) (B.loc_buffer tag)))
       (ensures (fun h0 _ h1 ->
         let open B in
         let tx = G.reveal tx in
//         frame_state s h0 h1 /\
         invariant s tx h1 /\
         modifies (loc_union (footprint s h1) (loc_buffer tag)) h0 h1 /\
         B.as_seq h1 tag == Spec.Hash.hash a (transcript_bytes tx)))


(*
val free

val extract




let can_extend_with_hsm12 (t:transcript_t) =
  match t with
  | Transcript_hello_server _ -> True
  | Transcript12 _ _ -> True
  | _ -> False

let can_extend_with_hsm13 (t:transcript_t) =
  match t with
  | Transcript_hello_server _ -> True
  | Transcript13 _ _ -> True
  | _ -> False

let extend_transcript
  (t:transcript_t)
  (msg:HSM.handshake{can_extend_with_hsm t})
  : GTot transcript_t
  = match t with
    | Transcript_nil -> Transcript_hello_server [msg]
    | Transcript_hello_server msgs -> Transcript_hello_server (msg::msgs)

let extend_transcript12
  (t:transcript_t)
  (msg:HSM12.handshake12{can_extend_with_hsm12 t})
  : GTot transcript_t
  = match t with
    | Transcript_hello_server msgs -> Transcript12 msgs [msg]
    | Transcript12 hmsgs msgs -> Transcript12 hmsgs (msg::msgs)

let extend_transcript13
  (t:transcript_t)
  (msg:HSM13.handshake13{can_extend_with_hsm13 t})
  : GTot transcript_t
  = match t with
    | Transcript_hello_server msgs -> Transcript13 msgs [msg]
    | Transcript13 hmsgs msgs -> Transcript13 hmsgs (msg::msgs)



// val extend_unhashed_transcript
//      (s:state)
//      (#b:LowParse.Low.Base.slice)
//      (i:irepr b HSM.handshake_parser)
//   : ST unit
//     (requires fun h ->
//       invariant s h /\



val extend_hash12
  (s:state)
  (b:B.buffer uint_8)
  (p0:uint_32)
  (p1:uint_32)
  (msg:G.erased HSM12.handshake12)
  : ST unit
       (requires fun h ->
         extend_hash_pre_common s b h /\
         can_extend_with_hsm12 (transcript s h) /\
         valid_parsing12 (G.reveal msg) p0 p1 b h)
       (ensures (fun h0 _ h1 ->
         extend_hash_post_common s b h0 h1 /\
         transcript s h1 == extend_transcript12 (transcript s h0) (G.reveal msg)))

val extend_hash13
  (s:state)
  (b:B.buffer uint_8)
  (p0:uint_32)
  (p1:uint_32)
  (msg:G.erased HSM13.handshake13)
  : ST unit
       (requires fun h ->
         extend_hash_pre_common s b h /\
         can_extend_with_hsm13 (transcript s h) /\
         valid_parsing13 (G.reveal msg) p0 p1 b h)
       (ensures (fun h0 _ h1 ->
         extend_hash_post_common s b h0 h1 /\
         transcript s h1 == extend_transcript13 (transcript s h0) (G.reveal msg)))



(* We need some form of collision resistance adapted to transcripts.
   i.e., if the hashes of two transcripts match then the transcripts
   themselves do.
*)
