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

open HSL.Common

type bytes = Spec.Hash.Definitions.bytes

type alg = Spec.Hash.Definitions.hash_alg

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
noeq type transcript_t =
  | Transcript_nil: transcript_t (* Why not Transcript_hello_server [] ?*)
  | Transcript_hello_server: h:list HSM.handshake -> transcript_t
  | Transcript12: h:list HSM.handshake(* { h negotiates TLS1.2 } *) -> m:list HSM12.handshake12 -> transcript_t
  | Transcript13: h:list HSM.handshake(* { h negotiates TLS1.3 } *) -> m:list HSM13.handshake13 -> transcript_t

/// `transcript_bytes`: The input of the hash algorithm computed by
/// concatenated the message formatting of the messages
///
/// Note, new messages are cons'd to the front of the transcript so
/// formatting is a fold right. This is convenient here, but is
/// potentially contentious since other parts of the code
/// use snoc
let transcript_bytes (t:transcript_t) : GTot bytes =
  match t with
  | Transcript_nil -> Seq.empty
  | Transcript_hello_server h ->
    List.fold_right_gtot h (fun x a -> Seq.append a (format_hs_msg x)) Seq.empty
  | Transcript12 h m ->
    Seq.append (List.fold_right_gtot h (fun x a -> Seq.append a (format_hs_msg x)) Seq.empty)
               (List.fold_right_gtot m (fun x a -> Seq.append a (format_hs12_msg x)) Seq.empty)
  | Transcript13 h m ->
    Seq.append (List.fold_right_gtot h (fun x a -> Seq.append a (format_hs_msg x)) Seq.empty)
               (List.fold_right_gtot m (fun x a -> Seq.append a (format_hs13_msg x)) Seq.empty)


/// `state`: Abstract state of the module
///
/// It maintains the transcript in mutable state.
/// It is allocated before knowing what the hash algorithm is
/// The API provides a way to set the hash algorithm later
///
/// We may need a way to free the state also
val state : Type0

/// `region_of`: The caller provides a region in which to allocate the
/// transcript instance
val region_of : state -> GTot Mem.rgn

/// `footprint`: Abstract footprint of this instance, used for framing
///
/// Q: Do we need a lemma or a refined result type to say that it is
/// included in the region? Note, the create and set_hash_alg functions
/// provide it as a postcondition
///
/// The footprint is the fragment of the HS.mem read by the
/// `transcript`, `hash_alg` and `invariant` functions (and
/// `footprint` itself). See below, `frame_state`
val footprint : state -> HS.mem -> GTot B.loc

/// `transcript`: The current (ghost) transcript
val transcript : state -> HS.mem -> GTot transcript_t

/// `hash_alg`: Hashing algorithm in use
val hash_alg : state -> HS.mem -> GTot (option alg)

/// `invariant`: Main abstract invariant of this module
val invariant : state -> HS.mem -> prop

/// `frame_state`: The postcondition of the framing lemma for
/// the main spec. functions and predicates provided by this module
/// They all only depend on the dynamic footprint `footprint`
///
/// Q: Why unfold?
unfold let frame_state (s:state) (h0 h1:HS.mem) : prop =
  hash_alg s h0 == hash_alg s h1 /\
  footprint s h0 == footprint s h1 /\
  transcript s h0 == transcript s h1 /\
  invariant s h1

/// `framing`: the framing lemma itself
val framing (s:state) (l:B.loc) (h0 h1: HS.mem)
  : Lemma
      (requires
        B.modifies l h0 h1 /\
        B.loc_disjoint l (footprint s h0) /\
        invariant s h0)
      (ensures frame_state s h0 h1)

/// `create`:
///
///   -- Caller provides a region `r` in which to allocate a
///      transcript instance
///
///   -- The instance is allocated in fresh state (so `modifies none`)
///
///   -- The transcript's initial state is empty and the hash alg is
///      not chosen yet
val create (r:Mem.rgn)
  : ST state
       (requires fun _ -> True)
       (ensures fun h0 s h1 ->
         let open B in
         invariant s h1 /\
         region_of s == r /\
         modifies loc_none h0 h1 /\
         fresh_loc (footprint s h1) h0 h1 /\
         r `region_includes` footprint s h1 /\
         hash_alg s h1 == None /\
         transcript s h1 == Transcript_nil)

/// `set_hash_alg`:
///    -- Sets the hash algorithm once and for all
///    -- Note, the footprint grows to include some fresh location `l`
val set_hash_alg (a:alg) (s:state)
  : ST unit
       (requires fun h ->
         invariant s h /\
         hash_alg s h == None)
       (ensures fun h0 _ h1 ->
         let open B in
         invariant s h1 /\
         hash_alg s h1 == Some a /\
         transcript s h1 == transcript s h0 /\
         (exists l. fresh_loc l h0 h1 /\
               footprint s h1 == B.loc_union l (footprint s h0) /\
               region_of s `region_includes` footprint s h1))

let can_extend_with_hsm (t:transcript_t) =
  match t with
  | Transcript_nil -> True
  | Transcript_hello_server _ -> True
  | _ -> False

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

unfold let extend_hash_pre_common
  (s:state)
  (b:B.buffer uint_8)
  (h:HS.mem)
  = invariant s h /\
    B.live h b /\
    B.loc_disjoint (B.loc_buffer b) (footprint s h) /\
    Some? (hash_alg s h)

unfold let extend_hash_post_common
  (s:state)
  (b:B.buffer uint_8)
  (h0 h1:HS.mem)
  = invariant s h1 /\
    B.modifies (footprint s h1) h0 h1 /\
    footprint s h1 == footprint s h0 /\
    hash_alg s h1 == hash_alg s h0

// val extend_unhashed_transcript
//      (s:state)
//      (#b:LowParse.Low.Base.slice)
//      (i:irepr b HSM.handshake_parser)
//   : ST unit
//     (requires fun h ->
//       invariant s h /\


val extend_hash
  (s:state)
  (b:B.buffer uint_8) //Should this be a LowParse.Low.Base.slice and a irepr?
  (p0:uint_32)
  (p1:uint_32)
  (msg:G.erased HSM.handshake)
  : ST unit
       (requires fun h ->
         extend_hash_pre_common s b h /\
         can_extend_with_hsm (transcript s h) /\
         valid_parsing (G.reveal msg) p0 p1 b h)
       (ensures (fun h0 _ h1 ->
         extend_hash_post_common s b h0 h1 /\
         transcript s h1 == extend_transcript (transcript s h0) (G.reveal msg)))

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

let buf_is_hash_of_b (a:alg) (tag:Hacl.Hash.Definitions.hash_t a) (h:HS.mem) (b:bytes)
  = assume (Seq.length b < Spec.Hash.Definitions.max_input_length a);  //AR: need to sort this out
    admit ();  //AR: TODO: strange behavior with interleaving
               //          verifying just the .fsti does not need this admit
               //          but when verifying the .fst, this definition does not verify
               //          my suspicion is some options going wrong
    B.as_seq h tag == Spec.Hash.hash a b

val extract_hash
  (#a:alg)
  (s:state)
  (tag:Hacl.Hash.Definitions.hash_t a)
  : ST unit
       (requires (fun h0 ->
         invariant s h0 /\
         hash_alg s h0 == Some a /\
         B.live h0 tag /\
         B.loc_disjoint (footprint s h0) (B.loc_buffer tag)))
       (ensures (fun h0 _ h1 ->
         let open B in
         frame_state s h0 h1 /\
         invariant s h1 /\
         modifies (loc_union (footprint s h1) (loc_buffer tag)) h0 h1 /\
         buf_is_hash_of_b a tag h1 (transcript_bytes (transcript s h1))))

(* We need some form of collision resistance adapted to transcripts.
   i.e., if the hashes of two transcripts match then the transcripts
   themselves do.
*)
