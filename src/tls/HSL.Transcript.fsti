(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: C. Fournet, T. Ramananandro, A. Rastogi, N. Swamy
*)
module HSL.Transcript
//Should this be called MITLS.TranscriptHash?

(* Summary:

   This module provides support for the transcript hash,
   as described in:

   https://tlswg.org/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.4.1

   Concretely, it is just an encapsulation of
   EverCrypt.Hash.Incremental, maintaining an incremental hash of a
   sequence of messages, as requested by its callers. At any point,
   the current value of the hash can be extracted into a
   caller-provided buffer.

   However, abstractly, it constructs an (erased) "transcript", a
   protocol-version-specific sequence of messages, maintaining an
   invariant that correlates the transcript with the state of the
   incremental hash.

   The main proof provided by the module is an injectivity property,
   based on a collision-resistance property of the underlying hashing
   algorithm: agreement on hashed values implies agreement on the
   transcript.
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
module HashDef = Spec.Hash.Definitions

module R = MITLS.Repr
module R_HS = MITLS.Repr.Handshake

module R_CH = MITLS.Repr.ClientHello
module CH = Parsers.ClientHello

module R_SH = MITLS.Repr.ServerHello
module SH = Parsers.ServerHello


//TODO: move to a separate module
let repr_hs12 (b:R.slice) =
  R.repr_p _ b HSM12.handshake12_parser

//TODO: move to a separate module
let repr_hs13 (b:R.slice) =
  R.repr_p _ b HSM13.handshake13_parser

type bytes = FStar.Seq.seq uint_8

/// `hs_ch` and `hs_sh`: Abbreviations for handshake messages that
/// hold client and server hellos, respectively
let hs_ch = ch:HSM.handshake{HSM.M_client_hello? ch}
let hs_sh = sh:HSM.handshake{HSM.M_server_hello? sh}

/// `is_hrr`: For now, we assume the existence of a pure function to
/// decide if a server-hello message is a hello-retry-request (hrr)
// assume
val is_hrr (sh:hs_sh) : bool

/// `hello_retry_request`: The type of HRR messages
inline_for_extraction
let hello_retry_request : Type0 =
  s:hs_sh { is_hrr s }

/// `retry`: a pair of a client hello and hello retry request
type retry =
  hs_ch
  & hello_retry_request

/// `client_hello_has_psk`: A client hello has a pre-shared key if
///    that mode appears in one of its extensions
let client_hello_has_psk (ch:CH.clientHello) =
  exists (ext:_).
    List.memP ext Parsers.ClientHello.(ch.extensions) /\
    Parsers.ClientHelloExtension.CHE_pre_shared_key? ext /\
    True (* what else do we need? e.g., that it has as many binders as ids? *)

/// `nego_version`: This is to be provided eventually by a refactoring
/// of the Negotiation module.
// assume
val nego_version (ch:hs_ch)
                 (sh:hs_sh)
       : PV.protocolVersion

/// `max_transcript_size` and `max_message_size`:
///
/// Some complications arise from the maximum size of transcript
/// hashes, since the EverCrypt API imposes a maximum number of bytes
/// that can be accumulated in an incremental hash (2^61 or 2^125,
/// depending on the choice of algorithm). Given that each message is
/// bounded in size by `max_message_size` (2^24), we conservatively
/// bound the size of the transcript (`max_transcript_size`) to 2^32
/// messages so that client code an easily track its length with a
/// u32.
///
/// Note, `max_transcript_size` should be at least
///  max (handshake12_parser_kind.parser_kind_high,
///       handshake13_parser_kind.parser_kind_high,
///       handshake_parser_kind.parser_kind_high)
unfold
let max_message_size = normalize_term (pow2 24)

unfold
let max_transcript_size : pos = normalize_term (pow2 32)


/// This lemma proves that the maximum size in bytes of a transcript
/// is smaller than the bound imposed by the Hash API
let max_message_size_lt_max_input_length (a: HashDef.hash_alg)
  : Lemma
    ((max_transcript_size + 4) * max_message_size < HashDef.max_input_length a)
    [SMTPat (Spec.Hash.Definitions.max_input_length a)]
  = assert_norm ((max_transcript_size + 4) * max_message_size < pow2 61);
    assert_norm ((max_transcript_size + 4) * max_message_size < pow2 125)

/// Move to the FStar.List library?
let bounded_list 'a n = l:list 'a{List.length l < n}

(*** Main state machine ***)

(** STATES **)

/// `transcript_t`: Transcript for 1.2 and 1.3 have a shared prefix
/// and then fork to version-specific message types
///
///   Note, HSM.handshake is the type of messages before the version
///   is negotiated and so does not contain either HSM12 or HSM13
///   messages. The three types are disjoint and parsed independently.
///
/// Further, each of the first two states have a variant in support of
/// hello-retry requests. The transcript hash records the full
/// transcript, including the retry, if any. Note, the standard
/// forbids multiple retries.
noeq
type transcript_t =
  | Start:
      retried:option retry ->
      transcript_t

  | Hello:
      retried:option retry ->
      ch:hs_ch ->
      transcript_t

  | Transcript12:
      ch:hs_ch ->
      sh:hs_sh{nego_version ch sh == PV.TLS_1p2} ->
      rest:bounded_list HSM12.handshake12 max_transcript_size ->
      transcript_t

  | Transcript13:
      retried:option retry ->
      ch:hs_ch ->
      sh:hs_sh{nego_version ch sh == PV.TLS_1p3} ->
      rest:bounded_list HSM13.handshake13 max_transcript_size ->
      transcript_t

/// `transcript_size`: the size of a transcript is the length of its
/// protocol-specific suffix
let transcript_size (t:transcript_t) =
    match t with
    | Start _
    | Hello _ _ -> 0
    | Transcript12 _ _ rest -> List.length rest
    | Transcript13 _ _ _ rest -> List.length rest

/// `extensible`: a transcript is extensible if it is smaller than
/// `max_transcript_size`
let extensible (t:transcript_t) = transcript_size t < max_transcript_size - 1
let ext_transcript_t = t:transcript_t{extensible t}

/// `transcript_bytes`: The input of the hash algorithm computed by
/// concatenated the message formatting of the messages
val transcript_bytes (t:transcript_t)
  : GTot (b: bytes {
       Seq.length b <= (max_transcript_size + 4) * max_message_size
    })

(** TRANSITIONS **)

/// `extend_with_hsm`: The main transition function
///
///    Dictates which next state to transition to (if any) from a
///    given transcript and a message
let transition_hsm
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
        match nego_version ch m, retry with
        | PV.TLS_1p2, None ->
          Some (Transcript12 ch m [])

        | PV.TLS_1p3, _ ->
          Some (Transcript13 retry ch m [])

        | _ -> None
        end

    | _ ->
      None

/// `transition_hrr`:
///    An auxiliary transition function, specific to TLS1.3
///    that handles hello-retry requests
let transition_hrr
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

/// `transition_hsm12`:
///    An auxiliary transition function, specific to TLS1.2
///    It only enforces the length constraint on the suffix
let transition_hsm12 (t:ext_transcript_t) (m:HSM12.handshake12)
  : option transcript_t
  = match t with
    | Transcript12 ch sh rest ->
      List.append_length rest [m];
      Some (Transcript12 ch sh (List.snoc (rest, m)))

    | _ -> None

/// `transition_hsm13`:
///    An auxiliary transition function, specific to TLS1.3
///    It only enforces the length constraint on the suffix
let transition_hsm13 (t:ext_transcript_t) (m:HSM13.handshake13)
  : option transcript_t
  = match t with
    | Transcript13 retry ch sh rest ->
      List.append_length rest [m];
      Some (Transcript13 retry ch sh (List.snoc (rest, m)))

    | _ -> None

(*** Concrete state and transitions ***)


/// `state`: Abstract state of the module
///
/// It maintains the transcript in mutable state.
///
/// We may need a way to free the state also, although if it is
/// allocated in a connection-granularity region, it will be reclaimed
/// along with that region.
val state (a:HashDef.hash_alg) : Type0

/// `invariant s t h`: Relates the state of the module (i.e., the
/// state of the underlying incremental hash) to the a particular
/// transcript
val invariant (#a: _) (s:state a) (t:transcript_t) (h:HS.mem) : Type0

/// `footprint`: Abstract memory footprint
val footprint (#a:_) (s:state a) : GTot B.loc

/// `elim_invariant`: One way to eliminate the invariant is simply to
///  recover that the memory footprint of the module is used in the
///  memory state `h`. Withouth this, it is not possible to prove that
///  a freshly allocated location doesn't interfere with the abstract
///  footprint of this module.
val elim_invariant (#a: _) (s:state a) (t:transcript_t) (h:HS.mem)
  : Lemma
    (requires invariant s t h)
    (ensures B.loc_not_unused_in h `B.loc_includes` footprint s)

/// `region_of`: The internal state of the module is allocated in a
/// user-provided region
val region_of (#a: _) (s:state a)
  : GTot HS.rid

/// `frame_invariant`: The invariant is maintained across
/// footprint-preserving heap modifications
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

/// `create`: Allocating a new instance of the transcript hash
///
///   -- Caller provides a region `r` in which to allocate a
///      transcript instance
///
///   -- The instance is allocated in fresh state (so `modifies none`)
///
///   -- The transcript's initial state is empty
val create (r:Mem.rgn) (a:HashDef.hash_alg)
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

(** CONCRETE STATE TRANSITIONS **)

/// `extend_pre_common`: Every state transition
/// has some basic requirements
///   -- state machine invariant
///   -- validity of message representations
///   -- disjointness of machine state and representation state
///   -- extensibility of the transcript
unfold
let extend_pre_common
  #a (s:state a)
  #t (#b:R.slice) (r:R.repr t b)
  (tx:transcript_t) (h:HS.mem)
  = invariant s tx h /\
    R.valid r h /\
    B.loc_disjoint (B.loc_buffer LP.(b.base)) (footprint s) /\
    extensible tx

/// `extend_hash_post_common`: Every state transition
/// has some basic guarantees
///   -- state machine invariant
///   -- mutates only the state machine's footprint
unfold
let extend_post_common
  #a (s:state a) (t:transcript_t) (h0 h1:HS.mem)
  = invariant s t h1 /\
    B.modifies (footprint s) h0 h1

/// `extend_hsm`: The main transition
///    - the state evolves according to `transition_hsm`
val extend_hsm
  (#a:_) (s:state a)
  (#b:R.slice) (r:R_HS.repr b)
  (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      extend_pre_common s r tx h /\
      Some? (transition_hsm tx (R.value r)))
    (ensures fun h0 tx' h1 ->
      let tx = G.reveal tx in
      let tx' = G.reveal tx' in
      tx' == Some?.v (transition_hsm tx (R.value r)) /\
      extend_post_common s tx' h0 h1)

/// `extend_hsm12`: Append to Transcript12
///    - the state evolves according to `transition_hsm12`
val extend_hsm12
  (#a:_) (s:state a)
  (#b:R.slice) (r:repr_hs12 b)
  (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      extend_pre_common s r tx h /\
      Some? (transition_hsm12 tx (R.value r)))
    (ensures fun h0 tx' h1 ->
      let tx = G.reveal tx in
      let tx' = G.reveal tx' in
      tx' == Some?.v (transition_hsm12 tx (R.value r)) /\
      extend_post_common s tx' h0 h1)

/// `extend_hsm13`: Append to Transcript13
///    - the state evolves according to `transition_hsm13`
val extend_hsm13
  (#a:_) (s:state a)
  (#b:R.slice) (r:repr_hs13 b)
  (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      extend_pre_common s r tx h /\
      Some? (transition_hsm13 tx (R.value r)))
    (ensures fun h0 tx' h1 ->
      let tx = G.reveal tx in
      let tx' = G.reveal tx' in
      tx' == Some?.v (transition_hsm13 tx (R.value r)) /\
      extend_post_common s tx' h0 h1)

/// `extend_ch_with_psk`:
///
///    This is a specialized transition used by the server to process
///    client hello's with pre-shared key binders.
///
///    See https://tlswg.org/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.11
///
///    Broadly, the server selects a particular PSK binder to validate.
///
///    Validation involves checking the hash of the transcript up to
///    the truncated client hello under a PSK binder key. Note, this
///    may be more than just the truncated client hello, since the
///    transcript may als include a hello-retry request.
///
///    This function does the following:
///
///      - truncates the client hello (until just before the first PSK
///        binder)
///
///      - extends the transcript hash with the truncation, extracts
///        that hash to a freshly allocation on the stack (in the
///        caller's stack frame; note the `StackInline`)
///
///      - then extends the transcript hash to with the suffix of the
///        client hello (i.e., all the binders excluded by the truncation)
///
///      - and correspondingly transitions the state machine to
///        include the entire client hello
val extend_ch_with_psk
  (#a:_) (s:state a)
  (#b:R.slice) (r:R_HS.repr b)
  (tx:G.erased transcript_t)
  : StackInline
      (Hacl.Hash.Definitions.hash_t a &
       G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      let hs = R.value r in
      extend_pre_common s r tx h /\
      Start? tx /\
      HSM.M_client_hello? hs /\
      client_hello_has_psk (HSM.M_client_hello?._0 hs))
    (ensures fun h0 (hash, tx') h1 ->
      let tx = G.reveal tx in
      let tx' = G.reveal tx' in
      B.fresh_loc (B.loc_buffer hash) h0 h1 /\
      B.live h1 hash /\
      tx' == Hello (Start?.retried tx) (R.value r) /\
      extend_post_common s tx' h0 h1)

/// `extend_hrr`: Hello retry requests
///     See https://tlswg.org/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.1.4
///  Transitions according to `transition_hrr`
val extend_hrr
  (#a:_) (s:state a)
  (#b:R.slice) (r_ch:R_HS.repr b)
  (#b':R.slice) (r_sh:R_HS.repr b')
  (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
    (requires fun h ->
      let tx = G.reveal tx in
      extend_pre_common s r_sh tx h /\
      Some? (transition_hrr tx (R.value r_ch) (R.value r_sh)))
    (ensures fun h0 tx' h1 ->
      let tx = G.reveal tx in
      let tx' = G.reveal tx' in
      tx' == Some?.v (transition_hrr tx (R.value r_ch) (R.value r_sh)) /\
      extend_post_common s tx' h0 h1)

(*** Extracting hashes and injectivity ***)

/// `extract_hash`:
///
///   At any point, we can extract the current state of thea
///   incremental hash into a user-provided buffer to store the tag
///
///   The post-condition ensures that the tag contains a hash of the
///   transcript bytes
val extract_hash
  (#a:_) (s:state a)
  (tag:Hacl.Hash.Definitions.hash_t a)
  (tx:G.erased transcript_t)
  : Stack unit
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


/// `injectivity`: The main lemma provided by this module is a form of
///  collision resistance adapted to transcripts, i.e., if the hashes
///  of two transcripts match then the transcripts themselves do.
val injectivity (a:HashDef.hash_alg) (tx1 tx2:G.erased transcript_t)
  : Lemma
    (ensures (
      let tx1 = G.reveal tx1 in
      let tx2 = G.reveal tx2 in
      Spec.Hash.hash a (transcript_bytes tx1) ==
      Spec.Hash.hash a (transcript_bytes tx2) ==>
      tx1 == tx2))
