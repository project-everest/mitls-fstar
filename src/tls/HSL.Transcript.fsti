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
module C = LowStar.ConstBuffer
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
module Psks = Parsers.OfferedPsks
module PB = ParsersAux.Binders

//TODO: move to a separate module
let repr_hs12 (b:R.const_slice) =
  R.repr_p _ b HSM12.handshake12_parser

//TODO: move to a separate module
let repr_hs13 (b:R.const_slice) =
  R.repr_p _ b HSM13.handshake13_parser

type bytes = FStar.Seq.seq uint_8

/// `hs_ch` and `hs_sh`: Abbreviations for handshake messages that
/// hold client and server hellos, respectively
let hs_ch = ch:HSM.handshake{HSM.M_client_hello? ch}
let hs_sh = sh:HSM.handshake{HSM.M_server_hello? sh}

/// `is_hrr`: For now, we assume the existence of a pure function to
/// decide if a server-hello message is a hello-retry-request (hrr)
// assume
val is_hrr (sh:SH.serverHello) : bool


/// `retry`: a pair of a client hello and hello retry request
type retry =
  CH.clientHello & s:SH.serverHello{is_hrr s}

////////////////////////////////////////////////////////////////////////////////
// Truncated client hellos
////////////////////////////////////////////////////////////////////////////////

/// `hs_tch`: Handshake message holding a truncated client hello
///
/// Truncated client hellos are related to pre-shared keys.
///
/// See https://tlswg.org/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.11
///
/// Broadly, the server selects a particular PSK binder to validate.
///
/// Validation involves checking the hash of the transcript up to the
/// truncated client hello under a PSK binder key. Note, this may be
/// more than just the truncated client hello, since the transcript
/// may also include a hello-retry request.
///
/// At the client side, in order to prepare the client hello message,
/// the client prepares a draft client hello with default binders of
/// the appropriate length. It then repeatedly hashes the truncation
/// of this draft client hello to compute the binder values, each time
/// perhaps using a different hashing algorithm (as determined by the
/// PSK identity).

let clientHello_with_binders = ch:CH.clientHello {
  PB.has_binders (HSM.M_client_hello ch)
}

let binders_len = len:uint_32{
  35 <= UInt32.v len /\
  UInt32.v len <= 65537
}

/// TODO: check with Tahina how to implement this function
let tch_binders_len (ch:clientHello_with_binders)
  : Tot (b:binders_len {
           let hs_ch = HSM.M_client_hello ch in
           UInt32.v b =
           Psks.offeredPsks_binders_bytesize
             (PB.get_binders hs_ch) /\
           UInt32.v b =
           Seq.length
             (LP.serialize
               Psks.offeredPsks_binders_serializer
                 (PB.get_binders hs_ch))
         })
  = let hs_ch = HSM.M_client_hello ch in
    Psks.offeredPsks_binders_bytesize_eq (PB.get_binders hs_ch);
    Psks.offeredPsks_binders_size32 (PB.get_binders hs_ch)
    // UInt32.uint_to_t (Psks.offeredPsks_binders_bytesize (PB.get_binders ch))

let hs_tch = tch:clientHello_with_binders{
  PB.get_binders (HSM.M_client_hello tch) ==
  PB.build_canonical_binders (tch_binders_len tch)
}

/// `truncate`: A specificational version of truncation
/// which replaces the binders of a client hellow with canonical binders
/// of the appropriate length
let truncate (ch:clientHello_with_binders)
  : GTot hs_tch
  = let cb = PB.build_canonical_binders (tch_binders_len ch) in
    let hs_ch = HSM.M_client_hello ch in
    let tch = PB.set_binders hs_ch cb in
    PB.truncate_clientHello_bytes_set_binders hs_ch cb;
    HSM.M_client_hello?._0 tch


/// `nego_version`: This is to be provided eventually by a refactoring
/// of the Negotiation module.
val nego_version (ch:CH.clientHello)
                 (sh:SH.serverHello)
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

  | ClientHello:
      retried:option retry ->
      ch:CH.clientHello ->
      transcript_t

  | TruncatedClientHello:
      retried:option retry ->
      tch:hs_tch ->
      transcript_t

  | Transcript12:
      ch:CH.clientHello ->
      sh:SH.serverHello{nego_version ch sh == PV.TLS_1p2} ->
      rest:bounded_list HSM12.handshake12 max_transcript_size ->
      transcript_t

  | Transcript13:
      retried:option retry ->
      ch:CH.clientHello ->
      sh:SH.serverHello{nego_version ch sh == PV.TLS_1p3} ->
      rest:bounded_list HSM13.handshake13 max_transcript_size ->
      transcript_t

/// `transcript_size`: the size of a transcript is the length of its
/// protocol-specific suffix
let transcript_size (t:transcript_t) =
    match t with
    | Start _
    | ClientHello _ _
    | TruncatedClientHello _ _ -> 0
    | Transcript12 _ _ rest -> List.length rest
    | Transcript13 _ _ _ rest -> List.length rest

/// `extensible`: a transcript is extensible if it is smaller than
/// `max_transcript_size`
let extensible (t:transcript_t) = transcript_size t < max_transcript_size - 1
let ext_transcript_t = t:transcript_t{extensible t}

(* A depiction of the state machine for transcript hashes


   Start None ----ch--> Hello None ch ---------------.-------------.
      |                     ^                        |             |
      |                     |                       sh13         sh12
      |                  complete_tch                |             |
      |                     |                        v             v
      .---------tch---> TCH None tch         Transcript13 None ... Transcript12 None ...
      |                                        |          ^           |          ^
      |                                        |          |           |          |
      |                                        .---hsm13--.           .---hsm12--.
     hrr
      |                               Transcript13 (Some hrr)
      |                                |         ^    ^
      |                                |         |    |
      |                                .--hsm13--.   sh13
      v                                               |
   Start (Some hrr) --ch-> Hello (Some hrr) ch -------.
      |                         ^
      |                         |
      |                       complete_tch
      |                         |
      .---------tch------> TCH (Some hrr) tch

   The machine is roughly structured as two copies of the same
   machine, related by a hello-retry-request (hrr) transition. Note,
   hrr is only in TLS1.3---so once that transition is taken, one can
   no longer reach that Transcript12 state.

   One subtlety is that, in practice, the client side of the protocol
   takes a slightly different path through the machine than the
   server. In the upper half of the machine (i.e., before hrr), the
   client does not know which hashing algorithm will be
   negotiated. But, it still needs to construct offered psk binders
   using truncated client hellos. So, an expected usage is that the
   client creates many instances of the of the transcript hash for
   each hash algorithm prescribed by each chosen binder; computes the
   hash of the truncated client hello and populates the binder value.

   Further, in the case of 0-RTT keys, the client optimistically uses
   computes a key using the hash of entire client hello using the
   hashing algorithm of the first PSK identity: in this scenario, the
   first transcript hash instance created above transitions from the
   TCH state to the Hello state using the complete_tch transition.

   Additionally, if/when the server picks a particular hashing
   algorithm/binder, the client may constructs a new transcript
   instance with that algorithm and moves from `Start None` to `Hello
   None ch` atomically, rather than via the `TCH` state.

   OTOH, once an hrr message is sent, the hashing algorithm is already
   chosen by the server and the client can move to the `Hello` state
   via `TCH` (in the bottom half of the picture), just as the server.

   Another subtlety is that the sh13 transitions shown above should
   not be enabled for ServerHello messages that are actually hello
   retry requests: however, we do not enforce that restriction in this
   state machine, leaving it to upper layers (the handshake state
   machine) to enforce.
 *)

/// The state machine above is split into several transition functions
/// for convenience and ease of typability (note, the labels that
/// guard the transitions do not all have the same type)

(** TRANSITIONS **)

noeq
type label =
  | L_ClientHello of CH.clientHello
  | L_ServerHello of SH.serverHello
  | L_TCH of clientHello_with_binders
  | L_CompleteTCH of clientHello_with_binders
  | L_HRR of retry
  | L_HSM12 of HSM12.handshake12
  | L_HSM13 of HSM13.handshake13

let transition (t:transcript_t) (l:label)
  : GTot (option transcript_t)
  = match t, l with
    | Start None, L_HRR retry ->
      Some (Start (Some retry))

    | Start retry, L_ClientHello ch ->
      Some (ClientHello retry ch)

    | Start retry, L_TCH ch ->
      Some (TruncatedClientHello retry (truncate ch))

    | TruncatedClientHello retry tch, L_CompleteTCH ch ->
      if tch = truncate ch
      then Some (ClientHello retry ch)
      else None

    | ClientHello retry ch, L_ServerHello sh ->
      begin
      match nego_version ch sh, retry with
      | PV.TLS_1p2, None ->
        Some (Transcript12 ch sh [])

      | PV.TLS_1p3, _ ->
        Some (Transcript13 retry ch sh [])

      | _ -> None
      end

    | Transcript12 ch sh rest, L_HSM12 m ->
      let msgs = List.snoc (rest, m) in
      if List.length msgs < max_transcript_size
      then Some (Transcript12 ch sh msgs)
      else None

    | Transcript13 retry ch sh rest, L_HSM13 m ->
      let msgs = List.snoc (rest, m) in
      if List.length msgs < max_transcript_size
      then Some (Transcript13 retry ch sh msgs)
      else None

    | _ -> None

let ( ~~> ) (t1 t2:transcript_t) =
  t1 == t2 \/
  (exists l. Some t2 == transition t1 l)

(* TODO: Transitive closure of ~~>
 let ( ~~>* ) (t1 t2:transcript_t) =
  exists l. Some t2 == transition t1 l
*)

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

let hs_ch_repr b = ch:R_HS.repr b { R_HS.is_ch ch }
let hs_sh_repr b = sh:R_HS.repr b { R_HS.is_sh sh }

noeq
type label_repr =
  | LR_ClientHello:
       #b:R.const_slice ->
       ch:hs_ch_repr b ->
       label_repr

  | LR_ServerHello:
       #b:R.const_slice ->
       ch:hs_sh_repr b ->
       label_repr

  | LR_TCH:
      #b:R.const_slice ->
      ch:hs_ch_repr b{PB.has_binders (R.value ch)} ->
      label_repr

  | LR_CompleteTCH:
      #b:R.const_slice ->
      ch:hs_ch_repr b{PB.has_binders (R.value ch)} ->
      label_repr

  | LR_HRR:
      #b1:R.const_slice ->
      ch:hs_ch_repr b1 ->
      #b2:R.const_slice ->
      hrr:hs_sh_repr b2{is_hrr (HSM.M_server_hello?._0 (R.value hrr))} ->
      label_repr

  | LR_HSM12:
      #b:R.const_slice ->
      hs12:repr_hs12 b ->
      label_repr

  | LR_HSM13:
      #b:R.const_slice ->
      hs13:repr_hs13 b ->
      label_repr

let label_of_label_repr (l:label_repr)
  : GTot label
  = match l with
    | LR_ClientHello ch ->
      L_ClientHello (HSM.M_client_hello?._0 (R.value ch))

    | LR_ServerHello sh ->
      L_ServerHello (HSM.M_server_hello?._0 (R.value sh))

    | LR_TCH ch ->
      L_TCH (HSM.M_client_hello?._0 (R.value ch))

    | LR_CompleteTCH ch ->
      L_CompleteTCH (HSM.M_client_hello?._0 (R.value ch))

    | LR_HRR ch sh ->
      L_HRR (HSM.M_client_hello?._0 (R.value ch),
             HSM.M_server_hello?._0 (R.value sh))

    | LR_HSM12 hs12 ->
      L_HSM12 (R.value hs12)

    | LR_HSM13 hs13 ->
      L_HSM13 (R.value hs13)


/// `valid_label`: Validity of the labels is simply the validity of
///  the message representations it contains
let valid_label_repr (l:label_repr) (h:HS.mem) =
  match l with
  | LR_HRR ch hrr ->
    R.valid ch h /\
    R.valid hrr h

  | LR_ClientHello r
  | LR_ServerHello r
  | LR_TCH r
  | LR_CompleteTCH r
  | LR_HSM12 r
  | LR_HSM13 r ->
    R.valid r h

/// `loc_of_label`: The footprint of a label is simply the union of
///  the footprints of all the message representations it contains
let loc_of_label_repr (l:label_repr) =
  match l with
  | LR_HRR #b1 _ #b2 _ ->
    B.loc_union
      (C.loc_buffer R.(b1.base))
      (C.loc_buffer R.(b1.base))

  | LR_ClientHello #b _
  | LR_ServerHello #b _
  | LR_TCH #b _
  | LR_CompleteTCH #b _
  | LR_HSM12 #b _
  | LR_HSM13 #b _ ->
    C.loc_buffer R.(b.base)

/// `extend`: The single, concrete state transition function
///
///   `extend s l tx` transitions and returns the new state tx'
///    in case the transition is enabled.
///
///    Internally, it extends the running hash of the transcript
///
///    It requires
///      -- state machine invariant
///      -- validity of message representations in the label
///      -- disjointness of machine state and label state
///      -- extensibility of the transcript
///      -- and that the transition be enabled
///
///    It ensures
///      -- state machine invariant
///      -- that it mutates only the state machine's footprint
///      -- that the new state is the one computed by the transition
val extend (#a:_) (s:state a) (l:label_repr) (tx:G.erased transcript_t)
  : Stack (G.erased transcript_t)
    (requires fun h ->
        let tx = G.reveal tx in
        invariant s tx h /\
        valid_label_repr l h /\
        B.loc_disjoint (loc_of_label_repr l) (footprint s) /\
        extensible tx /\
        Some? (transition tx (label_of_label_repr l)))
    (ensures fun h0 tx' h1 ->
        let tx = G.reveal tx in
        let tx' = G.reveal tx' in
        invariant s tx' h1 /\
        B.modifies (footprint s) h0 h1 /\
        tx' == Some?.v (transition tx (label_of_label_repr l)))


(*** Hashes and injectivity ***)

/// `transcript_hash`: The specificational hash of the transcript
val transcript_hash (a:HashDef.hash_alg) (t:transcript_t)
  : GTot (b: HashDef.lbytes (HashDef.hash_length a))


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
    (requires fun h0 ->
      let tx = G.reveal tx in
      invariant s tx h0 /\
      B.live h0 tag /\
      B.loc_disjoint (footprint s) (B.loc_buffer tag))
    (ensures fun h0 _ h1 ->
      let open B in
      let tx = G.reveal tx in
      invariant s tx h1 /\
      modifies (loc_union (footprint s) (loc_buffer tag)) h0 h1 /\
      B.live h1 tag /\
      B.as_seq h1 tag == transcript_hash a tx)


/// `injectivity`: The main lemma provided by this module is a form of
///  collision resistance adapted to transcripts, i.e., if the hashes
///  of two transcripts match then the transcripts themselves do.

/// TODO, still need to understand how to state this in terms of
/// Hashing.CRF
///
/// Something like

// val injectivity (a:HashDef.hash_alg) (tx1 tx2:G.erased transcript_t)
//   : Stack unit
//     (requires fun h ->
//       hashed a tx1 /\
//       hashed a tx2)
//     (ensures fun h0 _ h1 ->
//       h0 == h1 /\
//       (crf a /\
//        transcript_hash a tx1 == transcript_hash a tx2 ==>
//        tx1 == tx2))
