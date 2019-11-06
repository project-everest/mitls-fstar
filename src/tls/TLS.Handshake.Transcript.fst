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

  Authors: C. Fournet, A. Fromherz, T. Ramananandro, A. Rastogi, N. Swamy
*)
module TLS.Handshake.Transcript
open FStar.Integers
open FStar.HyperStack.ST
module List = FStar.List.Tot
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module HSM = HandshakeMessages

module PV = Parsers.ProtocolVersion
module LP = LowParse.Low.Base

module R = LowParse.Repr
module R_HS = MITLS.Repr.Handshake
module R_CH = MITLS.Repr.ClientHello
module R_SH = MITLS.Repr.ServerHello
module CRF = Crypto.CRF
module TestCRF = Test.CRF
module PB = ParsersAux.Binders
#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 16"

//Seems to be automatic
let serialize_max_size
  (#pk:_) (#t:_) (#p:LP.parser pk t) (s:LP.serializer p)
  (x:t)
: Lemma
  (requires (
    match pk.LP.parser_kind_high with
    | None -> False
    | Some n -> n < max_message_size
  ))
  (ensures (
    Seq.length (LP.serialize s x) < max_message_size
  ))
= ()

module LPSL = LowParse.Spec.List

val serialize_list_max_size
  (#pk:_) (#t:_) (#p:LP.parser pk t) (s:LP.serializer p)
  (x:list t)
: Lemma
  (requires (
    LPSL.serialize_list_precond pk /\ (
    match pk.LP.parser_kind_high with
    | None -> False
    | Some n -> n < max_message_size
  )))
  (ensures (
    Seq.length (LP.serialize (LPSL.serialize_list _ s) x) <= List.Tot.length x * max_message_size
  ))
//  [SMTPat (Seq.length (LP.serialize (LPSL.serialize_list _ s) x))]


let rec serialize_list_max_size #pk #t #p s x =
  match x with
  | [] -> LPSL.serialize_list_nil p s
  | hd::tl -> LPSL.serialize_list_cons p s hd tl; serialize_list_max_size s tl

let serialize_any_tag (ht:any_hash_tag) =
    LP.serialize HSM.handshake_serializer ht // (Parsers.Handshake.M_message_hash ht)

let serialize_client_hello (ch:HSM.clientHello) =
  LP.serialize HSM.handshake_serializer (HSM.M_client_hello ch)

let serialize_server_hello (sh:HSM.serverHello) =
  LP.serialize HSM.handshake_serializer (HSM.M_server_hello sh)

let serialize_retry (r:option retry)
  : GTot (b:bytes{Seq.length b < 2 * max_message_size })
  =
  match r with
  | None -> Seq.empty
  | Some (ht, sh) ->
    serialize_any_tag ht `Seq.append`
    serialize_server_hello sh

let transcript_bytes (t:transcript_t)
  : GTot (b:bytes {
    Seq.length b <= (max_transcript_size + 4) * max_message_size
    })
  = match t with
  | Start r ->
    serialize_retry r

  | TruncatedClientHello r tch ->
    serialize_retry r `Seq.append`
    FStar.Bytes.reveal (PB.truncate_clientHello_bytes (HSM.M_client_hello tch))

  | ClientHello r ch ->
    serialize_retry r `Seq.append`
    serialize_client_hello ch

  | Transcript12 ch sh rest ->
    serialize_list_max_size HSM.handshake12_serializer rest;
    serialize_client_hello ch `Seq.append` (
    serialize_server_hello sh `Seq.append`
    LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest
    )

  | Transcript13 retry ch sh rest ->
    serialize_list_max_size HSM.handshake13_serializer rest;
    serialize_retry retry `Seq.append` (
    serialize_client_hello ch `Seq.append` (
    serialize_server_hello sh `Seq.append` (
    LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest
    )))

let transcript_is_empty (t: transcript_t)
  : GTot bool
  = match t with
    | Start None -> true
    | _ -> false

let transcript_get_retry (t: transcript_t)
  : GTot (option retry)
  = match t with
    | Start r -> r
    | TruncatedClientHello r _ -> r
    | ClientHello r _ -> r
    | Transcript12 _ _ _ -> None
    | Transcript13 r _ _ _ -> r

let transcript_set_retry (t: transcript_t) (r: option retry { Transcript12? t ==> None? r }) : Tot transcript_t =
  match t with
  | Start _ -> Start r
  | TruncatedClientHello _ tch -> TruncatedClientHello r tch
  | ClientHello _ ch -> ClientHello r ch
  | Transcript12 ch sh rest -> Transcript12 ch sh rest
  | Transcript13 _ ch sh rest -> Transcript13 r ch sh rest

let transcript_script_bytes (t: transcript_t)
  : Lemma
    (ensures
      transcript_bytes t `Seq.equal`
      (serialize_retry (transcript_get_retry t) `Seq.append` transcript_bytes (transcript_set_retry t None)))
= ()

let seq_append_empty ()
  : Lemma
    (ensures
      FStar.Seq.(forall (s: seq LP.byte) . {:pattern (empty `append` s)} empty `append` s == s))
  = FStar.Seq.(assert (forall (s: seq LP.byte) . {:pattern (empty `append` s)} (empty `append` s) `equal` s))

let transcript_bytes_does_not_start_with_message_hash
  (t: transcript_t)
  (r: retry)
  (q: Seq.seq FStar.UInt8.t)
  : Lemma
    (requires
      transcript_get_retry t == None /\
      transcript_bytes t == serialize_retry (Some r) `Seq.append` q)
    (ensures False)
  = let ht, hrr = r in
    seq_append_empty();
    assert (transcript_bytes t `Seq.equal`
      (serialize_any_tag ht `Seq.append` (serialize_server_hello hrr `Seq.append` q)));
    match t with
    | ClientHello _ ch ->
      assert (transcript_bytes t `Seq.equal` (serialize_client_hello ch `Seq.append` Seq.empty));
      LP.serialize_strong_prefix HSM.handshake_serializer
        ht (HSM.M_client_hello ch)
        (serialize_server_hello hrr `Seq.append` q)
        Seq.empty

    | TruncatedClientHello _ tch ->
      PB.parse_truncate_clientHello_bytes (HSM.M_client_hello tch);
      LP.parse_strong_prefix HSM.handshake_parser
        (serialize_any_tag ht)
        (Bytes.reveal (PB.truncate_clientHello_bytes (HSM.M_client_hello tch)))

    | Transcript12 ch sh rest ->
      LP.serialize_strong_prefix HSM.handshake_serializer
        ht (HSM.M_client_hello ch)
        (serialize_server_hello hrr `Seq.append` q)
        (serialize_server_hello sh `Seq.append`
          LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest)

    | Transcript13 _ ch sh rest ->
      LP.serialize_strong_prefix HSM.handshake_serializer
        ht (HSM.M_client_hello ch)
        (serialize_server_hello hrr `Seq.append` q)
        (serialize_server_hello sh `Seq.append`
          LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest)

#push-options "--z3rlimit 32"
let transcript_bytes_injective_retry
  (r1: option retry)
  (t1: transcript_t { transcript_get_retry t1 == None } )
  (r2: option retry)
  (t2: transcript_t { transcript_get_retry t2 == None } )
  : Lemma
    (requires
      serialize_retry r1 `Seq.append` transcript_bytes t1 ==
      serialize_retry r2 `Seq.append` transcript_bytes t2)
    (ensures
      r1 == r2 /\
      transcript_bytes t1 `Seq.equal` transcript_bytes t2)
  = seq_append_empty ();
    match r1, r2 with
    | None, None -> ()
    | Some (ht1, sh1), Some (ht2, sh2) ->
      assert ((serialize_retry r1 `Seq.append` transcript_bytes t1) `Seq.equal`
              (serialize_any_tag ht1 `Seq.append` (serialize_server_hello sh1 `Seq.append` transcript_bytes t1)));
      assert ((serialize_retry r2 `Seq.append` transcript_bytes t2) `Seq.equal`
              (serialize_any_tag ht2 `Seq.append` (serialize_server_hello sh2 `Seq.append` transcript_bytes t2)));
      LP.serialize_strong_prefix HSM.handshake_serializer ht1 ht2
        (serialize_server_hello sh1 `Seq.append` transcript_bytes t1)
        (serialize_server_hello sh2 `Seq.append` transcript_bytes t2);
      LP.serialize_strong_prefix HSM.handshake_serializer
        (HSM.M_server_hello sh1) (HSM.M_server_hello sh2)
        (transcript_bytes t1) (transcript_bytes t2)
    | Some r1, _ ->
      transcript_bytes_does_not_start_with_message_hash t2 r1 (transcript_bytes t1)
    | _, Some r2 ->
      transcript_bytes_does_not_start_with_message_hash t1 r2 (transcript_bytes t2)
#pop-options

let transcript_arbitrary_index (t1: transcript_t)
  : GTot nat
  = match t1 with
    | Start _ -> 0
    | TruncatedClientHello _ _ -> 1
    | ClientHello _ _ -> 2
    | Transcript12 _ _ _ -> 3
    | Transcript13 _ _ _ _ -> 4

let seq_append_empty_r ()
  : Lemma
    (ensures
      (forall (s: Seq.seq LP.byte) . {:pattern (s `Seq.append` Seq.empty)} s `Seq.append` Seq.empty  == s))
  = FStar.Classical.forall_intro (Seq.append_empty_r #LP.byte)

let rec transcript_bytes_injective_no_retry
  (t1: transcript_t { transcript_get_retry t1 == None } )
  (t2: transcript_t { transcript_get_retry t2 == None } )
  : Lemma
    (requires
      transcript_bytes t1 `Seq.equal` transcript_bytes t2)
    (ensures
      t1 == t2)
    (decreases (transcript_arbitrary_index t2))
  = seq_append_empty ();
    if transcript_arbitrary_index t1 < transcript_arbitrary_index t2
    then transcript_bytes_injective_no_retry t2 t1
    else
      if Start? t2
      then ()
      else match t1 with
      | TruncatedClientHello _ tch1 ->
        begin
          match t2 with
          | TruncatedClientHello _ tch2 ->
            let tch1' = HSM.M_client_hello tch1 in
            let tch2' = HSM.M_client_hello tch2 in
          PB.truncate_clientHello_bytes_inj_binders_bytesize tch1' tch2';
          PB.set_binders_get_binders tch1';
          PB.set_binders_get_binders tch2';
          PB.truncate_clientHello_bytes_inj tch1' tch2' (PB.build_canonical_binders (ch_binders_len tch1))
        end
      | ClientHello _ ch1 ->
        begin
        match t2 with
        | TruncatedClientHello _ tch2 ->
          PB.parse_truncate_clientHello_bytes (HSM.M_client_hello tch2)
        | ClientHello _ ch2 ->
          LP.serializer_injective _ HSM.handshake_serializer (HSM.M_client_hello ch1) (HSM.M_client_hello ch2)
        end
      | Transcript12  ch1 sh1 rest1 ->
        begin
        match t2 with
        | TruncatedClientHello _ tch2 ->
          LP.parse_strong_prefix
            HSM.handshake_parser
            (LP.serialize HSM.handshake_serializer (HSM.M_client_hello ch1))
            (transcript_bytes t1);
          PB.parse_truncate_clientHello_bytes (HSM.M_client_hello tch2)
        | ClientHello _ ch2 ->
          seq_append_empty_r ();
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_client_hello ch1)
            (HSM.M_client_hello ch2)
            (serialize_server_hello sh1 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest1))
            Seq.empty
        | Transcript12 ch2 sh2 rest2 ->
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_client_hello ch1)
            (HSM.M_client_hello ch2)
            (serialize_server_hello sh1 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest1))
            (serialize_server_hello sh2 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest2));
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_server_hello sh1)
            (HSM.M_server_hello sh2)
            (LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest1)
            (LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest2);
          LP.serializer_injective _ (LPSL.serialize_list _ HSM.handshake12_serializer) rest1 rest2
        end
      | Transcript13 _ ch1 sh1 rest1 ->
        begin
        match t2 with
        | TruncatedClientHello _ tch2 ->
          LP.parse_strong_prefix
            HSM.handshake_parser
            (LP.serialize HSM.handshake_serializer (HSM.M_client_hello ch1))
            (transcript_bytes t1);
          PB.parse_truncate_clientHello_bytes (HSM.M_client_hello tch2)
        | ClientHello _ ch2 ->
          seq_append_empty_r ();
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_client_hello ch1)
            (HSM.M_client_hello ch2)
            (serialize_server_hello sh1 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest1))
            Seq.empty
        | Transcript12 ch2 sh2 rest2 ->
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_client_hello ch1)
            (HSM.M_client_hello ch2)
            (serialize_server_hello sh1 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest1))
            (serialize_server_hello sh2 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest2));
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_server_hello sh1)
            (HSM.M_server_hello sh2)
            (LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest1)
            (LP.serialize (LPSL.serialize_list _ HSM.handshake12_serializer) rest2);
          assert False
        | Transcript13 _ ch2 sh2 rest2 ->
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_client_hello ch1)
            (HSM.M_client_hello ch2)
            (serialize_server_hello sh1 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest1))
            (serialize_server_hello sh2 `Seq.append`
              (LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest2));
          LP.serialize_strong_prefix
            HSM.handshake_serializer
            (HSM.M_server_hello sh1)
            (HSM.M_server_hello sh2)
            (LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest1)
            (LP.serialize (LPSL.serialize_list _ HSM.handshake13_serializer) rest2);
          LP.serializer_injective _ (LPSL.serialize_list _ HSM.handshake13_serializer) rest1 rest2
        end

let transcript_bytes_injective (t1 t2:transcript_t)
  : Lemma
    (requires
      transcript_bytes t1 `Seq.equal` transcript_bytes t2)
    (ensures
      t1 == t2)
  = let t1' = transcript_set_retry t1 None in
    let t2' = transcript_set_retry t2 None in
    transcript_script_bytes t1;
    transcript_script_bytes t2;
    transcript_bytes_injective_retry (transcript_get_retry t1) t1' (transcript_get_retry t2) t2' ;
    transcript_bytes_injective_no_retry t1' t2'

noeq
type state (a:HashDef.hash_alg) = {
  region:Mem.rgn;
  loc: Ghost.erased B.loc;
  hash_state: CRF.state a
}

let invariant (#a:HashDef.hash_alg) (s:state a) (tx:transcript_t) (h:HS.mem) =
  CRF.hashed h s.hash_state `Seq.equal` transcript_bytes tx /\
  CRF.invariant h s.hash_state /\
  B.loc_region_only true s.region `B.loc_includes` Ghost.reveal s.loc /\
  Ghost.reveal s.loc == CRF.footprint h s.hash_state /\
  B.loc_not_unused_in h `B.loc_includes` Ghost.reveal s.loc

let footprint (#a:HashDef.hash_alg) (s:state a) = Ghost.reveal s.loc

let elim_invariant #a s t h = ()

let region_of #a s = s.region

let frame_invariant (#a:_) (s:state a) (t: transcript_t) (h0 h1:HS.mem) (l:B.loc) =
  CRF.frame_invariant l s.hash_state h0 h1

let create r a =
  let h0 = get() in
  let s = CRF.create_in a r in
  let h1 = get () in
  {region=r;
   loc=Ghost.hide (CRF.footprint h1 s);
   hash_state=s},
  Start None

let reset #a s tx =
  CRF.init (Ghost.hide a) s.hash_state;
  Start None

unfold
let extend_t (cond:label_repr -> bool) =
   (#a:_) ->
   (s:state a) ->
   (l:label_repr{cond l}) ->
   (tx:transcript_t) ->
   Stack transcript_t
    (requires fun h ->
        invariant s tx h /\
        valid_label_repr l h /\
        B.loc_disjoint (loc_of_label_repr l) (footprint s) /\
        extensible tx /\
        Some? (transition tx (label_of_label_repr l)))
    (ensures fun h0 tx' h1 ->
        invariant s tx' h1 /\
        B.modifies (footprint s) h0 h1 /\
        tx' == Some?.v (transition tx (label_of_label_repr l)))

let extend_ch : extend_t LR_ClientHello? =
  fun #a s l tx ->
  assert_norm (pow2 32 < pow2 61);
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_ClientHello ch ->
    //NS: 09/16 This assume is to justify the `to_buffer` cast a few lines below
    //That case is needed because CRF.update expects a buffer, not a const buffer
    //Once we have support for const buffers in KreMLin and in HACL*, we will
    //be able to remove this assume and the to_buffer cast
    //The same pattern appears in each case below.
    let ch_ptr = R.as_ptr ch in
    let len = R.Pos?.length ch in
    let data = R.Ptr?.b ch_ptr in

    assume (C.qbuf_qual (C.as_qbuf data) == C.MUTABLE);

    // These three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the client hello that is being added
    R.reveal_valid();
    LP.valid_pos_valid_exact HSM.handshake_parser h0 (R.slice_of_const_buffer data len) 0ul len;
    LP.valid_exact_serialize HSM.handshake_serializer h0 (R.slice_of_const_buffer data len) 0ul len;

    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer data) len;

    let tx' = Some?.v (transition tx (label_of_label_repr l)) in

    tx'

let extend_sh : extend_t LR_ServerHello? =
  fun #a s l tx ->
  assert_norm (pow2 32 < pow2 61);
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_ServerHello sh ->
    let sh_ptr = R.as_ptr sh in
    let len = R.Pos?.length sh in
    let data = R.Ptr?.b sh_ptr in

    assume (C.qbuf_qual (C.as_qbuf data) == C.MUTABLE);

    // These three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the server hello that is being added
    R.reveal_valid();
    LP.valid_pos_valid_exact HSM.handshake_parser h0 (R.slice_of_const_buffer data len) 0ul len;
    LP.valid_exact_serialize HSM.handshake_serializer h0 (R.slice_of_const_buffer data len) 0ul len;

    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer data) len;
    let h1 = HyperStack.ST.get() in

    let tx' = Some?.v (transition tx (label_of_label_repr l)) in

    LPSL.serialize_list_nil HSM.handshake12_parser HSM.handshake12_serializer;
    LPSL.serialize_list_nil HSM.handshake13_parser HSM.handshake13_serializer;
    assert ((transcript_bytes tx `Seq.append`
             serialize_server_hello (HSM.M_server_hello?._0 (R.value sh_ptr)))
        `Seq.equal`
             transcript_bytes tx');

    tx'

let extend_tch : extend_t LR_TCH? =
  fun #a s l tx ->
  assert_norm (pow2 32 < pow2 61);
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_TCH #b tch   ->
    R.reveal_valid();
    let tch_ptr = R.as_ptr tch in
    let data = R.Ptr?.b tch_ptr in
    let len = R.Pos?.length tch in
    assume (C.qbuf_qual (C.as_qbuf data) == C.MUTABLE);

    let slice = R.slice_of_const_buffer data len in
    assert (LP.valid HSM.handshake_parser h0 slice 0ul);
    let len = PB.binders_pos slice 0ul in
    let data = C.sub data 0ul len in

    PB.valid_truncate_clientHello h0 slice 0ul;
    assert (C.as_seq h0 data == FStar.Bytes.reveal (PB.truncate_clientHello_bytes (R.value_pos tch)));

    let h1 = HyperStack.ST.get () in
    CRF.frame_invariant B.loc_none s.hash_state h0 h1;
    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer data) len;

    let tx' = Some?.v (transition tx (label_of_label_repr l)) in

    PB.truncate_clientHello_bytes_set_binders
       (R.value tch_ptr)
       (PB.build_canonical_binders (ch_binders_len (HSM.M_client_hello?._0 (R.value tch_ptr))));

    tx'

#push-options "--z3rlimit_factor 2"
let extend_complete_tch : extend_t LR_CompleteTCH? =
  fun #a s l tx ->
  assert_norm (pow2 32 < pow2 61);
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_CompleteTCH #b tch ->
    R.reveal_valid();
    let tch_ptr = R.as_ptr tch in
    let data = R.Ptr?.b tch_ptr in
    let len = R.Pos?.length tch in
    assume (C.qbuf_qual (C.as_qbuf data) == C.MUTABLE);
    let slice = R.slice_of_const_buffer data len in

    R.reveal_valid();
    // Needed to detect that the whole b.R.base between start and pos is actually serialize tch
    LP.valid_pos_valid_exact HSM.handshake_parser h0 slice 0ul len;
    LP.valid_exact_serialize HSM.handshake_serializer h0 slice 0ul len;

    assert (LP.valid HSM.handshake_parser h0 slice 0ul);

    let start_pos = PB.binders_pos slice 0ul in

    let len = len - start_pos in
    let data = C.sub data start_pos len in

    PB.valid_truncate_clientHello h0 slice 0ul;

    let h1 = HyperStack.ST.get () in
    CRF.frame_invariant B.loc_none s.hash_state h0 h1;
    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer data) len;

    let tx' = Some?.v (transition tx (label_of_label_repr l)) in

    PB.truncate_clientHello_bytes_set_binders
      (R.value tch_ptr)
      (PB.build_canonical_binders (ch_binders_len (HSM.M_client_hello?._0 (R.value tch_ptr))));

    assert ((transcript_bytes tx `Seq.append` (C.as_seq h0 data))
           `Seq.equal`
           transcript_bytes tx');

    tx'
#pop-options

let extend_hrr : extend_t LR_HRR? =
  fun #a s l tx ->
  assert_norm (pow2 32 < pow2 61);
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_HRR ch_tag hrr ->
    let ch_ptr = R.as_ptr ch_tag in
    let ch_data = R.Ptr?.b ch_ptr in
    let ch_len = R.Pos?.length ch_tag in
    let ch_slice = R.slice_of_const_buffer ch_data ch_len in

    let hrr_ptr = R.as_ptr hrr in
    let hrr_data = R.Ptr?.b hrr_ptr in
    let hrr_len = R.Pos?.length hrr in
    let hrr_slice = R.slice_of_const_buffer hrr_data hrr_len in

    assume (C.qbuf_qual (C.as_qbuf ch_data) == C.MUTABLE);
    assume (C.qbuf_qual (C.as_qbuf hrr_data) == C.MUTABLE);

    let tx' = Some?.v (transition tx (label_of_label_repr l)) in

    // these three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the client hello that is being added
    R.reveal_valid();

    LP.valid_pos_valid_exact HSM.handshake_parser h0 ch_slice 0ul ch_len;
    LP.valid_exact_serialize HSM.handshake_serializer h0 ch_slice 0ul ch_len;

    LP.valid_pos_valid_exact HSM.handshake_parser h0 hrr_slice 0ul hrr_len;
    LP.valid_exact_serialize HSM.handshake_serializer h0 hrr_slice 0ul hrr_len;

    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer ch_data) ch_len;

    assert ((Seq.empty `Seq.append`  LP.serialize HSM.handshake_serializer (R.value ch_ptr))
      `Seq.equal`
        LP.serialize HSM.handshake_serializer (R.value ch_ptr));

    let h1 = HyperStack.ST.get() in

    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer hrr_data) hrr_len;

    let hf = HyperStack.ST.get () in

    tx'

let extend_hsm12 : extend_t LR_HSM12? =
  fun #a s l tx ->
  assert_norm (pow2 32 < pow2 61);
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_HSM12 hs12 ->
    let hs12_ptr = R.as_ptr hs12 in
    let hs12_data = R.Ptr?.b hs12_ptr in
    let hs12_len = R.Pos?.length hs12 in
    let hs12_slice = R.slice_of_const_buffer hs12_data hs12_len in

    assume (C.qbuf_qual (C.as_qbuf hs12_data) == C.MUTABLE);

    // These three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the client hello that is being added
    R.reveal_valid();
    LP.valid_pos_valid_exact HSM.handshake12_parser h0 hs12_slice 0ul hs12_len;
    LP.valid_exact_serialize HSM.handshake12_serializer h0 hs12_slice 0ul hs12_len;

    // let len = hs12.R.end_pos - hs12.R.start_pos in
    // let data = C.sub b.R.base hs12.R.start_pos len in
    let tx' = Some?.v (transition tx (label_of_label_repr l)) in

    LPSL.serialize_list_singleton HSM.handshake12_parser HSM.handshake12_serializer
      (R.value hs12_ptr);
    LPSL.serialize_list_append HSM.handshake12_parser HSM.handshake12_serializer
      (Transcript12?.rest tx)
      [R.value hs12_ptr];
    assert ((transcript_bytes tx `Seq.append`
             LP.serialize HSM.handshake12_serializer (R.value hs12_ptr))
        `Seq.equal`
             transcript_bytes tx');

    assert_norm ((max_transcript_size + 4) * max_message_size < pow2 61);

    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer hs12_data) hs12_len;

    tx'

let extend_hsm13 : extend_t LR_HSM13? =
  fun #a s l tx ->
  assert_norm (pow2 32 < pow2 61);
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_HSM13 hs13 ->
    let hs13_ptr = R.as_ptr hs13 in
    let hs13_data = R.Ptr?.b hs13_ptr in
    let hs13_len = R.Pos?.length hs13 in
    let hs13_slice = R.slice_of_const_buffer hs13_data hs13_len in

    assume (C.qbuf_qual (C.as_qbuf hs13_data) == C.MUTABLE);

    // These three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the client hello that is being added
    R.reveal_valid();
    LP.valid_pos_valid_exact HSM.handshake13_parser h0 hs13_slice 0ul hs13_len;
    LP.valid_exact_serialize HSM.handshake13_serializer h0 hs13_slice 0ul hs13_len;

    // let len = hs13.R.end_pos - hs13.R.start_pos in
    // let data = C.sub b.R.base hs13.R.start_pos len in

    let tx' = Some?.v (transition tx (label_of_label_repr l)) in

    LPSL.serialize_list_singleton HSM.handshake13_parser HSM.handshake13_serializer
      (R.value hs13_ptr);
    LPSL.serialize_list_append HSM.handshake13_parser HSM.handshake13_serializer
      (Transcript13?.rest tx)
      [R.value hs13_ptr];
    assert ((transcript_bytes tx `Seq.append`
             LP.serialize HSM.handshake13_serializer (R.value hs13_ptr))
        `Seq.equal`
             transcript_bytes tx');


    assert_norm ((max_transcript_size + 4) * max_message_size < pow2 61);

    CRF.update (Ghost.hide a) s.hash_state (C.to_buffer hs13_data) hs13_len;

    tx'

let extend (#a:_) (s:state a) (l:label_repr) (tx:transcript_t) =
  match l with
  | LR_ClientHello _ ->
    extend_ch s l tx
  | LR_ServerHello _ ->
    extend_sh s l tx
  | LR_TCH _ ->
    extend_tch s l tx
  | LR_CompleteTCH _ ->
    extend_complete_tch s l tx
  | LR_HRR _ _ ->
    extend_hrr s l tx
  | LR_HSM12 _ ->
    extend_hsm12 s l tx
  | LR_HSM13 _ ->
    extend_hsm13 s l tx

let transcript_hash (a:HashDef.hash_alg) (t:transcript_t)
  = Spec.Agile.Hash.hash a (transcript_bytes t)

let hashed (a:HashDef.hash_alg) (t:transcript_t) =
  Model.CRF.hashed a (transcript_bytes t)

let extract_hash (#a:_) (s:state a)
  (tag:Hacl.Hash.Definitions.hash_t a)
  (tx:transcript_t)
  =
    let h0 = HyperStack.ST.get() in
    CRF.finish (Ghost.hide a) s.hash_state tag;
    let h1 = HyperStack.ST.get() in
    B.(modifies_liveness_insensitive_buffer
      (footprint s `loc_union` (loc_region_only true Mem.tls_tables_region))
      (B.loc_buffer tag) h0 h1 tag)

let injectivity a t0 t1 =
  let b0 = Ghost.hide (transcript_bytes t0) in
  let b1 = Ghost.hide (transcript_bytes t1) in
  Model.CRF.injective a b0 b1;
  let aux () : Lemma
    (requires CRF.model /\ Model.CRF.crf a /\ b0 == b1)
    (ensures t0 == t1) =
    transcript_bytes_injective t0 t1
  in Classical.move_requires aux ()
