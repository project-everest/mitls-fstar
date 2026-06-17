module TLS13.Impl.Parser.DecoderWF

(**
  Pure builder lemmas that construct [TLS13.Impl.Client.Types.network_input_wf]
  (and the [decoder_fragment_relation] / [protected_decoder_fragment_relation]
  facts it requires) from the record-parse, record-open and inner-plaintext
  facts that the record decoders in [TLS13.Impl.Parser] hold in hand.

  These are kept separate from the (very large) Client.Types module so the
  decoder proofs can iterate quickly, mirroring the existing
  [TLS13.Impl.Parser.*] helper modules.
*)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module ID = FStar.IndefiniteDescription
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RV = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

#set-options "--fuel 1 --ifuel 2 --z3rlimit 30"

(* The content-type byte determines the decoded content type. *)
let lemma_content_type_matches_injective (wire:U8.t) (c1 c2:T.content_type)
  : Lemma
    (requires L.content_type_matches wire c1 /\ L.content_type_matches wire c2)
    (ensures c1 == c2)
= ()

(* parse_tls_message is deterministic and content_type_matches is injective in
   the byte, so wire_parse_success pins a unique message. *)
let lemma_wire_parse_unique
  (content_type:U8.t) (fragment:B.bytes) (m1 m2:M.tls_message)
  : Lemma
    (requires
      CT.wire_parse_success content_type fragment m1 /\
      CT.wire_parse_success content_type fragment m2)
    (ensures m1 == m2)
=
  assert (exists ct1.
    L.content_type_matches content_type ct1 /\
    WS.parse_tls_message ct1 fragment == Some m1);
  assert (exists ct2.
    L.content_type_matches content_type ct2 /\
    WS.parse_tls_message ct2 fragment == Some m2);
  let ct1 =
    ID.indefinite_description_ghost T.content_type
      (fun ct -> L.content_type_matches content_type ct /\
              WS.parse_tls_message ct fragment == Some m1) in
  let ct2 =
    ID.indefinite_description_ghost T.content_type
      (fun ct -> L.content_type_matches content_type ct /\
              WS.parse_tls_message ct fragment == Some m2) in
  lemma_content_type_matches_injective content_type ct1 ct2

(* The L-side classification of a received message agrees with the model's
   notion of "cleartext when received". *)
let l_is_received_cleartext (l:L.tls_message) : bool =
  match l with
  | L.LTlsHandshake (L.LServerHello _) -> true
  | L.LTlsHandshake L.LHelloRetryRequest -> true
  | L.LTlsChangeCipherSpec -> true
  | _ -> false

// This lemma states that when a message is locally identified as cleartext received,
// the spec also considers it cleartext when received
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let lemma_l_received_cleartext_matches
  (content_type:U8.t) (fragment:B.bytes) (l:L.tls_message) (m:M.tls_message)
  : Lemma
    (requires 
      CT.parsed_message_wire_success_for content_type fragment l m /\
      l_is_received_cleartext l)
    (ensures CS.network_message_is_cleartext CL.Received m)
=
  // From l_is_received_cleartext l, we know l is one of:
  // - L.LTlsHandshake (L.LServerHello _)
  // - L.LTlsHandshake L.LHelloRetryRequest
  // - L.LTlsChangeCipherSpec
  
  // From parsed_message_wire_success_for, m matches l:
  // - M.TlsHandshake (M.ServerHello _)
  // - M.TlsHandshake M.HelloRetryRequest
  // - M.TlsChangeCipherSpec
  
  // All three are cleartext when received according to network_message_is_cleartext CL.Received
  ()
#pop-options

(* The outer record content type must agree with the message's own content type
   for the cleartext-raw relation to hold. *)
let cleartext_outer_ct_ok (outer_ct:T.content_type) (m:M.tls_message) : prop =
  match m with
  | M.TlsHandshake (M.ServerHello _) -> outer_ct == T.Handshake
  | M.TlsHandshake M.HelloRetryRequest -> outer_ct == T.Handshake
  | M.TlsChangeCipherSpec -> outer_ct == T.ChangeCipherSpec
  | _ -> True

(* Runtime-decidable gate on the L-level message and the outer content-type
   byte that the decoder checks before accepting a cleartext record. *)
let cleartext_consistent (content_type:U8.t) (l:L.tls_message) : bool =
  match l with
  | L.LTlsHandshake (L.LServerHello _) -> U8.eq content_type 0x16uy
  | L.LTlsHandshake L.LHelloRetryRequest -> U8.eq content_type 0x16uy
  | L.LTlsChangeCipherSpec -> U8.eq content_type 0x14uy
  | _ -> false

let lemma_cleartext_consistent_implies
  (content_type:U8.t) (outer_ct:T.content_type)
  (fragment:B.bytes) (l:L.tls_message) (m:M.tls_message)
  : Lemma
    (requires
      CT.parsed_message_wire_success_for content_type fragment l m /\
      L.content_type_matches content_type outer_ct /\
      cleartext_consistent content_type l)
    (ensures l_is_received_cleartext l /\ cleartext_outer_ct_ok outer_ct m)
= ()


(* From an exact outer-record parse and the wire-success round trip, recover the
   model's [cleartext_tls_message_raw] for a received cleartext message. *)
#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let lemma_cleartext_tls_message_raw_of_parse
  (content_type:U8.t) (outer_ct:T.content_type)
  (fragment:B.bytes) (raw:B.bytes)
  (l:L.tls_message) (m:M.tls_message)
  : Lemma
    (requires
      WS.parse_record raw == Some (outer_ct, fragment, B.length raw) /\
      L.content_type_matches content_type outer_ct /\
      CT.parsed_message_wire_success_for content_type fragment l m /\
      CS.network_message_is_cleartext CL.Received m /\
      cleartext_outer_ct_ok outer_ct m)
    (ensures CS.cleartext_tls_message_raw m raw)
=
  // From parse_record we get serialize_record outer_ct fragment == raw
  WS.lemma_parse_record_serializes raw;
  Seq.lemma_eq_elim (WS.serialize_record outer_ct fragment) raw;
  
  // Prove by cases on the cleartext message type
  (match m with
   | M.TlsHandshake (M.ServerHello sh) ->
     RV.lemma_serialize_tls_message_handshake (M.ServerHello sh);
     Seq.lemma_eq_elim fragment (WS.serialize_handshake (M.ServerHello sh))
   | M.TlsHandshake M.HelloRetryRequest ->
     CSL.lemma_parse_record_full_raw_records_exactly raw outer_ct fragment
   | M.TlsChangeCipherSpec ->
     assert (exists ct.
       L.content_type_matches content_type ct /\
       WS.parse_tls_message ct fragment == Some M.TlsChangeCipherSpec);
     let ct =
       ID.indefinite_description_ghost T.content_type
         (fun ct -> L.content_type_matches content_type ct /\
                 WS.parse_tls_message ct fragment == Some M.TlsChangeCipherSpec) in
     lemma_content_type_matches_injective content_type ct outer_ct;
     RV.lemma_serialize_tls_message_change_cipher_spec ();
     RV.lemma_parse_tls_message_change_cipher_spec fragment
   | _ -> ())
#pop-options
(* decoder_fragment_relation, cleartext (non-ApplicationData outer) branch. *)
let lemma_mk_cleartext_decoder_fragment_relation
  (st0:CS.connection_state) (content_type:U8.t) (outer_ct:T.content_type)
  (fragment:B.bytes) (raw:B.bytes)
  : Lemma
    (requires
      WS.parse_record raw == Some (outer_ct, fragment, B.length raw) /\
      ~(outer_ct == T.ApplicationData) /\
      L.content_type_matches content_type outer_ct)
    (ensures CT.decoder_fragment_relation st0 content_type fragment raw)
=
  WS.lemma_parse_record_implies_parse_record_wire raw

(* network_input_wf for a successfully-parsed received cleartext message. *)
let lemma_mk_cleartext_network_input_wf
  (st0:CS.connection_state) (content_type:U8.t) (outer_ct:T.content_type)
  (fragment:B.bytes) (raw:B.bytes)
  (l:L.tls_message) (m:M.tls_message)
  : Lemma
    (requires
      WS.parse_record raw == Some (outer_ct, fragment, B.length raw) /\
      ~(outer_ct == T.ApplicationData) /\
      L.content_type_matches content_type outer_ct /\
      CT.parsed_message_wire_success_for content_type fragment l m /\
      l_is_received_cleartext l /\
      cleartext_outer_ct_ok outer_ct m)
    (ensures CT.network_input_wf st0 content_type fragment raw)
=
  lemma_mk_cleartext_decoder_fragment_relation st0 content_type outer_ct fragment raw;
  introduce forall msg.
    CT.wire_parse_success content_type fragment msg ==>
    CT.received_tls_raw_delta_legal st0 msg raw
  with introduce _ ==> _
  with _hyp. (
    lemma_wire_parse_unique content_type fragment msg m;
    lemma_l_received_cleartext_matches content_type fragment l m;
    lemma_cleartext_tls_message_raw_of_parse content_type outer_ct fragment raw l m
  )

(* As above, but the caller supplies the runtime-decidable [cleartext_consistent]
   gate instead of the ghost message-shape facts. *)
let lemma_mk_cleartext_network_input_wf_consistent
  (st0:CS.connection_state) (content_type:U8.t) (outer_ct:T.content_type)
  (fragment:B.bytes) (raw:B.bytes)
  (l:L.tls_message) (m:M.tls_message)
  : Lemma
    (requires
      WS.parse_record raw == Some (outer_ct, fragment, B.length raw) /\
      ~(outer_ct == T.ApplicationData) /\
      L.content_type_matches content_type outer_ct /\
      CT.parsed_message_wire_success_for content_type fragment l m /\
      cleartext_consistent content_type l)
    (ensures CT.network_input_wf st0 content_type fragment raw)
=
  lemma_cleartext_consistent_implies content_type outer_ct fragment l m;
  lemma_mk_cleartext_network_input_wf st0 content_type outer_ct fragment raw l m

(* network_input_wf for a cleartext record whose fragment fails to parse. *)
let lemma_mk_cleartext_network_input_wf_none
  (st0:CS.connection_state) (content_type:U8.t) (outer_ct:T.content_type)
  (fragment:B.bytes) (raw:B.bytes)
  : Lemma
    (requires
      WS.parse_record raw == Some (outer_ct, fragment, B.length raw) /\
      ~(outer_ct == T.ApplicationData) /\
      L.content_type_matches content_type outer_ct /\
      CT.wire_parse_failure content_type fragment)
    (ensures CT.network_input_wf st0 content_type fragment raw)
=
  lemma_mk_cleartext_decoder_fragment_relation st0 content_type outer_ct fragment raw;
  introduce forall msg.
    CT.wire_parse_success content_type fragment msg ==>
    CT.received_tls_raw_delta_legal st0 msg raw
  with introduce _ ==> _
  with _hyp. (
    assert (exists ct.
      L.content_type_matches content_type ct /\
      WS.parse_tls_message ct fragment == Some msg);
    let ct =
      ID.indefinite_description_ghost T.content_type
        (fun ct -> L.content_type_matches content_type ct /\
                WS.parse_tls_message ct fragment == Some msg) in
    assert (WS.parse_tls_message ct fragment == None)
  )

(* Construct protected_decoder_fragment_relation from the open-record and inner
   plaintext facts the decoder establishes after decryption. *)
let lemma_mk_protected_decoder_fragment_relation
  (st0:CS.connection_state) (content_type:U8.t) (fragment:B.bytes) (raw:B.bytes)
  (outer_fragment:B.bytes) (opened:B.bytes) (plaintext:M.plaintext)
  : Lemma
    (requires
      WS.parse_record raw == Some (T.ApplicationData, outer_fragment, B.length raw) /\
      (exists read_state'.
        R.open_record
          st0.CS.cs_model.CS.model_record.CS.record_read
          (CT.record_header_aad raw)
          outer_fragment == Some (opened, read_state')) /\
      WS.parse_plaintext opened == Some plaintext /\
      L.content_type_matches content_type plaintext.M.content_type /\
      Seq.equal fragment plaintext.M.fragment)
    (ensures CT.protected_decoder_fragment_relation st0 content_type fragment raw)
=
  WS.lemma_parse_record_implies_parse_record_wire raw

(* network_input_wf for a successfully-parsed received protected message. *)
let lemma_mk_protected_network_input_wf
  (st0:CS.connection_state) (content_type:U8.t) (fragment:B.bytes) (raw:B.bytes)
  (outer_fragment:B.bytes) (l:L.tls_message) (m:M.tls_message)
  : Lemma
    (requires
      WS.parse_record raw == Some (T.ApplicationData, outer_fragment, B.length raw) /\
      CT.protected_decoder_fragment_relation st0 content_type fragment raw /\
      CT.parsed_message_wire_success_for content_type fragment l m /\
      ~(l_is_received_cleartext l))
    (ensures CT.network_input_wf st0 content_type fragment raw)
=
  assert (CT.decoder_fragment_relation st0 content_type fragment raw);
  introduce forall msg.
    CT.wire_parse_success content_type fragment msg ==>
    CT.received_tls_raw_delta_legal st0 msg raw
  with introduce _ ==> _
  with _hyp. (
    lemma_wire_parse_unique content_type fragment msg m;
    lemma_l_received_cleartext_matches content_type fragment l m;
    CSL.lemma_parse_record_full_raw_records_exactly raw T.ApplicationData outer_fragment
  )

(* network_input_wf for a protected record whose inner plaintext fails to parse. *)
let lemma_mk_protected_network_input_wf_none
  (st0:CS.connection_state) (content_type:U8.t) (fragment:B.bytes) (raw:B.bytes)
  : Lemma
    (requires
      CT.protected_decoder_fragment_relation st0 content_type fragment raw /\
      CT.wire_parse_failure content_type fragment)
    (ensures CT.network_input_wf st0 content_type fragment raw)
=
  assert (CT.decoder_fragment_relation st0 content_type fragment raw);
  introduce forall msg.
    CT.wire_parse_success content_type fragment msg ==>
    CT.received_tls_raw_delta_legal st0 msg raw
  with introduce _ ==> _
  with _hyp. (
    assert (exists ct.
      L.content_type_matches content_type ct /\
      WS.parse_tls_message ct fragment == Some msg);
    let ct =
      ID.indefinite_description_ghost T.content_type
        (fun ct -> L.content_type_matches content_type ct /\
                WS.parse_tls_message ct fragment == Some msg) in
    assert (WS.parse_tls_message ct fragment == None)
  )

(* For [decode_network_buffer]: establish [WS.parse_record] on the consumed
   record prefix [prefix == Seq.slice raw 0 (5 + flen)] from the header bytes
   validated on the full input buffer [raw].  The five header indices of the
   prefix coincide with those of [raw] (it is a length-(5+flen) prefix), so the
   header lemma applies and the prefix is consumed exactly. *)
let lemma_parse_record_buffer_prefix
  (raw:B.bytes) (prefix:B.bytes) (flen:nat)
  : Lemma
    (requires
      flen <= 16640 /\
      5 + flen <= B.length raw /\
      B.length prefix == 5 + flen /\
      prefix == Seq.slice raw 0 (5 + flen) /\
      (let b0 = U8.v (Seq.index raw 0) in
       b0 = 0x14 \/ b0 = 0x15 \/ b0 = 0x16 \/ b0 = 0x17) /\
      U8.v (Seq.index raw 1) = 0x03 /\
      U8.v (Seq.index raw 2) = 0x03 /\
      U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) == flen)
    (ensures
      (match WS.parse_record prefix with
       | None -> False
       | Some (ct, frag, consumed) ->
         consumed == 5 + flen /\
         Seq.equal frag (Seq.slice prefix 5 (5 + flen)) /\
         (U8.v (Seq.index raw 0) = 0x14 ==> ct == T.ChangeCipherSpec) /\
         (U8.v (Seq.index raw 0) = 0x15 ==> ct == T.Alert) /\
         (U8.v (Seq.index raw 0) = 0x16 ==> ct == T.Handshake) /\
         (U8.v (Seq.index raw 0) = 0x17 ==> ct == T.ApplicationData)))
=
  Seq.lemma_index_slice raw 0 (5 + flen) 0;
  Seq.lemma_index_slice raw 0 (5 + flen) 1;
  Seq.lemma_index_slice raw 0 (5 + flen) 2;
  Seq.lemma_index_slice raw 0 (5 + flen) 3;
  Seq.lemma_index_slice raw 0 (5 + flen) 4;
  RV.lemma_parse_record_from_header prefix
