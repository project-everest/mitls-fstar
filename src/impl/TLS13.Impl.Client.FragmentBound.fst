module TLS13.Impl.Client.FragmentBound

(* Auxiliary lemma supporting Decision 2 of the parser work: a well-formed
   network input (CT.network_input_wf) always yields a recovered dispatcher
   fragment whose length is bounded by the TLS 1.3 record-fragment size limit
   (L.max_record_fragment_len = 16640).  This lemma lives in its own module so
   that it does not perturb the SMT context of the very large
   TLS13.Impl.Client.Types module. *)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module R = TLS13.Record.Spec
module ID = FStar.IndefiniteDescription
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module RV = TLS13.Wire.Spec.Reveal
module CT = TLS13.Impl.Client.Types

(* open_record discards the AEAD-open length refinement at its option boundary;
   recover it (open_record is transparent so this is by computation). *)
let lemma_open_record_len
  (st:R.direction_state)
  (aad:B.bytes)
  (ct:M.sealed_record)
  : Lemma
      (requires Some? (R.open_record st aad ct))
      (ensures B.length (fst (Some?.v (R.open_record st aad ct))) + 16 == B.length ct)
=
  ()

let lemma_network_input_wf_fragment_bound
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires CT.network_input_wf st0 content_type fragment raw_received)
      (ensures B.length fragment <= L.max_record_fragment_len)
=
  assert (CT.decoder_fragment_relation st0 content_type fragment raw_received);
  WS.lemma_parse_record_fragment_bound raw_received;
  let outer_ct =
    ID.indefinite_description_ghost T.content_type
      (fun outer_ct -> exists outer_fragment.
        WS.parse_record raw_received == Some (outer_ct, outer_fragment, B.length raw_received) /\
        (if outer_ct == T.ApplicationData
         then CT.protected_decoder_fragment_relation st0 content_type fragment raw_received
         else L.content_type_matches content_type outer_ct /\ Seq.equal fragment outer_fragment)) in
  let outer_fragment =
    ID.indefinite_description_ghost M.sealed_record
      (fun outer_fragment ->
        WS.parse_record raw_received == Some (outer_ct, outer_fragment, B.length raw_received) /\
        (if outer_ct == T.ApplicationData
         then CT.protected_decoder_fragment_relation st0 content_type fragment raw_received
         else L.content_type_matches content_type outer_ct /\ Seq.equal fragment outer_fragment)) in
  if outer_ct = T.ApplicationData
  then begin
    assert (CT.protected_decoder_fragment_relation st0 content_type fragment raw_received);
    let pof =
      ID.indefinite_description_ghost B.bytes
        (fun pof ->
          WS.parse_record raw_received == Some (T.ApplicationData, pof, B.length raw_received) /\
          (exists opened. CT.protected_record_opened st0 raw_received pof opened /\
            (exists plaintext. WS.parse_plaintext opened == Some plaintext /\
              CT.decoder_fragment_matches_plaintext content_type fragment plaintext))) in
    let opened =
      ID.indefinite_description_ghost B.bytes
        (fun opened ->
          CT.protected_record_opened st0 raw_received pof opened /\
          (exists plaintext. WS.parse_plaintext opened == Some plaintext /\
            CT.decoder_fragment_matches_plaintext content_type fragment plaintext)) in
    let plaintext =
      ID.indefinite_description_ghost M.plaintext
        (fun plaintext ->
          WS.parse_plaintext opened == Some plaintext /\
          CT.decoder_fragment_matches_plaintext content_type fragment plaintext) in
    assert (CT.protected_record_opened st0 raw_received pof opened);
    let rs =
      ID.indefinite_description_ghost R.direction_state
        (fun rs ->
          R.open_record
            st0.CS.cs_model.CS.model_record.CS.record_read
            (CT.record_header_aad raw_received)
            pof == Some (opened, rs)) in
    assert (R.open_record
              st0.CS.cs_model.CS.model_record.CS.record_read
              (CT.record_header_aad raw_received)
              pof == Some (opened, rs));
    lemma_open_record_len
      st0.CS.cs_model.CS.model_record.CS.record_read
      (CT.record_header_aad raw_received)
      pof;
    assert (B.length opened + 16 == B.length pof);
    assert (B.length pof <= 16640);
    RV.lemma_parse_plaintext_fragment_len opened;
    assert (B.length plaintext.M.fragment + 1 == B.length opened);
    assert (CT.decoder_fragment_matches_plaintext content_type fragment plaintext);
    Seq.lemma_eq_elim fragment plaintext.M.fragment
  end
  else begin
    assert (L.content_type_matches content_type outer_ct /\ Seq.equal fragment outer_fragment);
    Seq.lemma_eq_elim fragment outer_fragment
  end
