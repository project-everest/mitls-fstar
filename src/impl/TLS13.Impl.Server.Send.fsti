module TLS13.Impl.Server.Send

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Sem = TLS13.Wire.Semantics
module W = TLS13.Wire.Spec
module GSH = TLS13.Wire.Generated.ServerHello
module GSHbody = TLS13.Wire.Generated.ServerHello_body
module GCS = TLS13.Wire.Generated.CipherSuite
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

(* Build-direction witness builders for generated wire records (defined in the
   implementation module).  They are total: their accessor postconditions are
   guarded by the input side-conditions that the wire format imposes (a
   ServerHello random must differ from the HelloRetryRequest sentinel; the
   certificate chain must be a non-empty bounded blob). *)
val mk_cert_witness (chain: B.bytes)
  : (c:GCert.certificate {
      (1 <= Seq.length chain /\ Seq.length chain <= 32768) ==>
      Sem.certificate_entries c == [ (chain <: Seq.seq U8.t) ] })

(* The canonical single-entry Certificate built by [mk_cert_witness] from a
   non-empty, bounded certificate chain serializes to exactly [13 + |chain|]
   bytes.  Discharges the serializer-length preconditions threaded through the
   server certificate send path. *)
val lemma_mk_cert_witness_bytesize (chain: B.bytes)
  : Lemma
    (requires 1 <= B.length chain /\
              B.length chain <= Bounds.max_server_certificate_chain_len)
    (ensures
      B.length (W.serialize_handshake (M.Certificate (mk_cert_witness chain))) ==
        13 + B.length chain)

(* The wire serialization of a CertificateVerify handshake message is exactly
   [8 + |signature|] bytes.  Discharges the serializer-length preconditions of
   the server CertificateVerify send path. *)
val lemma_serialize_handshake_certificate_verify_len (cv: GCV.certificateVerify)
  : Lemma
    (ensures
      B.length (W.serialize_handshake (M.CertificateVerify cv)) ==
        8 + B.length (Sem.certificateVerify_signature_bytes cv))

(* A TLS 1.3 Finished handshake message carrying a 32-byte verify_data
   serializes to exactly 36 bytes.  Discharges the serializer-length
   preconditions of the client-Finished verification path. *)
val lemma_serialize_handshake_finished_len (fin: GFin.finished)
  : Lemma
    (ensures B.length (W.serialize_handshake (M.Finished fin)) == 36)

val mk_server_hello_witness
  (random: B.bytes)
  (key_share: B.bytes)
  (session_id: B.bytes)
  (cs: GCS.cipherSuite)
  : (sh:GSH.serverHello {
      (Seq.length random == 32 /\
       (Seq.length random == 32 ==> (random <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
       Seq.length session_id == 32 /\
       Seq.length key_share == 32) ==>
      ((match Sem.serverHello_random sh with Some r -> Seq.equal r random | None -> False) /\
       Sem.serverHello_cipher_suite sh == Some cs /\
       Seq.equal (Sem.serverHello_session_id_echo_32 sh) session_id /\
       (match Sem.serverHello_key_share_x25519 sh with
        | Some k -> Seq.equal k key_share
        | None -> False)) })

(* The canonical ServerHello (key_share + supported_versions extensions) built by
   [mk_server_hello_witness] serializes to exactly 122 bytes; discharges the
   [|serialize_handshake (M.ServerHello sh)| == 122] send-path preconditions. *)
val lemma_mk_server_hello_witness_bytesize
  (random: B.bytes)
  (key_share: B.bytes)
  (session_id: B.bytes)
  (cs: GCS.cipherSuite)
  : Lemma
    (requires Seq.length random == 32 /\
              (random <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst /\
              Seq.length session_id == 32 /\
              Seq.length key_share == 32)
    (ensures
      B.length (W.serialize_handshake
        (M.ServerHello (mk_server_hello_witness random key_share session_id cs))) == 122)

(* Build-direction bridge (server ServerHello): the Model-level canonical
   builder [CM.server_hello_of_selection] coincides with the send-path witness
   [mk_server_hello_witness] applied to the same random / key_share /
   cipher_suite -- both reduce to the identical generated record. *)
val lemma_server_hello_of_selection_eq_witness
  (sel: CS.server_handshake_selection)
  : Lemma
    (ensures
      CM.server_hello_of_selection sel ==
      mk_server_hello_witness
        (CM.sho_random sel)
        sel.CS.server_key_share_public
        (CM.sho_session_id sel)
        (CM.sho_cipher_suite sel))

(* Build-direction bridge for CanonicalProtocol's symbolic LocalSendServerHello
   arm.  [ST.server_local_event_input_ready]/LocalSendServerHello carries the
   Model send obligation on the canonical ServerHello built from the state's
   selection [CM.server_hello_of_selection selection]; the credentialed send
   path requires the obligation on the witness form
   [mk_server_hello_witness (payload[0:32]) (x25519 (payload[32:64])) CHACHA]
   plus the HRR-sentinel guard on the payload random.  Under the input_ready
   facts (the state selection is [selection], its random and key-share match the
   payload slices, and key-share consistency) the two builders coincide, so
   [can_send_server_hello] transfers by congruence and the matches-clause forces
   the random off the HRR sentinel. *)
val lemma_can_send_server_hello_witness_of_selection
  (st: CS.connection_state)
  (selection: CS.server_handshake_selection)
  (server_random: B.bytes)
  (server_private_key: B.bytes)
  : Lemma
    (requires
      Seq.length server_random == 32 /\
      Seq.length server_private_key == 32 /\
      st.CS.cs_model.CS.model_handshake.CS.hs_server_selection == Some selection /\
      Seq.equal (selection.CS.server_random <: Seq.seq U8.t)
                (server_random <: Seq.seq U8.t) /\
      Some? selection.CS.server_key_share_private /\
      Seq.equal (Some?.v selection.CS.server_key_share_private <: Seq.seq U8.t)
                (server_private_key <: Seq.seq U8.t) /\
      CS.server_selection_key_share_consistent selection /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
      selection.CS.server_selected_cipher_suite == CM.server_selected_suite st /\
      CM.can_send_server_hello st (CM.server_hello_of_selection selection)
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ServerHello (CM.server_hello_of_selection selection)))))
    (ensures
      ((server_random <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
      (let sh = mk_server_hello_witness server_random
                  (CryptoSpec.x25519_public_from_private server_private_key)
                  (CM.stored_client_hello_session_id st)
                  (CM.server_selected_suite st) in
       CM.can_send_server_hello st sh
         (CS.serialized_cleartext_tls_message
           (M.TlsHandshake (M.ServerHello sh)))))

(* Build-direction bridge for the server Endpoint's deferred
   LocalSendServerHello handler.  Given the raw state/material matching facts
   (the state selection's random and private key equal the payload slices, the
   public key is x25519 of the private slice, the random is off the HRR sentinel
   and the cipher suite is CHACHA), the canonical [CM.server_hello_of_selection
   selection] can be sent, so plain [ST.server_local_event_input_ready]/
   LocalSendServerHello holds.  Mirrors the inline reasoning in
   [TLS13.Impl.Server.Driver.BufferedHandshake] (valid_selection +
   [CM.lemma_server_hello_of_selection_matches] +
   [CM.lemma_server_hello_of_selection_bytesize]); factored into a lemma so the
   heavy [can_send_server_hello] derivation stays out of the large deferred-action
   Pulse function (whose whole-function query is otherwise destabilised). *)
val lemma_input_ready_server_hello_of_selection
  (st: CS.connection_state)
  (selection: CS.server_handshake_selection)
  (material: B.bytes)
  : Lemma
    (requires
      B.length material == 64 /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
      st.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
      st.CS.cs_model.CS.model_handshake.CS.hs_server_selection == Some selection /\
      B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        122 <= Bounds.max_transcript_len /\
      Seq.equal (selection.CS.server_random <: Seq.seq U8.t)
                (CL.raw_slice material 0 32 <: Seq.seq U8.t) /\
      ((CL.raw_slice material 0 32 <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
      Some? selection.CS.server_key_share_private /\
      Seq.equal (Some?.v selection.CS.server_key_share_private <: Seq.seq U8.t)
                (CL.raw_slice material 32 64 <: Seq.seq U8.t) /\
      (selection.CS.server_key_share_public <: B.bytes) ==
        CryptoSpec.x25519_public_from_private (CL.raw_slice material 32 64) /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
      selection.CS.server_selected_cipher_suite == CM.server_selected_suite st)
    (ensures
      ST.server_local_event_input_ready st ST.LocalSendServerHello material)

(* Aggregate discharge of the four conditional obligations threaded through
   [S.process_local_event_with_credentials], for a symbolic [kind].  Proven
   from the plain and credentialed input_ready facts:
   VClF/CV bridge the transcript bounds via the finished / certificate-verify
   length lemmas; SendServerHello uses the SH build-direction bridge; and
   SendCertificate is vacuous because plain input_ready has no such case. *)
val lemma_server_process_local_obligations
  (st: CS.connection_state)
  (kind: ST.local_event_kind)
  (payload: B.bytes)
  (certificate_chain: B.bytes)
  (credential_identity: CS.server_credential_identity)
  (out_len_v: nat)
  : Lemma
    (requires
      ST.server_local_event_input_ready st kind payload /\
      ST.server_local_event_input_ready_with_credentials
        st kind payload certificate_chain credential_identity /\
      // Certificate-chain non-emptiness.  With the (un-weakened) plain
      // input_ready now carrying a reachable LocalSendCertificate case, this
      // branch is no longer vacuous; 1 <= |chain| is not a state invariant (no
      // config guarantees a non-empty chain) so it is established by a runtime
      // check at the send site and threaded in here (mirroring the analogous
      // Server.Driver.Local.check_certificate_chain_nonempty pattern).
      (kind == ST.LocalSendCertificate ==> 1 <= B.length certificate_chain))
    (ensures
      (kind == ST.LocalVerifyClientFinished /\
       Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
       B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
         Bounds.max_transcript_len /\
       CM.can_verify_client_finished st
         (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished)) /\
      (kind == ST.LocalSendServerHello /\ out_len_v == 127 ==>
       (Seq.length (CL.raw_slice payload 0 32) == 32 ==>
        (CL.raw_slice payload 0 32 <: Seq.lseq U8.t 32) <>
          GSHbody.serverHello_body_cst) /\
       (let sh = mk_server_hello_witness
                   (CL.raw_slice payload 0 32)
                   (CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64))
                   (CM.stored_client_hello_session_id st)
                   (CM.server_selected_suite st) in
        CM.can_send_server_hello st sh
          (CS.serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh))))) /\
      (kind == ST.LocalSendCertificateVerify /\
       Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
       B.length (W.serialize_handshake (M.CertificateVerify
         (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify))) ==
         8 + B.length (Sem.certificateVerify_signature_bytes
           (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)) /\
       B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
         B.length (W.serialize_handshake (M.CertificateVerify
           (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify))) <=
         Bounds.max_transcript_len) /\
      (kind == ST.LocalSendCertificate ==>
       1 <= B.length certificate_chain /\ B.length certificate_chain <= 32768 /\
       B.length (W.serialize_handshake
         (M.Certificate (mk_cert_witness certificate_chain))) ==
         13 + B.length certificate_chain))

(* Runtime accessor for the [j]-th byte of the HelloRetryRequest sentinel
   [GSHbody.serverHello_body_cst].  (The generated [serverHello_body_get_byte]
   is private to its implementation module, so we re-expose a copy here.) *)
inline_for_extraction
val hrr_sentinel_byte (j: SZ.t { SZ.v j < 32 })
  : (b: U8.t { b == Seq.index GSHbody.serverHello_body_cst (SZ.v j) })

(* Runtime 32-byte comparison of a freshly-generated server random against the
   HelloRetryRequest sentinel.  Returns [true] iff the first 32 bytes of
   [material] differ from the sentinel; this discharges the cst-guard that
   [mk_server_hello_witness] / [lemma_mk_server_hello_witness_bytesize] require.
   Security-critical: the iff postcondition must NOT be weakened. *)
fn server_random_differs_from_cst (material: array U8.t) (#p: perm) (#mb: erased (b:B.bytes{B.length b >= 32}))
  requires pts_to material #p mb
  returns b: bool
  ensures pts_to material #p mb **
          pure (b <==> (CL.raw_slice mb 0 32 <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst)

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

fn process_send_server_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased GSH.serverHello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v raw_len <= SZ.v network_out_len /\
                 Seq.equal
                    (Seq.slice (Ghost.reveal 'old_network_out) 0 (SZ.v raw_len))
                    (Ghost.reveal 'raw_bytes) /\
                 Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh)) /\
                 SZ.v fragment_len <= Bounds.max_server_hello_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_send_server_hello 'st0 sh (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_server_hello_state
                    'st0
                    sh
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendServerHello
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_hello_serialized
  (s:server)
  (lsh:IM.server_hello)
  (#sh:erased GSH.serverHello)
  (#server_random_bytes: erased B.bytes)
  (#server_key_share_bytes: erased B.bytes)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 127 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Seq.length (Ghost.reveal server_random_bytes) == 32 /\
                 (Ghost.reveal server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst /\
                 Seq.length (Ghost.reveal server_key_share_bytes) == 32 /\
                 Ghost.reveal sh ==
                   mk_server_hello_witness
                     (Ghost.reveal server_random_bytes)
                     (Ghost.reveal server_key_share_bytes)
                     (CM.stored_client_hello_session_id 'st0)
                     (CM.server_selected_suite 'st0) /\
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                Seq.equal
                  network_out_bytes
                  (CS.serialized_cleartext_tls_message
                    (M.TlsHandshake (M.ServerHello sh))) /\
                st1 ==
                  CM.sent_server_hello_state
                    'st0
                    sh
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendServerHello
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_hello_from_arrays
  (s:server)
  (server_random:array U8.t)
  (server_key_share:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_key_share_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 127 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                 // sentinel (serverHello_body_cst); unprovable for a symbolic random,
                 // so threaded as an explicit caller obligation.
                 (Seq.length (Ghost.reveal 'server_random_bytes) == 32 ==>
                  (Ghost.reveal 'server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                 (let sh = mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh)))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_key_share_bytes) == 32 ==>
                 (let sh = mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
                  Seq.equal
                    network_out_bytes
                    (CS.serialized_cleartext_tls_message
                      (M.TlsHandshake (M.ServerHello sh))) /\
                  st1 ==
                    CM.sent_server_hello_state
                      'st0
                      sh
                      network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_server_hello_with_derived_public_from_private_array
  (s:server)
  (server_random:array U8.t)
  (server_private_key:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_private_key 'server_private_key_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_private_key_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 127 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                 // sentinel (serverHello_body_cst); unprovable for a symbolic random,
                 // so threaded as an explicit caller obligation.
                 (Seq.length (Ghost.reveal 'server_random_bytes) == 32 ==>
                  (Ghost.reveal 'server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                 (let sh = mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (CryptoSpec.x25519_public_from_private
                       (Ghost.reveal 'server_private_key_bytes)) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh)))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_private_key 'server_private_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_private_key_bytes) == 32 ==>
                 (let sh = mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (CryptoSpec.x25519_public_from_private
                        (Ghost.reveal 'server_private_key_bytes)) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
                  Seq.equal
                    network_out_bytes
                    (CS.serialized_cleartext_tls_message
                      (M.TlsHandshake (M.ServerHello sh))) /\
                  st1 ==
                    CM.sent_server_hello_state
                      'st0
                      sh
                      network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_encrypted_extensions_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 28 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerHelloSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
                   Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake
                         (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (let ee = ([] <: GEE.encryptedExtensions) in
                 st1 ==
                   CM.sent_encrypted_extensions_state
                     'st0
                     ee
                     network_out_bytes) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendEncryptedExtensions
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn build_certificate_from_credentials
  (creds:O.server_credentials)
  requires O.is_server_credentials creds 'certificate_chain 'credential_identity **
           // TODO-A1: chain length bound not exposed by O.is_server_credentials;
           // needed because mk_cert_witness's Sem.certificate_entries postcondition is conditional
           // on 1 <= |chain| <= 32768. The empty-chain case is excluded at the caller by
           // legal_event (certificate_msg_matches_server_config).
           pure (1 <= B.length (Ghost.reveal 'certificate_chain) /\
                 B.length (Ghost.reveal 'certificate_chain) <= 32768)
  returns result: option IM.certificate_msg
  ensures O.is_server_credentials creds 'certificate_chain 'credential_identity **
          (match result with
           | Some lcert ->
             IM.is_valid_certificate_msg
               lcert
               (mk_cert_witness (Ghost.reveal 'certificate_chain)) **
             pure (
               SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
                 B.length (Ghost.reveal 'certificate_chain) /\
               lcert.IM.certificate_msg_cert_count == 1sz)
           | None ->
             pure (
               B.length (Ghost.reveal 'certificate_chain) >
                 IM.max_certificate_chain_bytes))

fn process_send_certificate_serialized
  (s:server)
  (lcert:IM.certificate_msg)
  (#cert:erased GCert.certificate)
  (#chain:erased B.bytes)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_msg lcert cert **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 1 <= Seq.length (Ghost.reveal chain) /\
                 Seq.length (Ghost.reveal chain) <= 32768 /\
                 Ghost.reveal cert == mk_cert_witness (Ghost.reveal chain) /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_handshake (M.Certificate (Ghost.reveal cert))) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 lcert.IM.certificate_msg_cert_count == 1sz /\
                 (exists (certificate:B.bytes).
                   Sem.certificate_entries (Ghost.reveal cert) == [certificate]) /\
                 Sem.certificate_entries (Ghost.reveal cert) <> [] /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> CS.certificate_msg_matches_server_config cfg (Ghost.reveal cert)
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.Certificate (Ghost.reveal cert));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_state
                    'st0
                    (Ghost.reveal cert)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_certificate_from_credentials
  (s:server)
  (creds:O.server_credentials)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 Some?
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                  ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 13 + B.length (Ghost.reveal 'certificate_chain) + 17 <= 16640 /\
                 SZ.v network_out_len ==
                 13 + B.length (Ghost.reveal 'certificate_chain) + 22 /\
                 // TODO-A1: |serialize_handshake (Certificate cert)| == 13 + |chain| was provided
                 // by the now-deleted W.lemma_serialize_certificate_from_single_chain_len; threaded
                 // as a precondition (true wire length of a single-entry certificate with empty
                 // request-context and empty extensions).
                 B.length (TLS13.Wire.Spec.serialize_handshake
                  (M.Certificate (mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                  13 + B.length (Ghost.reveal 'certificate_chain) /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> cfg.CS.server_certificate_chain == Ghost.reveal 'certificate_chain
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  13 + B.length (Ghost.reveal 'certificate_chain) <=
                    Bounds.max_transcript_len /\
                 CS.legal_event
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value =
                      M.TlsHandshake
                        (M.Certificate (mk_cert_witness (Ghost.reveal 'certificate_chain)));
                  }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_state
                    'st0
                    (mk_cert_witness (Ghost.reveal 'certificate_chain))
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_certificate_verify_serialized
  (s:server)
  (lcv:IM.certificate_verify)
  (#cv:erased GCV.certificateVerify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_verify lcv cv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                  | Some stored_cv -> stored_cv == Ghost.reveal cv
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_verify_state
                    'st0
                    (Ghost.reveal cv)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_stored_certificate_verify_serialized
  (s:server)
  (#cv:erased GCV.certificateVerify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                  B.length 'old_app_out == SZ.v app_out_len /\
                  SZ.v fragment_len ==
                    B.length
                      (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                  SZ.v fragment_len + 17 <= 16640 /\
                  SZ.v network_out_len == SZ.v fragment_len + 22 /\
                  ST.server_end_to_end_invariant 'st0 /\
                  'st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                  'st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                  Some?
                    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits
                    ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    Some (Ghost.reveal cv) /\
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= Bounds.max_transcript_len /\
                  CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Sent;
                      CL.message_value =
                        M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                    }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_verify_state
                    'st0
                    (Ghost.reveal cv)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendCertificateVerify
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_finished_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 58 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   Bounds.max_transcript_len)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (match
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic
                 with
                 | Some server_hs ->
                   let fin = ((K.finished_verify_data
                         server_hs.CS.traffic_secret
                         (Tr.hash
                           'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)) <: GFin.finished) in
                   st1 ==
                     CM.sent_server_finished_state
                       'st0
                       fin
                       network_out_bytes
                 | None -> True) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerFinished
                  B.empty
                  network_out_bytes
                  app_out_bytes)
