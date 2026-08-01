module TLS13.Impl.Server.Send

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CR = TLS13.Impl.ConnectionState.Repr
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module Ser = TLS13.Impl.Serializer
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Tr = TLS13.Transcript
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module Ref = Pulse.Lib.Reference
module W = TLS13.Wire.Spec
module Rev = TLS13.Wire.Spec.Reveal.Handshake
module LP = LowParse.Spec.Base
module Sem = TLS13.Wire.Semantics
module GSH = TLS13.Wire.Generated.ServerHello
module GHS = TLS13.Wire.Generated.Handshake
module GSHbody = TLS13.Wire.Generated.ServerHello_body
module GSHB = TLS13.Wire.Generated.ServerHelloBody
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GKE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCS = TLS13.Wire.Generated.CipherSuite
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCertE = TLS13.Wire.Generated.CertificateEntry
module GCL = TLS13.Wire.Generated.Certificate_certificate_list
module GEX = TLS13.Wire.Generated.CertificateEntry_extensions
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module GSS = TLS13.Wire.Generated.SignatureScheme
module SerH = TLS13.Impl.Serializer.Handshake
module CQ = TLS13.Impl.ConnectionState.Queries

(* ----------------------------------------------------------------------- *)
(* Build-direction witness builders for generated wire records.            *)
(* The migration replaced the old flat M.* message records by the          *)
(* generated nested wire records; these helpers reconstruct a canonical    *)
(* wire witness whose TLS13.Wire.Semantics accessors expose exactly the    *)
(* fields the old flat records carried.                                     *)
(* ----------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let mk_cert_witness (chain: B.bytes)
  : (c:GCert.certificate {
      (1 <= Seq.length chain /\ Seq.length chain <= 32768) ==>
      Sem.certificate_entries c == [ (chain <: Seq.seq U8.t) ] })
=
  let safe : (x:Seq.seq U8.t{1 <= Seq.length x /\ Seq.length x <= 32768}) =
    if 1 <= Seq.length chain && Seq.length chain <= 32768 then chain else Seq.create 1 0uy in
  let cd : GCertE.certificateEntry_cert_data = safe in
  let ex : GCertE.certificateEntry_extensions = [] in
  let entry : GCertE.certificateEntry = { GCertE.cert_data = cd; GCertE.extensions = ex } in
  GEX.certificateEntry_extensions_list_bytesize_nil;
  GCL.certificate_certificate_list_list_bytesize_nil;
  assert (GCL.certificate_certificate_list_list_bytesize [entry] ==
          GCertE.certificateEntry_bytesize entry);
  let cl : GCert.certificate_certificate_list = [entry] in
  let rc : GCert.certificate_certificate_request_context = B.empty in
  let c : GCert.certificate = { GCert.certificate_request_context = rc; GCert.certificate_list = cl } in
  assert (Sem.certificate_entries c == Sem.cert_entries_data [entry]);
  c
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let mk_cert_witness_entries_unconditional (chain: B.bytes)
  : Lemma
    (ensures
      (1 <= Seq.length chain /\ Seq.length chain <= 32768 ==>
       Sem.certificate_entries (mk_cert_witness chain) == [ (chain <: Seq.seq U8.t) ]) /\
      (~(1 <= Seq.length chain /\ Seq.length chain <= 32768) ==>
       Sem.certificate_entries (mk_cert_witness chain) == [ (Seq.create 1 0uy <: Seq.seq U8.t) ]))
  = ()

let mk_cert_witness_chain_matches_lemma
  (storage: B.bytes) (storage_len: nat) (offsets: Seq.seq SZ.t) (lens: Seq.seq SZ.t) (chain: B.bytes)
  : Lemma
    (requires
      1 <= Seq.length chain /\ Seq.length chain <= 32768 /\
      IM.certificate_chain_matches storage storage_len offsets lens 1 [chain])
    (ensures
      IM.certificate_chain_matches storage storage_len offsets lens 1
        (Sem.certificate_entries (mk_cert_witness chain)))
  = mk_cert_witness_entries_unconditional chain
#pop-options

(* Bridging lemma: the abstract certificate witness [mk_cert_witness] coincides,
   under the non-empty/bounded chain guard, with the build-direction serializer's
   canonical pin [SerH.poc_canonical_cert].  Both build the identical generated
   record (empty request_context; single certificateEntry { cert_data = chain;
   extensions = [] }).  Lets callers discharge the serializer's
   [cert == SerH.poc_canonical_cert chain] precondition. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_mk_cert_witness_eq_poc (chain: B.bytes)
  : Lemma
    (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
    (ensures mk_cert_witness chain == SerH.poc_canonical_cert chain)
  = ()
#pop-options

(* The canonical single-entry Certificate produced by [mk_cert_witness] from a
   non-empty, bounded certificate chain serializes to exactly [13 + |chain|]
   bytes on the wire: handshake msg_type 1 + handshake length 3 +
   certificate_request_context length 1 + certificate_list length 3 +
   [ single entry: cert_data length 3 + |chain| + extensions length 2 ]
   = 13 + |chain|.  Discharges the serializer-length precondition of
   [process_send_certificate_exact_and_write_once]. *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 100"
let lemma_mk_cert_witness_bytesize (chain: B.bytes)
  : Lemma
    (requires 1 <= B.length chain /\
              B.length chain <= Bounds.max_server_certificate_chain_len)
    (ensures
      B.length (W.serialize_handshake (M.Certificate (mk_cert_witness chain))) ==
        13 + B.length chain)
  = assert_norm (Bounds.max_server_certificate_chain_len == 16610);
    let c = mk_cert_witness chain in
    GCL.certificate_certificate_list_list_bytesize_nil;
    GEX.certificateEntry_extensions_list_bytesize_nil;
    Rev.lemma_serialize_handshake_certificate c;
    GHS.handshake_bytesize_eq (GHS.Body_certificate (c <: GHS.handshake_body_certificate));
    ()
#pop-options

(* The wire serialization of a CertificateVerify handshake message is exactly
   [8 + |signature|] bytes: handshake msg_type 1 + handshake length 3 +
   signature_scheme 2 + signature length-prefix 2 + |signature|.  Discharges the
   serializer-length precondition of
   [process_send_certificate_verify_exact_and_write_once]. *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 100"
let lemma_serialize_handshake_certificate_verify_len (cv: GCV.certificateVerify)
  : Lemma
    (ensures
      B.length (W.serialize_handshake (M.CertificateVerify cv)) ==
        8 + B.length (Sem.certificateVerify_signature_bytes cv))
  = Rev.lemma_serialize_handshake_certificate_verify cv;
    GHS.handshake_bytesize_eq (GHS.Body_certificate_verify cv);
    GSS.signatureScheme_bytesize_eq cv.GCV.algorithm;
    ()
#pop-options

(* A TLS 1.3 Finished handshake message carrying a 32-byte verify_data
   serializes to exactly 36 bytes: handshake msg_type 1 + handshake length 3 +
   32 verify_data bytes.  Discharges the serializer-length precondition of the
   client-Finished verification path. *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 100"
let lemma_serialize_handshake_finished_len (fin: GFin.finished)
  : Lemma
    (ensures B.length (W.serialize_handshake (M.Finished fin)) == 36)
  = Rev.lemma_serialize_handshake_finished fin;
    GHS.handshake_bytesize_eq (GHS.Body_finished fin);
    ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let mk_server_hello_witness
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
=
  let safe_ks : (k:Seq.seq U8.t{Seq.length k == 32}) =
    if Seq.length key_share = 32 then key_share else Seq.create 32 0uy in
  let ke : GKE.keyShareEntry_key_exchange = safe_ks in
  let kse : GKE.keyShareEntry = { GKE.group = GNG.X25519; GKE.key_exchange = ke } in
  GNG.namedGroup_bytesize_eq GNG.X25519;
  GKE.keyShareEntry_key_exchange_bytesize_eqn ke;
  assert (GKE.keyShareEntry_key_exchange_bytesize ke == 34);
  let ksesh : GESH.extensionServerHello_extension_data_key_share = kse in
  let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share ksesh in
  // RFC 8446: a TLS 1.3 ServerHello MUST carry the supported_versions extension
  // selecting TLS 1.3 (the byte-level serializer wrote it too). Listed AFTER
  // key_share to match the original wire order.
  let sv_ext : GESH.extensionServerHello =
    GESH.Extension_data_supported_versions
      (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions) in
  GSHB.serverHelloBody_extensions_list_bytesize_nil;
  GSHB.serverHelloBody_extensions_list_bytesize_cons sv_ext [];
  GSHB.serverHelloBody_extensions_list_bytesize_cons ks_ext [sv_ext];
  GPV.protocolVersion_bytesize_eq GPV.TLS_1p3;
  assert (GSHB.serverHelloBody_extensions_list_bytesize [ks_ext; sv_ext] ==
          GESH.extensionServerHello_bytesize ks_ext +
          GESH.extensionServerHello_bytesize sv_ext);
  let exts : GSHB.serverHelloBody_extensions = [ks_ext; sv_ext] in
  (* RFC 8446 D.4 middlebox compatibility: echo the client's 32-byte
     legacy_session_id verbatim.  Clamped to keep this function total. *)
  let sid : GSHB.serverHelloBody_legacy_session_id_echo =
    if Seq.length session_id = 32 then session_id else Seq.create 32 0uy in
  let body : GSHB.serverHelloBody = {
    GSHB.legacy_session_id_echo = sid;
    GSHB.cipher_suite = cs;
    GSHB.legacy_compression_method = 0uy;
    GSHB.extensions = exts;
  } in
  if Seq.length random = 32 then begin
    let r32 : Seq.lseq U8.t 32 = random in
    if r32 <> GSHbody.serverHello_body_cst then begin
      let bf : GSHbody.serverHello_body_false = { GSHbody.tag = r32; GSHbody.value = body } in
      let sh : GSH.serverHello = {
        GSH.legacy_version = GPV.TLS_1p2;
        GSH.body = GSHbody.ServerHello_body_false bf;
      } in
      assert (Sem.serverHello_key_share_x25519 sh == Sem.sh_find_key_share [ks_ext; sv_ext]);
      sh
    end else
      { GSH.legacy_version = GPV.TLS_1p2; GSH.body = GSHbody.HelloRetryRequest body }
  end else
    { GSH.legacy_version = GPV.TLS_1p2; GSH.body = GSHbody.HelloRetryRequest body }
#pop-options

(* The canonical ServerHello produced by [mk_server_hello_witness] (key_share +
   supported_versions extensions) serializes to exactly 122 bytes on the wire.
   This discharges the [|serialize_handshake (M.ServerHello sh)| == 122]
   preconditions threaded through the server send path. *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let lemma_mk_server_hello_witness_bytesize
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
  = let sh = mk_server_hello_witness random key_share session_id cs in
    Rev.lemma_serialize_handshake_server_hello sh;
    GHS.handshake_bytesize_eq (GHS.Body_server_hello sh);
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p2;
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p3;
    GCS.cipherSuite_bytesize_eq cs;
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKE.keyShareEntry_key_exchange_bytesize_eqn (key_share <: GKE.keyShareEntry_key_exchange);
    GSHB.serverHelloBody_extensions_list_bytesize_nil;
    ()
#pop-options

(* Bridging lemma: the abstract canonical witness [mk_server_hello_witness]
   built by the server send path coincides, under the (runtime-checked) HRR
   sentinel guard, with the build-direction serializer's canonical pin
   [SerH.poc_canonical_sh].  Both construct the identical generated record
   (legacy_version = TLS_1p2; ServerHello_body_false { tag = rnd; value = body }
   with sid = the echoed 32-byte session id, cipher_suite = cs, compression = 0, extensions =
   [key_share(X25519, ks); supported_versions(TLS_1p3)]); only the local module
   aliases differ.  Establishing this lets callers discharge the serializer's
   [sh == SerH.poc_canonical_sh rnd ks sid cs] precondition. *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 100"
let lemma_mk_server_hello_witness_eq_poc
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
      mk_server_hello_witness random key_share session_id cs ==
      SerH.poc_canonical_sh random key_share session_id cs)
  = ()
#pop-options

(* ----------------------------------------------------------------------- *)
(* Build-direction bridge (server ServerHello):                            *)
(* the Model-level canonical builder [CM.server_hello_of_selection]         *)
(* coincides with the send-path witness [mk_server_hello_witness] applied   *)
(* to the same random / key_share / cipher_suite.  Both reduce to the       *)
(* identical generated record (only the local module aliases differ,        *)
(* exactly as in [lemma_mk_server_hello_witness_eq_poc]).                    *)
(* ----------------------------------------------------------------------- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 100"
let lemma_server_hello_of_selection_eq_witness
  (sel: CS.server_handshake_selection)
  : Lemma
    (ensures
      CM.server_hello_of_selection sel ==
      mk_server_hello_witness
        (CM.sho_random sel)
        sel.CS.server_key_share_public
        (CM.sho_session_id sel)
        T.TLS_CHACHA20_POLY1305_SHA256)
  = ()
#pop-options

(* ----------------------------------------------------------------------- *)
(* The legacy_session_id echo is invisible to the send obligation.          *)
(*                                                                          *)
(* [CM.can_send_server_hello] constrains the ServerHello only through       *)
(* [CS.server_hello_matches_selection] (random / key share / cipher suite), *)
(* the serialized length (a constant 122 for any 32-byte echo) and          *)
(* [CS.event_raw_delta_legal], which just ties [raw_sent] to the            *)
(* serialization of the very same message.  None of these mention the       *)
(* echo, so the obligation transports between two witnesses that differ     *)
(* only in their 32-byte legacy_session_id.  This is what lets the send     *)
(* path echo the *stored ClientHello's* session id while the Model-level    *)
(* canonical builder names the selection's copy.                            *)
(* ----------------------------------------------------------------------- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let lemma_can_send_server_hello_session_id_irrelevant
  (st: CS.connection_state)
  (random: B.bytes)
  (key_share: B.bytes)
  (sid1: B.bytes)
  (sid2: B.bytes)
  : Lemma
    (requires
      Seq.length random == 32 /\
      Seq.length key_share == 32 /\
      Seq.length sid1 == 32 /\
      Seq.length sid2 == 32 /\
      (random <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst /\
      (let sh1 = mk_server_hello_witness random key_share sid1 T.TLS_CHACHA20_POLY1305_SHA256 in
       CM.can_send_server_hello st sh1
         (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh1)))))
    (ensures
      (let sh2 = mk_server_hello_witness random key_share sid2 T.TLS_CHACHA20_POLY1305_SHA256 in
       CM.can_send_server_hello st sh2
         (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh2)))))
  =
  let sh1 = mk_server_hello_witness random key_share sid1 T.TLS_CHACHA20_POLY1305_SHA256 in
  let sh2 = mk_server_hello_witness random key_share sid2 T.TLS_CHACHA20_POLY1305_SHA256 in
  lemma_mk_server_hello_witness_bytesize random key_share sid1 T.TLS_CHACHA20_POLY1305_SHA256;
  lemma_mk_server_hello_witness_bytesize random key_share sid2 T.TLS_CHACHA20_POLY1305_SHA256;
  ()
#pop-options

(* ----------------------------------------------------------------------- *)
(* Build-direction bridge for CanonicalProtocol's symbolic                 *)
(* LocalSendServerHello arm.                                                *)
(*                                                                          *)
(* [ST.server_local_event_input_ready]/LocalSendServerHello carries the     *)
(* Model send obligation on the *canonical* ServerHello                     *)
(* [CM.server_hello_of_selection selection] built from the state's server   *)
(* selection; the credentialed send path                                    *)
(* [S.process_local_event_with_credentials] instead requires the obligation *)
(* on the *witness* form [mk_server_hello_witness (payload[0:32])           *)
(* (x25519 (payload[32:64])) CHACHA] plus the HRR-sentinel guard on the     *)
(* payload random.  Under the input_ready facts (the state selection is     *)
(* [selection], its random and key-share match the payload slices, and      *)
(* key-share consistency) the two canonical builders coincide, so           *)
(* [can_send_server_hello] transfers by congruence, and the matches-clause  *)
(* forces the random off the HRR sentinel.                                  *)
(* ----------------------------------------------------------------------- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let lemma_can_send_server_hello_witness_of_selection
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
      CM.can_send_server_hello st (CM.server_hello_of_selection selection)
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ServerHello (CM.server_hello_of_selection selection)))))
    (ensures
      ((server_random <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
      (let sh = mk_server_hello_witness server_random
                  (CryptoSpec.x25519_public_from_private server_private_key)
                  (CM.stored_client_hello_session_id st)
                  T.TLS_CHACHA20_POLY1305_SHA256 in
       CM.can_send_server_hello st sh
         (CS.serialized_cleartext_tls_message
           (M.TlsHandshake (M.ServerHello sh)))))
  =
  let sh0 = CM.server_hello_of_selection selection in
  // 1. can_send_server_hello st sh0 _ carries, via the state selection,
  //    server_hello_matches_selection selection sh0.
  assert (CS.server_hello_matches_selection selection sh0);
  // 2. serverHello_random sh0 == Some (sho_random selection) (structural).
  assert (Sem.serverHello_random sh0 == Some (CM.sho_random selection));
  // matches => Seq.equal (sho_random selection) selection.server_random.
  Seq.lemma_eq_elim (CM.sho_random selection <: Seq.seq U8.t)
                    (selection.CS.server_random <: Seq.seq U8.t);
  Seq.lemma_eq_elim (selection.CS.server_random <: Seq.seq U8.t)
                    (server_random <: Seq.seq U8.t);
  // hence sho_random selection == selection.server_random == server_random,
  // and sho_random selection <> cst (type) => server_random <> cst.
  assert ((CM.sho_random selection <: Seq.lseq U8.t 32) ==
          (server_random <: Seq.lseq U8.t 32));
  assert ((server_random <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst);
  // 3. key-share consistency: x25519 server_private_key == server_key_share_public.
  Seq.lemma_eq_elim (Some?.v selection.CS.server_key_share_private <: Seq.seq U8.t)
                    (server_private_key <: Seq.seq U8.t);
  assert (CryptoSpec.x25519_public_from_private server_private_key ==
          (selection.CS.server_key_share_public <: B.bytes));
  // 4. the canonical builders coincide; congruence with (2)/(3) gives the
  //    witness equality, and can_send_server_hello transfers.
  lemma_server_hello_of_selection_eq_witness selection;
  assert (sh0 == mk_server_hello_witness server_random
                   (CryptoSpec.x25519_public_from_private server_private_key)
                   (CM.sho_session_id selection)
                   T.TLS_CHACHA20_POLY1305_SHA256);
  // The send path echoes the *stored ClientHello's* session id rather than the
  // selection's copy; the send obligation does not see the echo at all.
  lemma_can_send_server_hello_session_id_irrelevant
    st
    server_random
    (CryptoSpec.x25519_public_from_private server_private_key)
    (CM.sho_session_id selection)
    (CM.stored_client_hello_session_id st);
  ()
#pop-options

(* ----------------------------------------------------------------------- *)
(* Build-direction bridge for the server Endpoint's deferred                *)
(* LocalSendServerHello handler.  Given the raw state/material matching      *)
(* facts, the canonical [CM.server_hello_of_selection selection] can be sent, *)
(* so plain input_ready holds.  Mirrors the inline reasoning in              *)
(* [Driver.Handshake] (valid_selection + the two Model send lemmas); factored *)
(* into a lemma so the heavy [can_send_server_hello] derivation stays out of  *)
(* the large Endpoint deferred-action Pulse function (whose whole-function    *)
(* query is otherwise destabilised by the added obligations).                *)
(* ----------------------------------------------------------------------- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let lemma_input_ready_server_hello_of_selection
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
      selection.CS.server_selected_cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256)
    (ensures
      ST.server_local_event_input_ready st ST.LocalSendServerHello material)
  =
  // random equalities: selection.server_random == material[0:32], off cst.
  Seq.lemma_eq_elim (selection.CS.server_random <: Seq.seq U8.t)
                    (CL.raw_slice material 0 32 <: Seq.seq U8.t);
  assert ((selection.CS.server_random <: Seq.lseq U8.t 32) <>
          GSHbody.serverHello_body_cst);
  // private-key equality => key-share consistency.
  Seq.lemma_eq_elim (Some?.v selection.CS.server_key_share_private <: Seq.seq U8.t)
                    (CL.raw_slice material 32 64 <: Seq.seq U8.t);
  assert (CS.server_selection_key_share_consistent selection);
  // valid_selection holds (random off HRR sentinel + CHACHA cipher suite), so
  // the canonical builder matches the selection and serialises to 122 bytes;
  // legal_event / event_raw_delta_legal / can_send_server_hello follow, exactly
  // as in Driver.Handshake's inline discharge.
  assert (CM.valid_selection selection);
  let sh_sel = CM.server_hello_of_selection selection in
  CM.lemma_server_hello_of_selection_matches selection;
  CM.lemma_server_hello_of_selection_bytesize selection;
  assert (CS.server_hello_matches_selection selection sh_sel);
  assert (B.length (W.serialize_handshake (M.ServerHello sh_sel)) == 122);
  assert (CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh_sel);
    }));
  assert (CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh_sel);
    })
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh_sel)))
    B.empty);
  assert (CM.can_send_server_hello st sh_sel
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh_sel))));
  ()
#pop-options

(* ----------------------------------------------------------------------- *)
(* Aggregate discharge of the four conditional obligations threaded through *)
(* [S.process_local_event_with_credentials].  CanonicalProtocol's           *)
(* [server_process_local] calls that function with a *symbolic* kind, so it  *)
(* must establish the whole implication conjunction at once.  We prove it    *)
(* from the input_ready facts (both the plain and credentialed forms):       *)
(*  - VClF: input_ready (site 2) restates can_verify_client_finished's       *)
(*    conjuncts + [transcript+36]; the finished-length lemma bridges the     *)
(*    transcript bound (a Finished serializes to 36 bytes).                  *)
(*  - SendServerHello: input_ready (site 3) carries the send obligation on   *)
(*    the canonical [CM.server_hello_of_selection selection]; the SH build   *)
(*    bridge transfers it to the witness form + the HRR-sentinel guard.      *)
(*  - SendCertificateVerify: input_ready (site 4) carries [transcript+8+     *)
(*    |sig|]; the certificate-verify-length lemma bridges the serialized     *)
(*    length ([8+|sig|]).                                                    *)
(*  - SendCertificate: plain input_ready is [False] for this kind (it has no *)
(*    LocalSendCertificate case), so the obligation is vacuous.              *)
(* ----------------------------------------------------------------------- *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 200"
let lemma_server_process_local_obligations
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
                   T.TLS_CHACHA20_POLY1305_SHA256 in
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
  =
  match kind with
  | ST.LocalVerifyClientFinished ->
    introduce
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
      (B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
         Bounds.max_transcript_len /\
       CM.can_verify_client_finished st
         (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished))
    with _h.
    ( let fin = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished in
      lemma_serialize_handshake_finished_len fin;
      assert (CM.can_verify_client_finished st fin) )
  | ST.LocalSendServerHello ->
    introduce
      out_len_v == 127 ==>
      ((Seq.length (CL.raw_slice payload 0 32) == 32 ==>
        (CL.raw_slice payload 0 32 <: Seq.lseq U8.t 32) <>
          GSHbody.serverHello_body_cst) /\
       (let sh = mk_server_hello_witness
                   (CL.raw_slice payload 0 32)
                   (CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64))
                   (CM.stored_client_hello_session_id st)
                   T.TLS_CHACHA20_POLY1305_SHA256 in
        CM.can_send_server_hello st sh
          (CS.serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh)))))
    with _h.
    ( let server_random = CL.raw_slice payload 0 32 in
      let server_private_key = CL.raw_slice payload 32 64 in
      assert (B.length payload == 64);
      assert (Seq.length server_random == 32);
      assert (Seq.length server_private_key == 32);
      match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some selection ->
        lemma_can_send_server_hello_witness_of_selection
          st selection server_random server_private_key )
  | ST.LocalSendCertificateVerify ->
    introduce
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
      (B.length (W.serialize_handshake (M.CertificateVerify
         (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify))) ==
         8 + B.length (Sem.certificateVerify_signature_bytes
           (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)) /\
       B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
         B.length (W.serialize_handshake (M.CertificateVerify
           (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify))) <=
         Bounds.max_transcript_len)
    with _h.
    ( let cv = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
      lemma_serialize_handshake_certificate_verify_len cv )
  | ST.LocalSendCertificate ->
    // 1 <= |chain| comes from the caller obligation (established at the send
    // site by a runtime chain non-emptiness check); |chain| <= 16610 comes from
    // server_local_event_input_ready_with_credentials's 13 + |chain| + 17 <=
    // 16640.  The serialize-length equation is the mk_cert_witness bytesize.
    lemma_mk_cert_witness_bytesize certificate_chain
  | _ -> ()
#pop-options

(* ----------------------------------------------------------------------- *)
(* TODO-A1 cst-guard runtime check.                                        *)
(* The ServerHello random generated by the server must differ from the     *)
(* HelloRetryRequest sentinel [GSHbody.serverHello_body_cst]; otherwise     *)
(* [mk_server_hello_witness] would emit an HRR.  Since the random is freshly *)
(* generated by [Crypto.random_bytes], we discharge the (cryptographically  *)
(* impossible) collision with a runtime 32-byte comparison.                 *)
(* ----------------------------------------------------------------------- *)
(* Copy of the generated (private) serverHello_body_sz_contradiction. *)
let hrr_sentinel_sz_contradiction (j: SZ.t)
  : Lemma (requires SZ.v j < 32 /\ ~(j == 0sz) /\ ~(j == 1sz) /\ ~(j == 2sz) /\ ~(j == 3sz) /\ ~(j == 4sz) /\ ~(j == 5sz) /\ ~(j == 6sz) /\ ~(j == 7sz) /\ ~(j == 8sz) /\ ~(j == 9sz) /\ ~(j == 10sz) /\ ~(j == 11sz) /\ ~(j == 12sz) /\ ~(j == 13sz) /\ ~(j == 14sz) /\ ~(j == 15sz) /\ ~(j == 16sz) /\ ~(j == 17sz) /\ ~(j == 18sz) /\ ~(j == 19sz) /\ ~(j == 20sz) /\ ~(j == 21sz) /\ ~(j == 22sz) /\ ~(j == 23sz) /\ ~(j == 24sz) /\ ~(j == 25sz) /\ ~(j == 26sz) /\ ~(j == 27sz) /\ ~(j == 28sz) /\ ~(j == 29sz) /\ ~(j == 30sz) /\ ~(j == 31sz)) (ensures False) = ()

#push-options "--z3rlimit 16"
inline_for_extraction
let hrr_sentinel_byte (j: SZ.t { SZ.v j < 32 })
  : (b: U8.t { b == Seq.index GSHbody.serverHello_body_cst (SZ.v j) }) =
  assert_norm (FStar.List.Tot.Base.length [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] == 32);
  FStar.Seq.Properties.lemma_seq_of_list_index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] (SZ.v j);
  if j = 0sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 0 == 0xcfuy); 0xcfuy) else
  if j = 1sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 1 == 0x21uy); 0x21uy) else
  if j = 2sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 2 == 0xaduy); 0xaduy) else
  if j = 3sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 3 == 0x74uy); 0x74uy) else
  if j = 4sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 4 == 0xe5uy); 0xe5uy) else
  if j = 5sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 5 == 0x9auy); 0x9auy) else
  if j = 6sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 6 == 0x61uy); 0x61uy) else
  if j = 7sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 7 == 0x11uy); 0x11uy) else
  if j = 8sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 8 == 0xbeuy); 0xbeuy) else
  if j = 9sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 9 == 0x1duy); 0x1duy) else
  if j = 10sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 10 == 0x8cuy); 0x8cuy) else
  if j = 11sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 11 == 0x02uy); 0x02uy) else
  if j = 12sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 12 == 0x1euy); 0x1euy) else
  if j = 13sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 13 == 0x65uy); 0x65uy) else
  if j = 14sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 14 == 0xb8uy); 0xb8uy) else
  if j = 15sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 15 == 0x91uy); 0x91uy) else
  if j = 16sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 16 == 0xc2uy); 0xc2uy) else
  if j = 17sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 17 == 0xa2uy); 0xa2uy) else
  if j = 18sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 18 == 0x11uy); 0x11uy) else
  if j = 19sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 19 == 0x16uy); 0x16uy) else
  if j = 20sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 20 == 0x7auy); 0x7auy) else
  if j = 21sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 21 == 0xbbuy); 0xbbuy) else
  if j = 22sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 22 == 0x8cuy); 0x8cuy) else
  if j = 23sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 23 == 0x5euy); 0x5euy) else
  if j = 24sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 24 == 0x07uy); 0x07uy) else
  if j = 25sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 25 == 0x9euy); 0x9euy) else
  if j = 26sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 26 == 0x09uy); 0x09uy) else
  if j = 27sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 27 == 0xe2uy); 0xe2uy) else
  if j = 28sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 28 == 0xc8uy); 0xc8uy) else
  if j = 29sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 29 == 0xa8uy); 0xa8uy) else
  if j = 30sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 30 == 0x33uy); 0x33uy) else
  if j = 31sz then (assert_norm (FStar.List.Tot.Base.index [0xcfuy; 0x21uy; 0xaduy; 0x74uy; 0xe5uy; 0x9auy; 0x61uy; 0x11uy; 0xbeuy; 0x1duy; 0x8cuy; 0x02uy; 0x1euy; 0x65uy; 0xb8uy; 0x91uy; 0xc2uy; 0xa2uy; 0x11uy; 0x16uy; 0x7auy; 0xbbuy; 0x8cuy; 0x5euy; 0x07uy; 0x9euy; 0x09uy; 0xe2uy; 0xc8uy; 0xa8uy; 0x33uy; 0x9cuy] 31 == 0x9cuy); 0x9cuy) else
  (hrr_sentinel_sz_contradiction j; 0uy)
#pop-options

let lemma_pointwise_iff_raw_slice_cst (mb: B.bytes)
  : Lemma (requires B.length mb >= 32)
          (ensures ((forall (k:nat). k < 32 ==> Seq.index mb k == Seq.index GSHbody.serverHello_body_cst k) <==>
                    ((CL.raw_slice mb 0 32 <: Seq.lseq U8.t 32) == GSHbody.serverHello_body_cst)))
  = let s : Seq.lseq U8.t 32 = CL.raw_slice mb 0 32 in
    assert (s == Seq.slice mb 0 32);
    let cst = GSHbody.serverHello_body_cst in
    introduce (forall (k:nat). k < 32 ==> Seq.index mb k == Seq.index cst k) ==> (s == cst)
    with _. (
      Seq.lemma_eq_intro s cst
    );
    introduce (s == cst) ==> (forall (k:nat). k < 32 ==> Seq.index mb k == Seq.index cst k)
    with _. ()

let lemma_range_ext_cst (mb: B.bytes) (n:nat) (ae:bool) (mv cv: U8.t)
  : Lemma (requires B.length mb >= 32 /\ n < 32 /\
                    mv == Seq.index mb n /\
                    cv == Seq.index GSHbody.serverHello_body_cst n /\
                    (ae <==> (forall (k:nat). k < n ==> Seq.index mb k == Seq.index GSHbody.serverHello_body_cst k)))
          (ensures ((ae && (mv = cv)) <==>
                    (forall (k:nat). k < n + 1 ==> Seq.index mb k == Seq.index GSHbody.serverHello_body_cst k)))
  = ()

fn server_random_differs_from_cst (material: array U8.t) (#p: perm) (#mb: erased (b:B.bytes{B.length b >= 32}))
  requires pts_to material #p mb
  returns b: bool
  ensures pts_to material #p mb **
          pure (b <==> (CL.raw_slice mb 0 32 <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst)
{
  let mut j = 0sz;
  let mut all_equal = true;
  while (
    let jv = Ref.read j;
    jv `SZ.lt` 32sz
  )
  invariant exists* je ae.
    pts_to material #p mb **
    Ref.pts_to j je **
    Ref.pts_to all_equal ae **
    pure (SZ.v je <= 32 /\ B.length mb >= 32 /\
          (ae <==> (forall (k:nat). k < SZ.v je ==> Seq.index mb k == Seq.index GSHbody.serverHello_body_cst k)))
  decreases (32 - SZ.v (Ref.read j))
  {
    let jv = Ref.read j;
    let mv = material.(jv);
    let cv = hrr_sentinel_byte jv;
    let cur = Ref.read all_equal;
    lemma_range_ext_cst mb (SZ.v jv) cur mv cv;
    Ref.write all_equal (cur && (mv = cv));
    Ref.write j (jv `SZ.add` 1sz);
  };
  lemma_pointwise_iff_raw_slice_cst mb;
  let res = Ref.read all_equal;
  not res
}

noextract
let lemma_server_handshake_write_seal_some
  (st:CS.connection_state)
  (aad:B.bytes)
  (msg:M.tls_message)
  : Lemma
      (requires ST.server_end_to_end_invariant st /\
                st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                (st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
                 st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent) /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
      (ensures Some? (R.seal
        st.CS.cs_model.CS.model_record.CS.record_write
        aad
        {
          R.content_type = T.Application_data;
          R.fragment = TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment msg;
        }))
=
  assert_norm (ST.server_end_to_end_invariant st ==
    (ST.server_state_correct st /\
     ST.server_raw_to_message_replay_consistent st));
  assert (ST.server_state_correct st);
  assert_norm (ST.server_state_correct st ==
    (ST.server_state_core_correct st /\
     TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_replay_consistent st /\
     TLS13.Spec.StateMachine.Replay.connection_state_received_decode_replay_consistent st));
  assert (ST.server_state_core_correct st);
  assert_norm (ST.server_state_core_correct st ==
    (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
     Some? st.CS.cs_model.CS.model_config.CS.config_server /\
     (match st.CS.cs_model.CS.model_config.CS.config_server with
      | Some cfg ->
        B.length cfg.CS.server_certificate_chain <=
          Bounds.max_server_certificate_chain_len
      | None -> False) /\
     TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
     TLS13.Spec.StateMachine.Replay.connection_state_full_log_consistent_for_role CS.ServerEndpoint st));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st);
  CSL.lemma_server_handshake_write_record_has_keys st;
  assert (TLS13.Spec.StateMachine.Replay.connection_state_full_log_consistent_for_role CS.ServerEndpoint st);
  assert (TLS13.Spec.StateMachine.Log.connection_state_layered_log_consistent_for_role CS.ServerEndpoint st);
  assert (TLS13.Spec.StateMachine.Log.connection_state_record_keys_consistent_for_role CS.ServerEndpoint st);
  assert (TLS13.Spec.StateMachine.KeyMaterial.model_record_keys_consistent_for_role CS.ServerEndpoint st.CS.cs_model);
  assert (TLS13.Spec.StateMachine.KeyMaterial.record_write_key_schedule_projection_for_role
    CS.ServerEndpoint
    st.CS.cs_model);
  assert (
    match st.CS.cs_model.CS.model_record.CS.record_write.R.key,
          st.CS.cs_model.CS.model_record.CS.record_write.R.static_iv with
    | Some _, Some _ -> True
    | _, _ -> False);
  CM.lemma_seal_some_of_keys
    st.CS.cs_model.CS.model_record.CS.record_write
    aad
    {
      R.content_type = T.Application_data;
      R.fragment = TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment msg;
    }

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
                   (W.serialize_handshake (M.ServerHello sh)) /\
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
{
  unfold (connection_exactly s 'st0);
  CLH.mark_sent_server_hello
    s
    raw
    fragment
    fragment_len
    lsh
    #sh;
  fold (connection_exactly
    s
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = raw_len;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = Ghost.reveal 'raw_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_server_hello_state_evolves
    'st0
    sh
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (SZ.v raw_len <= B.length 'old_network_out));
  assert (pure (ST.response_network_out resp 'old_network_out ==
    Seq.slice 'old_network_out 0 (SZ.v raw_len)));
  assert (pure (Seq.equal
    (ST.response_network_out resp 'old_network_out)
    (Ghost.reveal 'raw_bytes)));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    ST.LocalSendServerHello
    B.empty
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    ST.LocalSendServerHello
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (TLS13.Spec.StateMachine.Replay.event_protected_raw_segmented_success
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    ST.LocalSendServerHello
    B.empty
    'old_network_out
    'old_app_out));
  resp
}

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
                 Seq.length (Ghost.reveal server_random_bytes) == 32 /\
                 (Ghost.reveal server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst /\
                 Seq.length (Ghost.reveal server_key_share_bytes) == 32 /\
                 Ghost.reveal sh ==
                   mk_server_hello_witness
                     (Ghost.reveal server_random_bytes)
                     (Ghost.reveal server_key_share_bytes)
                     (CM.stored_client_hello_session_id 'st0)
                     (T.TLS_CHACHA20_POLY1305_SHA256) /\
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
{
  lemma_mk_server_hello_witness_eq_poc
    (Ghost.reveal server_random_bytes)
    (Ghost.reveal server_key_share_bytes)
    (CM.stored_client_hello_session_id 'st0)
    (T.TLS_CHACHA20_POLY1305_SHA256);
  let written_raw =
    Ser.serialize_server_hello_record_from_selection
      #sh
      #server_random_bytes
      #server_key_share_bytes
      #(Ghost.hide (CM.stored_client_hello_session_id 'st0 <: B.bytes))
      #(Ghost.hide (T.TLS_CHACHA20_POLY1305_SHA256 <: GCS.cipherSuite))
      lsh
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  assert (pure (B.length network_out_bytes == 127));
  assert (pure (SZ.v written_raw == 127));
  assert (pure (Seq.equal
    network_out_bytes
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh)))));
  assert (pure (CM.can_send_server_hello
    'st0
    sh
    network_out_bytes));

  let mut fragment = [| 0uy; 122sz |];
  let written_fragment =
    Ser.serialize_server_hello_from_selection
      #sh
      #server_random_bytes
      #server_key_share_bytes
      #(Ghost.hide (CM.stored_client_hello_session_id 'st0 <: B.bytes))
      #(Ghost.hide (T.TLS_CHACHA20_POLY1305_SHA256 <: GCS.cipherSuite))
      lsh
      fragment
      122sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 122));
  assert (pure (SZ.v written_fragment == 122));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.ServerHello sh))));
  assert (pure (SZ.v written_fragment <= Bounds.max_server_hello_len));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_server_hello
    s
    network_out
    fragment
    written_fragment
    lsh
    #sh;
  fold (connection_exactly
    s
    (CM.sent_server_hello_state 'st0 sh network_out_bytes));

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_server_hello_state_evolves
    'st0
    sh
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_server_hello_state 'st0 sh network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_server_hello_state 'st0 sh network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_server_hello_state 'st0 sh network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    ST.LocalSendServerHello
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    ST.LocalSendServerHello
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (TLS13.Spec.StateMachine.Replay.event_protected_raw_segmented_success
    (Ghost.reveal ev)
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (Ghost.reveal ev)
    network_out_bytes));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    ST.LocalSendServerHello
    B.empty
    network_out_bytes
    'old_app_out));
  resp
}

fn build_server_hello_from_arrays
  (server_random:array U8.t)
  (server_key_share:array U8.t)
  (session_id:array U8.t)
  (#sh:erased GSH.serverHello)
  requires pts_to server_random 'server_random_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pts_to session_id 'session_id_bytes **
           pure (B.length 'server_random_bytes == 32 /\
                B.length 'server_key_share_bytes == 32 /\
                B.length 'session_id_bytes == 32 /\
                // TODO-A1: ServerHello random must differ from the HRR sentinel
                (Seq.length (Ghost.reveal 'server_random_bytes) == 32 ==>
                 (Ghost.reveal 'server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                Ghost.reveal sh == (mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (Ghost.reveal 'session_id_bytes) (T.TLS_CHACHA20_POLY1305_SHA256)))
  returns lsh:IM.server_hello
  ensures pts_to server_random 'server_random_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          pts_to session_id 'session_id_bytes **
          IM.is_valid_server_hello lsh sh
{
  let random_vec = V.alloc 0uy 32sz;
  let session_id_vec = V.alloc 0uy 32sz;
  let key_share_vec = V.alloc 0uy 32sz;
  CR.copy_fixed32_array_to_vec server_random random_vec;
  CR.copy_fixed32_array_to_vec session_id session_id_vec;
  CR.copy_fixed32_array_to_vec server_key_share key_share_vec;
  let lsh = {
    IM.server_hello_random = random_vec;
    IM.server_hello_session_id = session_id_vec;
    IM.server_hello_key_share = key_share_vec;
    IM.server_hello_cipher_suite = 0x1303us;
  };
  with random_bytes. assert (V.pts_to random_vec random_bytes);
  with session_id_vec_bytes. assert (V.pts_to session_id_vec session_id_vec_bytes);
  with key_share_bytes. assert (V.pts_to key_share_vec key_share_bytes);
  assert (pure (Seq.equal random_bytes (Ghost.reveal 'server_random_bytes)));
  assert (pure (Seq.equal session_id_vec_bytes (Ghost.reveal 'session_id_bytes)));
  assert (pure (Seq.equal key_share_bytes (Ghost.reveal 'server_key_share_bytes)));
  assert_norm (IM.cipher_suite_matches 0x1303us T.TLS_CHACHA20_POLY1305_SHA256);
  rewrite (V.pts_to random_vec random_bytes)
    as (V.pts_to lsh.IM.server_hello_random random_bytes);
  rewrite (V.pts_to session_id_vec session_id_vec_bytes)
    as (V.pts_to lsh.IM.server_hello_session_id session_id_vec_bytes);
  rewrite (V.pts_to key_share_vec key_share_bytes)
    as (V.pts_to lsh.IM.server_hello_key_share key_share_bytes);
  fold (IM.is_valid_server_hello
    lsh
    (Ghost.reveal sh));
  lsh
}

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
                 // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                 // sentinel (serverHello_body_cst); unprovable for a symbolic random,
                 // so threaded as an explicit caller obligation.
                 (Seq.length (Ghost.reveal 'server_random_bytes) == 32 ==>
                  (Ghost.reveal 'server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                 (let sh = mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (T.TLS_CHACHA20_POLY1305_SHA256) in
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
                 (let sh = mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (T.TLS_CHACHA20_POLY1305_SHA256) in
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
{
  let sh = Ghost.hide (mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (T.TLS_CHACHA20_POLY1305_SHA256) <: GSH.serverHello);
  let mut session_id = [| 0uy; 32sz |];
  rewrite (connection_exactly s 'st0) as (CR.connection_exactly s 'st0);
  CQ.read_client_hello_session_id s session_id;
  rewrite (CR.connection_exactly s 'st0) as (connection_exactly s 'st0);
  with sid_bytes. assert (pts_to session_id sid_bytes);
  Seq.lemma_eq_elim (Ghost.reveal sid_bytes) (CM.stored_client_hello_session_id 'st0);
  let lsh =
    build_server_hello_from_arrays
      server_random
      server_key_share
      session_id
      #sh;
  process_send_server_hello_serialized
    s
    lsh
    #sh
    #('server_random_bytes)
    #('server_key_share_bytes)
    network_out
    network_out_len
    app_out
    app_out_len
}

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
                 // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                 // sentinel (serverHello_body_cst); unprovable for a symbolic random,
                 // so threaded as an explicit caller obligation.
                 (Seq.length (Ghost.reveal 'server_random_bytes) == 32 ==>
                  (Ghost.reveal 'server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                 (let sh = mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (CryptoSpec.x25519_public_from_private
                     (Ghost.reveal 'server_private_key_bytes)) (CM.stored_client_hello_session_id 'st0) (T.TLS_CHACHA20_POLY1305_SHA256) in
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
                       (Ghost.reveal 'server_private_key_bytes)) (CM.stored_client_hello_session_id 'st0) (T.TLS_CHACHA20_POLY1305_SHA256) in
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
{
  let mut server_key_share = [| 0uy; 32sz |];
  Crypto.x25519_public_from_private server_private_key server_key_share;
  with server_key_share_bytes. assert (pts_to server_key_share server_key_share_bytes);
  assert (pure (server_key_share_bytes ==
    CryptoSpec.x25519_public_from_private (Ghost.reveal 'server_private_key_bytes)));
  assert (pure (B.length server_key_share_bytes == 32));
  let sh = Ghost.hide (mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (T.TLS_CHACHA20_POLY1305_SHA256));
  assert (pure (CM.can_send_server_hello
    'st0
    (Ghost.reveal sh)
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))))));
  let resp =
    process_send_server_hello_from_arrays
      s
      server_random
      server_key_share
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (connection_exactly s st1 **
            pts_to server_random 'server_random_bytes **
            pts_to server_key_share server_key_share_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (st1 ==
    CM.sent_server_hello_state 'st0 (Ghost.reveal sh) network_out_bytes));
  assert (pure (Seq.equal
    network_out_bytes
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))))));
  resp
}

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
{
  let ee : erased GEE.encryptedExtensions =
    Ghost.hide ([] <: GEE.encryptedExtensions);


  let alpn = V.alloc 0uy 255sz;
  let lee = {
    IM.encrypted_extensions_alpn = alpn;
    IM.encrypted_extensions_alpn_len = 0sz;
    IM.encrypted_extensions_has_alpn = false;
  };
  assert (pure (lee.IM.encrypted_extensions_alpn == alpn));
  with alpn_bytes. assert (V.pts_to alpn alpn_bytes);
  assert (pure (V.is_full_vec alpn));
  assert (pure (V.length alpn == IM.max_alpn_len));
  assert (pure (SZ.v lee.IM.encrypted_extensions_alpn_len <= B.length alpn_bytes));
  rewrite (V.pts_to alpn alpn_bytes)
    as (V.pts_to lee.IM.encrypted_extensions_alpn alpn_bytes);
  fold (IM.is_valid_encrypted_extensions lee (Ghost.reveal ee));

  let mut fragment = [| 0uy; 6sz |];
  let written_fragment =
    Ser.serialize_empty_encrypted_extensions
      fragment
      6sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 6));
  assert (pure (SZ.v written_fragment == 6));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.EncryptedExtensions (Ghost.reveal ee)))));
  lemma_server_handshake_write_seal_some
    'st0
    (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee)));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.EncryptedExtensions (Ghost.reveal ee))
      s.records.write
      fragment
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length network_out_bytes == 28));
  assert (pure (SZ.v written_raw == 28));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.Application_data 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee)))
    network_out_bytes));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
    })
    network_out_bytes
    B.empty;
  assert (pure (TLS13.Spec.StateMachine.Replay.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Log.connection_state_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.model_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_write_key_schedule_projection_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (CM.can_send_encrypted_extensions
    'st0
    (Ghost.reveal ee)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_encrypted_extensions
    s
    network_out
    fragment
    written_fragment
    lee
    #ee;
  fold (connection_exactly
    s
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes));

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_encrypted_extensions_state_evolves
    'st0
    (Ghost.reveal ee)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    network_out_bytes
    'old_app_out));
  resp
}

#push-options "--fuel 3 --ifuel 2 --z3rlimit 200"
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
{
  assert_norm (IM.max_certificate_chain_bytes == 32768);
  let chain_bytes = V.alloc 0uy 32768sz;
  with old_chain_bytes. assert (V.pts_to chain_bytes old_chain_bytes);
  assert (pure (V.is_full_vec chain_bytes));
  assert (pure (V.length chain_bytes == IM.max_certificate_chain_bytes));
  assert (pure (B.length old_chain_bytes == IM.max_certificate_chain_bytes));
  V.to_array_pts_to chain_bytes;
  let copy_result =
    O.copy_server_certificate_chain
      creds
      (V.vec_to_array chain_bytes)
      32768sz;
  match copy_result {
    None -> {
      V.to_vec_pts_to chain_bytes;
      V.free chain_bytes;
      assert (pure (
        B.length (Ghost.reveal 'certificate_chain) >
          IM.max_certificate_chain_bytes));
      None
    }
    Some certificate_len -> {
      V.to_vec_pts_to chain_bytes;
      with copied_chain_bytes. assert (V.pts_to chain_bytes copied_chain_bytes);
      assert (pure (B.length copied_chain_bytes == IM.max_certificate_chain_bytes));
      assert (pure (SZ.v certificate_len ==
        B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (SZ.v certificate_len <= IM.max_certificate_chain_bytes));
      assert (pure (Seq.equal
        (Seq.slice copied_chain_bytes 0 (SZ.v certificate_len))
        (Ghost.reveal 'certificate_chain)));

      assert_norm (IM.max_certificate_chain_entries == 8);
      let cert_offsets = V.alloc 0sz 8sz;
      let cert_lens = V.alloc 0sz 8sz;
      with old_offsets. assert (V.pts_to cert_offsets old_offsets);
      with old_lens. assert (V.pts_to cert_lens old_lens);
      assert (pure (V.is_full_vec cert_offsets));
      assert (pure (V.is_full_vec cert_lens));
      assert (pure (V.length cert_offsets == IM.max_certificate_chain_entries));
      assert (pure (V.length cert_lens == IM.max_certificate_chain_entries));

      V.to_array_pts_to cert_offsets;
      (V.vec_to_array cert_offsets).(0sz) <- 0sz;
      V.to_vec_pts_to cert_offsets;
      V.to_array_pts_to cert_lens;
      (V.vec_to_array cert_lens).(0sz) <- certificate_len;
      V.to_vec_pts_to cert_lens;

      with offsets. assert (V.pts_to cert_offsets offsets);
      with lens. assert (V.pts_to cert_lens lens);
      assert (pure (Seq.length offsets == IM.max_certificate_chain_entries));
      assert (pure (Seq.length lens == IM.max_certificate_chain_entries));
      assert (pure (Seq.index offsets 0 == 0sz));
      assert (pure (Seq.index lens 0 == certificate_len));

      let lcert = {
        IM.certificate_msg_chain_bytes = chain_bytes;
        IM.certificate_msg_chain_bytes_len = certificate_len;
        IM.certificate_msg_cert_offsets = cert_offsets;
        IM.certificate_msg_cert_lens = cert_lens;
        IM.certificate_msg_cert_count = 1sz;
      };
      rewrite (V.pts_to chain_bytes copied_chain_bytes) as
        (V.pts_to lcert.IM.certificate_msg_chain_bytes copied_chain_bytes);
      rewrite (V.pts_to cert_offsets offsets) as
        (V.pts_to lcert.IM.certificate_msg_cert_offsets offsets);
      rewrite (V.pts_to cert_lens lens) as
        (V.pts_to lcert.IM.certificate_msg_cert_lens lens);
      assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len <=
        B.length copied_chain_bytes));
      assert (pure (SZ.v lcert.IM.certificate_msg_cert_count <= Seq.length offsets));
      assert (pure (SZ.v lcert.IM.certificate_msg_cert_count <= Seq.length lens));
      assert (pure (IM.certificate_chain_matches
        copied_chain_bytes
        (SZ.v certificate_len)
        offsets
        lens
        1
        [Ghost.reveal 'certificate_chain]));
      assert (pure (SZ.v certificate_len <= 32768));
      mk_cert_witness_chain_matches_lemma
        copied_chain_bytes
        (SZ.v certificate_len)
        offsets
        lens
        (Ghost.reveal 'certificate_chain);
      fold (IM.is_valid_certificate_msg
        lcert
        (mk_cert_witness (Ghost.reveal 'certificate_chain)));
      assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
        B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (lcert.IM.certificate_msg_cert_count == 1sz));
      Some lcert
    }
  }
}
#pop-options

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
                     (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) /\
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
{
  let fragment = V.alloc 0uy fragment_len;
  with old_fragment_bytes. assert (V.pts_to fragment old_fragment_bytes);
  V.pts_to_len fragment;
  assert (pure (B.length old_fragment_bytes == SZ.v fragment_len));
  V.to_array_pts_to fragment;
  lemma_mk_cert_witness_eq_poc (Ghost.reveal chain);
  let written_fragment =
    Ser.serialize_certificate_from_credential
      #cert
      #chain
      lcert
      (V.vec_to_array fragment)
      fragment_len;
  with fragment_bytes. assert (pts_to (V.vec_to_array fragment) fragment_bytes);
  assert (pure (B.length fragment_bytes == SZ.v fragment_len));
  assert (pure (SZ.v written_fragment == SZ.v fragment_len));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));
  assert (pure (
    B.length (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) ==
    SZ.v fragment_len));
  lemma_server_handshake_write_seal_some
    'st0
    (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.Certificate (Ghost.reveal cert)));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.Certificate (Ghost.reveal cert))
      s.records.write
      (V.vec_to_array fragment)
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (SZ.v written_raw == SZ.v fragment_len + 22));
  assert (pure (SZ.v written_raw == SZ.v network_out_len));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.Application_data 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.Certificate (Ghost.reveal cert)))
    network_out_bytes));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes
    B.empty;
  assert (pure (TLS13.Spec.StateMachine.Replay.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Log.connection_state_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.model_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_write_key_schedule_projection_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (CM.can_send_certificate
    'st0
    (Ghost.reveal cert)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_certificate
    s
    network_out
    (V.vec_to_array fragment)
    written_fragment
    lcert
    #cert;
  fold (connection_exactly
    s
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes));
  V.to_vec_pts_to fragment;
  V.free fragment;

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_certificate_state_evolves
    'st0
    (Ghost.reveal cert)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    ST.LocalSendCertificate
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    ST.LocalSendCertificate
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    ST.LocalSendCertificate
    B.empty
    network_out_bytes
    'old_app_out));
  resp
}

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
                 B.length (W.serialize_handshake
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
{
  let built = build_certificate_from_credentials creds;
  match built {
    None -> {
      assert_norm (IM.max_certificate_chain_bytes == 32768);
      assert (pure (
        B.length (Ghost.reveal 'certificate_chain) >
          IM.max_certificate_chain_bytes));
      assert (pure (
        13 + B.length (Ghost.reveal 'certificate_chain) + 17 <= 16640));
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    Some lcert -> {
      let cert:erased GCert.certificate =
        Ghost.hide (mk_cert_witness (Ghost.reveal 'certificate_chain));
      // Branch spec's certificate_msg_matches_server_config requires the exact
      // Sem.certificate_entries (mk_cert_witness chain) == [chain]; the branch SMT context
      // (unlike pr265's) does not auto-unfold this, so call the lemma explicitly.
      // 1 <= |chain| <= 32768 is available here (precondition of build_certificate_from_credentials).
      mk_cert_witness_entries_unconditional (Ghost.reveal 'certificate_chain);
      assert (pure (lcert.IM.certificate_msg_cert_count == 1sz));
      assert (pure (exists (certificate:B.bytes).
        Sem.certificate_entries (Ghost.reveal cert) == [certificate]));
      assert (pure (Sem.certificate_entries (Ghost.reveal cert) <> []));
      assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
        B.length (Ghost.reveal 'certificate_chain)));
      // TODO-A1: |serialize_handshake (Certificate cert)| == 13 + |chain| was provided by the
      // now-deleted W.lemma_serialize_certificate_from_single_chain_len. For a single-entry
      // certificate with empty request-context and empty extensions this is exactly the wire
      // length (4 hs-header + 1 ctx-len + 3 list-len + 3 entry-len + |chain| + 2 ext-len). It is
      // now threaded in as a precondition of this function (see requires below).
      assert (pure (
        B.length (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) ==
          13 + B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (
        13 + B.length (Ghost.reveal 'certificate_chain) <=
          Bounds.max_transcript_len));
      assert (pure (
        SZ.fits (SZ.v lcert.IM.certificate_msg_chain_bytes_len + 13)));
      let fragment_len =
        SZ.add lcert.IM.certificate_msg_chain_bytes_len 13sz;
      assert (pure (SZ.v fragment_len ==
        B.length (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));
      assert (pure (SZ.v fragment_len + 17 <= 16640));
      assert (pure (SZ.v network_out_len == SZ.v fragment_len + 22));
      assert (pure (B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        SZ.v fragment_len <= Bounds.max_transcript_len));
      assert (pure (
        match 'st0.CS.cs_model.CS.model_config.CS.config_server with
        | Some cfg -> CS.certificate_msg_matches_server_config cfg (Ghost.reveal cert)
        | None -> False));
      process_send_certificate_serialized
        s
        lcert
        #cert
        #('certificate_chain)
        fragment_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
  }
}

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
                     (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
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
{
  let fragment = V.alloc 0uy fragment_len;
  with old_fragment_bytes. assert (V.pts_to fragment old_fragment_bytes);
  V.pts_to_len fragment;
  assert (pure (B.length old_fragment_bytes == SZ.v fragment_len));
  V.to_array_pts_to fragment;
  let written_fragment =
    Ser.serialize_certificate_verify_from_signature
      #cv
      lcv
      (V.vec_to_array fragment)
      fragment_len;
  with fragment_bytes. assert (pts_to (V.vec_to_array fragment) fragment_bytes);
  assert (pure (B.length fragment_bytes == SZ.v fragment_len));
  assert (pure (SZ.v written_fragment == SZ.v fragment_len));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (
    B.length (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) ==
    SZ.v fragment_len));
  lemma_server_handshake_write_seal_some
    'st0
    (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)));
  IM.free_certificate_verify lcv;

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.CertificateVerify (Ghost.reveal cv))
      s.records.write
      (V.vec_to_array fragment)
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (SZ.v written_raw == SZ.v fragment_len + 22));
  assert (pure (SZ.v written_raw == SZ.v network_out_len));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.Application_data 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)))
    network_out_bytes));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty;
  assert (pure (TLS13.Spec.StateMachine.Replay.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Log.connection_state_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.model_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_write_key_schedule_projection_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (CM.can_send_certificate_verify
    'st0
    (Ghost.reveal cv)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_certificate_verify
    s
    network_out
    (V.vec_to_array fragment)
    written_fragment
    #cv;
  fold (connection_exactly
    s
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes));
  V.to_vec_pts_to fragment;
  V.free fragment;

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_certificate_verify_state_evolves
    'st0
    (Ghost.reveal cv)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
  resp
}

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
                     (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
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
{
  let fragment = V.alloc 0uy fragment_len;
  with old_fragment_bytes. assert (V.pts_to fragment old_fragment_bytes);
  V.pts_to_len fragment;
  assert (pure (B.length old_fragment_bytes == SZ.v fragment_len));
  V.to_array_pts_to fragment;

  unfold (connection_exactly s 'st0);
  let written_fragment =
    CLH.serialize_stored_certificate_verify_fragment
      s
      #cv
      (V.vec_to_array fragment)
      fragment_len
      #'st0;
  fold (connection_exactly s 'st0);
  with fragment_bytes. assert (pts_to (V.vec_to_array fragment) fragment_bytes);
  assert (pure (B.length fragment_bytes == SZ.v fragment_len));
  assert (pure (SZ.v written_fragment == SZ.v fragment_len));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (
    B.length (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) ==
    SZ.v fragment_len));
  lemma_server_handshake_write_seal_some
    'st0
    (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.CertificateVerify (Ghost.reveal cv))
      s.records.write
      (V.vec_to_array fragment)
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (SZ.v written_raw == SZ.v fragment_len + 22));
  assert (pure (SZ.v written_raw == SZ.v network_out_len));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.Application_data 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)))
    network_out_bytes));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty;
  assert (pure (TLS13.Spec.StateMachine.Replay.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Log.connection_state_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.model_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_write_key_schedule_projection_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (CM.can_send_certificate_verify
    'st0
    (Ghost.reveal cv)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_certificate_verify
    s
    network_out
    (V.vec_to_array fragment)
    written_fragment
    #cv;
  fold (connection_exactly
    s
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes));
  V.to_vec_pts_to fragment;
  V.free fragment;

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_certificate_verify_state_evolves
    'st0
    (Ghost.reveal cv)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
  resp
}

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
{
  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with transcript_storage transcript_len. _;
  let transcript_len_runtime = !s.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  assert (pure (CR.byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));
  V.to_array_pts_to s.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array s.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to s.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes ==
    Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  unfold (CR.key_schedule_exactly
    s.handshake.keys
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (CR.traffic_key_material_exactly
    s.handshake.keys.server_handshake_traffic
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  with sh_present sh_secret sh_key sh_iv. _;
  CR.lemma_traffic_key_material_match_present_of_some
    sh_present
    sh_secret
    sh_key
    sh_iv
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic;
  assert (pure (sh_present));
  assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic ==
    Some {
      CS.traffic_secret = sh_secret;
      CS.traffic_key = sh_key;
      CS.traffic_iv = sh_iv;
    }));

  V.to_array_pts_to s.handshake.keys.server_handshake_traffic.traffic_secret;
  let mut verify_data = [| 0uy; 32sz |];
  KS.finished_verify_data
    (V.vec_to_array s.handshake.keys.server_handshake_traffic.traffic_secret)
    transcript_hash
    verify_data;
  V.to_vec_pts_to s.handshake.keys.server_handshake_traffic.traffic_secret;
  with verify_data_bytes. assert (pts_to verify_data verify_data_bytes);
  assert (pure (verify_data_bytes ==
    K.finished_verify_data
      sh_secret
      (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  fold (CR.traffic_key_material_exactly
    s.handshake.keys.server_handshake_traffic
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (CR.key_schedule_exactly
    s.handshake.keys
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  let fin = Ghost.hide ((verify_data_bytes) <: GFin.finished);
  let fin_vec = V.alloc 0uy 32sz;
  CR.copy_fixed32_array_to_vec verify_data fin_vec;
  let lfin = { IM.finished_verify_data = fin_vec };
  assert (pure (lfin.IM.finished_verify_data == fin_vec));
  with fin_vec_bytes. assert (V.pts_to fin_vec fin_vec_bytes);
  assert (pure (fin_vec_bytes == verify_data_bytes));
  rewrite (V.pts_to fin_vec fin_vec_bytes)
    as (V.pts_to lfin.IM.finished_verify_data fin_vec_bytes);
  assert (pure (B.length verify_data_bytes == 32));
  assert (pure (Seq.equal fin_vec_bytes (Sem.finished_verify_data (Ghost.reveal fin))));
  fold (IM.is_valid_finished lfin (Ghost.reveal fin));

  let mut fragment = [| 0uy; 36sz |];
  let written_fragment =
    Ser.serialize_server_finished
      #fin
      lfin
      fragment
      36sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 36));
  assert (pure (SZ.v written_fragment == 36));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  lemma_server_handshake_write_seal_some
    'st0
    (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.Finished (Ghost.reveal fin)));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.Finished (Ghost.reveal fin))
      s.records.write
      fragment
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length network_out_bytes == 58));
  assert (pure (SZ.v written_raw == 58));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.Application_data 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
    network_out_bytes));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty;
  assert (pure (TLS13.Spec.StateMachine.Replay.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty));
  assert (pure (TLS13.Spec.StateMachine.Log.connection_state_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.model_record_keys_consistent_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_write_key_schedule_projection_for_role
    CS.ServerEndpoint
    'st0.CS.cs_model));
  assert (pure (H.verify_finished
    sh_secret
    (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    (Ghost.reveal fin)));
  assert (pure (CM.can_send_server_finished
    'st0
    (Ghost.reveal fin)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_server_finished
    s
    network_out
    fragment
    written_fragment
    lfin
    #fin;
  fold (connection_exactly
    s
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes));

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_server_finished_state_evolves
    'st0
    (Ghost.reveal fin)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (Ghost.reveal ev == CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
  }));
  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert_norm (ST.local_event_kind_matches
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    }));
  assert (pure (ST.local_payload_matches_app_sent_delta
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })));
  assert (pure (ST.local_event_supported_profile
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })));
  assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes));
  assert (pure (resp.status == ST.StepOk));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    ST.LocalSendServerFinished
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    ST.LocalSendServerFinished
    B.empty
    network_out_bytes
    'old_app_out));
  resp
}
