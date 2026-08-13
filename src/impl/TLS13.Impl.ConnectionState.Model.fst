module TLS13.Impl.ConnectionState.Model

#lang-pulse

open Pulse.Lib.Pervasives
open FStar.List.Tot

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module SM = TLS13.Spec.StateMachine.ClientTrace
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec
module GA = TLS13.Wire.Generated.Alert
module GAL = TLS13.Wire.Generated.AlertLevel
module GAD = TLS13.Wire.Generated.AlertDescription
module LP = LowParse.Spec

// Phase 5: handshake_msg payloads are the QuackyDucky-generated wire records.
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
// Generated component modules used to build the canonical wire ClientHello
// returned by client_hello_of_start.
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCS = TLS13.Wire.Generated.CipherSuite
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSS = TLS13.Wire.Generated.SignatureScheme
module GCHE = TLS13.Wire.Generated.ClientHello_extensions
// For the ClientHello record-size bound in client_hello_matches_start: reveal
// serialize_handshake to the generated handshake serializer and compute the
// bytesize of the canonical 5-extension ClientHello.
module GHS = TLS13.Wire.Generated.Handshake
module GNG = TLS13.Wire.Generated.NamedGroup
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module Rev = TLS13.Wire.Spec.Reveal.Handshake

open TLS13.Impl.ConnectionState.Bounds

let lemma_sizet_lte_plain (x:SZ.t) (y:SZ.t)
  : Lemma (sizet_lte_plain x y == (SZ.v x <= SZ.v y))
=
  ()

let lemma_seal_some_of_keys
  (s:R.direction_state)
  (aad:B.bytes)
  (pt:M.plaintext)
  : Lemma
      (requires (match s.R.key, s.R.static_iv with
                 | Some _, Some _ -> True
                 | _, _ -> False))
      (ensures Some? (R.seal s aad pt))
=
  match s.R.key, s.R.static_iv with
  | Some _, Some _ -> ()
  | _, _ -> ()

let lemma_bounded_u16_sizet_of_sizet
  (n:nat)
  (z:SZ.t)
  : Lemma
      (requires n == SZ.v z /\ n < 65536)
      (ensures bounded_u16_sizet n == z)
=
  SZ.size_v_inj z

let rec lemma_cipher_suites_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites)
      (ensures len == length suites)
      (decreases len)
=
  if len == 0 then
    ()
  else if len <= Seq.length wire then
    match suites with
    | suite :: rest ->
      lemma_cipher_suites_match_length
        (Seq.slice wire 1 (Seq.length wire))
        (len - 1)
        rest
    | [] -> ()
  else
    ()

let rec lemma_signature_schemes_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes)
      (ensures len == length schemes)
      (decreases len)
=
  if len == 0 then
    ()
  else if len <= Seq.length wire then
    match schemes with
    | scheme :: rest ->
      lemma_signature_schemes_match_length
        (Seq.slice wire 1 (Seq.length wire))
        (len - 1)
        rest
    | [] -> ()
  else
    ()

let lemma_signature_schemes_match_first_rsa_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes /\
                0 < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire 0) == 0x0804)
      (ensures CS.signature_scheme_offered schemes T.Rsa_pss_rsae_sha256)
=
  match schemes with
  | scheme :: _ ->
    assert (IM.signature_scheme_matches (Seq.index wire 0) scheme);
    (match scheme with
    | T.Rsa_pss_rsae_sha256 -> ()
    | T.Ecdsa_secp256r1_sha256 -> assert False
    | T.Ed25519 -> assert False
    | T.Unknown_signatureScheme _ -> assert False)
  | [] ->
    lemma_signature_schemes_match_length wire len schemes;
    assert False

let lemma_cipher_suites_match_first_chacha_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                0 < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire 0) == 0x1303)
      (ensures CS.cipher_suite_offered suites T.TLS_CHACHA20_POLY1305_SHA256)
=
  match suites with
  | suite :: _ ->
    assert (IM.cipher_suite_matches (Seq.index wire 0) suite);
    (match suite with
    | T.TLS_CHACHA20_POLY1305_SHA256 -> ()
    | T.Unknown_cipherSuite _ -> assert False)
  | [] ->
    lemma_cipher_suites_match_length wire len suites;
    assert False

let rec lemma_signature_schemes_match_index_rsa_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  (i:nat)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes /\
                i < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire i) == 0x0804)
      (ensures CS.signature_scheme_offered schemes T.Rsa_pss_rsae_sha256)
      (decreases i)
=
  if i = 0
  then lemma_signature_schemes_match_first_rsa_offer wire len schemes
  else
    match schemes with
    | scheme :: rest ->
      let wire' = Seq.slice wire 1 (Seq.length wire) in
      assert (Seq.index wire' (i - 1) == Seq.index wire i);
      lemma_signature_schemes_match_index_rsa_offer wire' (len - 1) rest (i - 1)
    | [] ->
      lemma_signature_schemes_match_length wire len schemes;
      assert False

let rec lemma_cipher_suites_match_index_chacha_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  (i:nat)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                i < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire i) == 0x1303)
      (ensures CS.cipher_suite_offered suites T.TLS_CHACHA20_POLY1305_SHA256)
      (decreases i)
=
  if i = 0
  then lemma_cipher_suites_match_first_chacha_offer wire len suites
  else
    match suites with
    | suite :: rest ->
      let wire' = Seq.slice wire 1 (Seq.length wire) in
      assert (Seq.index wire' (i - 1) == Seq.index wire i);
      lemma_cipher_suites_match_index_chacha_offer wire' (len - 1) rest (i - 1)
    | [] ->
      lemma_cipher_suites_match_length wire len suites;
      assert False

let lemma_cipher_suites_match_first_aes_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                0 < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire 0) == 0x1301)
      (ensures CS.cipher_suite_offered suites T.TLS_AES_128_GCM_SHA256)
=
  match suites with
  | suite :: _ ->
    assert (IM.cipher_suite_matches (Seq.index wire 0) suite);
    (match suite with
    | T.TLS_AES_128_GCM_SHA256 -> ()
    | T.Unknown_cipherSuite _ -> assert False)
  | [] ->
    lemma_cipher_suites_match_length wire len suites;
    assert False

let rec lemma_cipher_suites_match_index_aes_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  (i:nat)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                i < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire i) == 0x1301)
      (ensures CS.cipher_suite_offered suites T.TLS_AES_128_GCM_SHA256)
      (decreases i)
=
  if i = 0
  then lemma_cipher_suites_match_first_aes_offer wire len suites
  else
    match suites with
    | suite :: rest ->
      let wire' = Seq.slice wire 1 (Seq.length wire) in
      assert (Seq.index wire' (i - 1) == Seq.index wire i);
      lemma_cipher_suites_match_index_aes_offer wire' (len - 1) rest (i - 1)
    | [] ->
      lemma_cipher_suites_match_length wire len suites;
      assert False

let lemma_signature_schemes_match_exists_rsa_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes /\
                len <= Seq.length wire /\
                (exists (i:nat). i < len /\ U16.v (Seq.index wire i) == 0x0804))
      (ensures CS.signature_scheme_offered schemes T.Rsa_pss_rsae_sha256)
=
  let aux (i:nat)
    : Lemma
        (requires i < len /\ U16.v (Seq.index wire i) == 0x0804)
        (ensures CS.signature_scheme_offered schemes T.Rsa_pss_rsae_sha256)
    = lemma_signature_schemes_match_index_rsa_offer wire len schemes i
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let rec lemma_cipher_suites_match_absent_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  (target:U16.t)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                len <= Seq.length wire /\
                (forall (i:nat). i < len ==> Seq.index wire i <> target))
      (ensures ~(CS.cipher_suite_offered suites (IM.cipher_suite_of_u16 target)))
      (decreases len)
=
  if len = 0 then ()
  else
    match suites with
    | suite :: rest ->
      // head: the wire code at 0 is not [target], and [cipher_suite_of_u16] is
      // injective on wire codes, so the head suite is not the named one.
      IM.lemma_cipher_suite_of_u16_matches (Seq.index wire 0) suite;
      let wire' = Seq.slice wire 1 (Seq.length wire) in
      assert (forall (i:nat). i < len - 1 ==> Seq.index wire' i == Seq.index wire (i + 1));
      lemma_cipher_suites_match_absent_offer wire' (len - 1) rest target
    | [] ->
      lemma_cipher_suites_match_length wire len suites

let lemma_cipher_suites_match_exists_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  (target:U16.t)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                len <= Seq.length wire /\
                (target == 0x1303us \/ target == 0x1301us) /\
                (exists (i:nat). i < len /\ Seq.index wire i == target))
      (ensures CS.cipher_suite_offered suites (IM.cipher_suite_of_u16 target))
=
  IM.lemma_cipher_suite_of_u16_chacha ();
  IM.lemma_cipher_suite_of_u16_aes ();
  let aux (i:nat)
    : Lemma
        (requires i < len /\ Seq.index wire i == target)
        (ensures CS.cipher_suite_offered suites (IM.cipher_suite_of_u16 target))
    = if target = 0x1303us
      then begin
        assert_norm (U16.v 0x1303us == 0x1303);
        lemma_cipher_suites_match_index_chacha_offer wire len suites i
      end
      else begin
        assert_norm (U16.v 0x1301us == 0x1301);
        lemma_cipher_suites_match_index_aes_offer wire len suites i
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_cipher_suites_match_exists_chacha_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                len <= Seq.length wire /\
                (exists (i:nat). i < len /\ U16.v (Seq.index wire i) == 0x1303))
      (ensures CS.cipher_suite_offered suites T.TLS_CHACHA20_POLY1305_SHA256)
=
  let aux (i:nat)
    : Lemma
        (requires i < len /\ U16.v (Seq.index wire i) == 0x1303)
        (ensures CS.cipher_suite_offered suites T.TLS_CHACHA20_POLY1305_SHA256)
    = lemma_cipher_suites_match_index_chacha_offer wire len suites i
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// Phase 5: client_hello_of_start is now a faithful, total transparent `let` in
// TLS13.Impl.ConnectionState.Model.fsti (it builds the canonical 5-extension
// ClientHello, clamping invalid/unbounded start fields).  Nothing to define here.

// Under valid_start the clamps in client_hello_of_start are identities, so every
// TLS13.Wire.Semantics accessor returns the matching `start` field.  Discharged
// by unfolding client_hello_of_start and the accessors (fuel for the extension
// list walks).
#push-options "--fuel 8 --ifuel 8 --z3rlimit 400"
let rec lemma_cipher_suite_offered_b (suites:list T.cipher_suite) (suite:T.cipher_suite)
  : Lemma (cipher_suite_offered_b suites suite <==> CS.cipher_suite_offered suites suite)
          [SMTPat (cipher_suite_offered_b suites suite)]
  = match suites with
    | [] -> ()
    | _ :: rest -> lemma_cipher_suite_offered_b rest suite

let lemma_server_selected_suite_supported (st:CS.connection_state)
  : Lemma (H.is_supported_cipher_suite (server_selected_suite st))
  = ()

let lemma_client_hello_of_start_matches
  (start:CS.handshake_start)
  : Lemma (requires valid_start start)
          (ensures CS.client_hello_matches_start start (client_hello_of_start start))
=
  // The 5 semantic-accessor conjuncts are discharged by unfolding
  // client_hello_of_start and the TLS13.Wire.Semantics accessors (fuel).
  // The remaining conjunct is the record-size bound
  //   B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640.
  // Reveal serialize_handshake to the generated serializer and compute the
  // exact bytesize of the canonical 5-extension ClientHello: it equals
  //   220 + |sni| + 2*|cipher_suites| + 2*|signature_schemes|
  // which under valid_start is at most 220 + 255 + 32 + 32 = 539 <= 16640.
  let sni = cho_sni start in
  let sa = cho_sa_data (cho_sa_list start) in
  let ks = start.CS.start_client_key_share_public in
  let pks = start.CS.start_client_p256_public in
  let sn_ext = cho_sn_ext sni in
  let sg_ext = cho_sg_ext in
  let sa_ext = cho_sa_ext sa in
  let ks_ext = cho_ks_ext ks pks in
  let sv_ext = cho_sv_ext in
  let ch = client_hello_of_start start in
  Rev.lemma_serialize_handshake_client_hello ch;
  GHS.handshake_bytesize_eq (GHS.Body_client_hello (ch <: GHS.handshake_body_client_hello));
  GCH.clientHello_extensions_list_bytesize_nil;
  GCH.clientHello_extensions_list_bytesize_cons sv_ext [];
  GCH.clientHello_extensions_list_bytesize_cons ks_ext [sv_ext];
  GCH.clientHello_extensions_list_bytesize_cons sa_ext [ks_ext; sv_ext];
  GCH.clientHello_extensions_list_bytesize_cons sg_ext [sa_ext; ks_ext; sv_ext];
  GCH.clientHello_extensions_list_bytesize_cons sn_ext [sg_ext; sa_ext; ks_ext; sv_ext];
  ()
#pop-options

// Server mirror of the client record-size reasoning inside
// lemma_client_hello_of_start_matches: reveal serialize_handshake to the
// generated serializer and compute the exact bytesize of the canonical
// ServerHello.  It equals 90 + |session_id| (legacy_version TLS_1p2 + 32-byte
// random + 1-byte session-id-echo length + the echo + cipher suite + null
// compression + [key_share(X25519, 32 bytes); supported_versions(TLS_1p3)]),
// i.e. 122 for a middlebox-compatibility-mode peer and 90 for one with
// compatibility mode off.  Structurally identical to
// TLS13.Impl.Server.Send.lemma_mk_server_hello_witness_bytesize.
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let lemma_server_hello_of_selection_bytesize
  (sel:CS.server_handshake_selection)
  : Lemma (requires valid_selection sel)
          (ensures
            B.length (W.serialize_handshake
              (M.ServerHello (server_hello_of_selection sel))) ==
            90 + Seq.length (sho_session_id sel))
= let sh = server_hello_of_selection sel in
  Rev.lemma_serialize_handshake_server_hello sh;
  GHS.handshake_bytesize_eq (GHS.Body_server_hello sh);
  GPV.protocolVersion_bytesize_eq GPV.TLS_1p2;
  GPV.protocolVersion_bytesize_eq GPV.TLS_1p3;
  GCS.cipherSuite_bytesize_eq (sho_cipher_suite sel);
  GNG.namedGroup_bytesize_eq GNG.X25519;
  GKSE.keyShareEntry_key_exchange_bytesize_eqn
    (sel.CS.server_key_share_public <: GKSE.keyShareEntry_key_exchange);
  GSHBody.serverHelloBody_legacy_session_id_echo_bytesize_eqn (sho_session_id sel);
  GSHBody.serverHelloBody_extensions_list_bytesize_nil;
  ()
#pop-options

// Server mirror of lemma_client_hello_of_start_matches.  Under valid_selection
// the clamp (sho_random) is an identity, so every TLS13.Wire.Semantics accessor
// on the canonical server_hello_of_selection returns the matching `selection`
// field.  Discharged (like the reference lemma_canonical_* in
// TLS13.Impl.Serializer.Handshake) by unfolding server_hello_of_selection and
// the accessors (fuel for the 2-extension list walk).  The ServerHello
// wire-profile bound (serialized handshake <= 16640) in
// server_hello_matches_selection is discharged from the exact bytesize
// (90 + |session_id|, at most 122).
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_server_hello_of_selection_matches
  (sel:CS.server_handshake_selection)
  : Lemma (requires valid_selection sel)
          (ensures CS.server_hello_matches_selection sel (server_hello_of_selection sel))
= lemma_server_hello_of_selection_bytesize sel
#pop-options

// Faithful len-helper bridge (see .fsti).  Off the LocalHandshake hot path.
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let lemma_client_hello_len_helpers_from_start
  (start:CS.handshake_start)
  (ch:GCH.clientHello)
  (server_name_storage:B.bytes)
  (server_name_len:SZ.t)
  (cipher_suites:Seq.seq U16.t)
  (cipher_suites_len:SZ.t)
  (signature_schemes:Seq.seq U16.t)
  (signature_schemes_len:SZ.t)
  : Lemma
      (requires valid_start start /\
                ch == client_hello_of_start start /\
                B.length server_name_storage == max_hostname_len /\
                B.length start.CS.start_server_name == SZ.v server_name_len /\
                SZ.v server_name_len <= B.length server_name_storage /\
                Seq.length cipher_suites == max_cipher_suites /\
                SZ.v cipher_suites_len <= Seq.length cipher_suites /\
                IM.cipher_suites_match
                  cipher_suites
                  (SZ.v cipher_suites_len)
                  start.CS.start_cipher_suites /\
                Seq.length signature_schemes == max_signature_schemes /\
                SZ.v signature_schemes_len <= Seq.length signature_schemes /\
                IM.signature_schemes_match
                  signature_schemes
                  (SZ.v signature_schemes_len)
                  start.CS.start_signature_schemes)
      (ensures
        client_hello_server_name_len_for ch == server_name_len /\
        client_hello_cipher_suites_len_for ch == cipher_suites_len /\
        client_hello_signature_schemes_len_for ch == signature_schemes_len)
=
  lemma_client_hello_of_start_matches start;
  lemma_cipher_suites_match_length cipher_suites (SZ.v cipher_suites_len) start.CS.start_cipher_suites;
  lemma_signature_schemes_match_length signature_schemes (SZ.v signature_schemes_len) start.CS.start_signature_schemes;
  lemma_bounded_u16_sizet_of_sizet (B.length start.CS.start_server_name) server_name_len;
  lemma_bounded_u16_sizet_of_sizet (length start.CS.start_cipher_suites) cipher_suites_len;
  lemma_bounded_u16_sizet_of_sizet (length start.CS.start_signature_schemes) signature_schemes_len
#pop-options

let lemma_application_data_record_count_small
  (bytes:B.bytes)
  : Lemma
      (requires B.length bytes <= SM.max_application_data_fragment_len)
      (ensures SM.application_data_record_count bytes == 1)
=
  SM.lemma_application_data_record_count_len_small (B.length bytes)

let lemma_advance_direction_records_one (s:R.direction_state)
  : Lemma (CS.advance_direction_records s 1 == R.next_seq s)
=
  ()

let lemma_seal_application_success_next_seq
  (s:R.direction_state)
  (aad:B.bytes)
  (payload:B.bytes)
  (ciphertext:B.bytes)
  (s':R.direction_state)
  : Lemma
      (requires R.seal
                  s
                  aad
                  { R.content_type = T.Application_data;
                    R.fragment = payload } == Some (ciphertext, s'))
      (ensures s' == R.next_seq s)
=
  match s.R.key, s.R.static_iv with
  | Some _, Some _ -> ()
  | _, _ -> ()

noextract
let close_notify_alert_fragment () : GTot B.bytes =
  LP.serialize GA.alert_serializer {
    GA.level = GAL.Fatal;
    GA.description = GAD.Close_notify;
  }

let lemma_close_notify_alert_fragment_generated ()
  : Lemma (
      close_notify_alert_fragment () ==
      LP.serialize GA.alert_serializer {
        GA.level = GAL.Fatal;
        GA.description = GAD.Close_notify;
      })
  = ()

let lemma_local_fail_state_evolves (st:CS.connection_state) (err:T.tls_error)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (local_fail_state st err) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent (local_fail_state st err) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event = CS.ConnLocalEvent (CS.LocalFail err);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (local_fail_state st err))
=
  let delta = {
    CS.delta_event = CS.ConnLocalEvent (CS.LocalFail err);
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_connection_delta st delta (local_fail_state st err));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (local_fail_state st err));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (local_fail_state st err);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (local_fail_state st err));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (local_fail_state st err))

let lemma_started_handshake_state_evolves
  (st:CS.connection_state)
  (start:CS.handshake_start)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_start_handshake st start)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (started_handshake_state st start) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (started_handshake_state st start) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalStartHandshake start);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (started_handshake_state st start))
=
  let ev = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (started_handshake_state st start).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (started_handshake_state st start));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (started_handshake_state st start));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (started_handshake_state st start);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (started_handshake_state st start));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (started_handshake_state st start))

let lemma_started_server_state_evolves
  (st:CS.connection_state)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_start_server st)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (started_server_state st) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (started_server_state st) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event = CS.ConnLocalEvent CS.LocalStartServer;
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (started_server_state st))
=
  let ev = CS.ConnLocalEvent CS.LocalStartServer in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (started_server_state st).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (started_server_state st));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (started_server_state st));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (started_server_state st);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (started_server_state st));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (started_server_state st))

let lemma_selected_server_parameters_state_evolves
  (st:CS.connection_state)
  (selection:CS.server_handshake_selection)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_select_server_parameters st selection)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (selected_server_parameters_state st selection) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (selected_server_parameters_state st selection) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalSelectServerParameters selection);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (selected_server_parameters_state st selection))
=
  let ev = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (selected_server_parameters_state st selection).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (selected_server_parameters_state st selection));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (selected_server_parameters_state st selection));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (selected_server_parameters_state st selection);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (selected_server_parameters_state st selection));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (selected_server_parameters_state st selection))

let lemma_sent_client_hello_state_evolves
  (st:CS.connection_state)
  (ch:GCH.clientHello)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_client_hello st ch raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_client_hello_state st ch raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_client_hello_state st ch raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_client_hello_state st ch raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_client_hello_state st ch raw_sent).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.legal_connection_delta st delta (sent_client_hello_state st ch raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (sent_client_hello_state st ch raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_client_hello_state st ch raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (sent_client_hello_state st ch raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (sent_client_hello_state st ch raw_sent))

let lemma_derived_shared_secret_state_evolves
  (st:CS.connection_state)
  (shared:TLS13.Crypto.Spec.x25519_shared_secret)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)))
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (derived_shared_secret_state st shared) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (derived_shared_secret_state st shared) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (derived_shared_secret_state st shared))
=
  let ev = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (derived_shared_secret_state st shared).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (derived_shared_secret_state st shared));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (derived_shared_secret_state st shared));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (derived_shared_secret_state st shared);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (derived_shared_secret_state st shared));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (derived_shared_secret_state st shared))

let lemma_installed_traffic_keys_state_evolves
  (st:CS.connection_state)
  (install:CS.traffic_key_install)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (installed_traffic_keys_state st install) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (installed_traffic_keys_state st install) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st install))
=
  let ev = CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (installed_traffic_keys_state st install).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (installed_traffic_keys_state st install));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (installed_traffic_keys_state st install));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (installed_traffic_keys_state st install);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (installed_traffic_keys_state st install));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (installed_traffic_keys_state st install))

let lemma_installed_traffic_keys_for_role_state_evolves
  (st:CS.connection_state)
  (role_install:CS.role_traffic_key_install)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole role_install)))
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (installed_traffic_keys_for_role_state st role_install) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (installed_traffic_keys_for_role_state st role_install) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeysForRole role_install);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_for_role_state st role_install))
=
  let ev =
    CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole role_install) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (installed_traffic_keys_for_role_state st role_install).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (installed_traffic_keys_for_role_state st role_install));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (installed_traffic_keys_for_role_state st role_install));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (installed_traffic_keys_for_role_state st role_install);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (installed_traffic_keys_for_role_state st role_install));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (installed_traffic_keys_for_role_state st role_install))

let lemma_validated_certificate_state_evolves
  (st:CS.connection_state)
  (peer:X.peer_identity)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)))
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (validated_certificate_state st peer) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (validated_certificate_state st peer) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (validated_certificate_state st peer))
=
  let ev = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (validated_certificate_state st peer).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (validated_certificate_state st peer));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (validated_certificate_state st peer));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (validated_certificate_state st peer);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (validated_certificate_state st peer));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (validated_certificate_state st peer))

let lemma_client_handshake_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (CS.negotiated_aead_alg model.CS.model_handshake)
                (K.client_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_handshake_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (CS.negotiated_aead_alg model.CS.model_handshake)
                (K.server_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_role_server_handshake_write_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloSent /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (CS.negotiated_aead_alg model.CS.model_handshake)
                  (K.server_handshake_traffic_secret
                    handshake_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_server_role_client_handshake_read_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloSent /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (CS.negotiated_aead_alg model.CS.model_handshake)
                  (K.client_handshake_traffic_secret
                    handshake_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_client_application_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedVerified /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (CS.negotiated_aead_alg model.CS.model_handshake)
                (K.client_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_application_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedVerified /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (CS.negotiated_aead_alg model.CS.model_handshake)
                (K.server_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_role_server_application_write_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedSent /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (CS.negotiated_aead_alg model.CS.model_handshake)
                  (K.server_application_traffic_secret
                    master_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_server_role_client_application_read_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientFinishedReceived /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (CS.negotiated_aead_alg model.CS.model_handshake)
                  (K.client_application_traffic_secret
                    master_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_received_hello_retry_request_rejected_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientHelloSent /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_hello_retry_request_rejected_state st raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_hello_retry_request_rejected_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_hello_retry_request_rejected_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake M.HelloRetryRequest;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (CS.fail_model st.CS.cs_model tls_hello_retry_request_rejected_error));
  assert (CS.legal_connection_delta
    st
    delta
    (received_hello_retry_request_rejected_state st raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_hello_retry_request_rejected_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_hello_retry_request_rejected_state st raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_hello_retry_request_rejected_state st raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_hello_retry_request_rejected_state st raw_received))

let lemma_received_change_cipher_spec_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                (exists stage.
                  st.CS.cs_model.CS.model_control == CS.ControlHandshaking stage) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsChangeCipherSpec;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_change_cipher_spec_state st raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_change_cipher_spec_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsChangeCipherSpec;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_change_cipher_spec_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsChangeCipherSpec;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev == Some st.CS.cs_model);
  assert (CS.legal_connection_delta st delta (received_change_cipher_spec_state st raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (received_change_cipher_spec_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_change_cipher_spec_state st raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (received_change_cipher_spec_state st raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (received_change_cipher_spec_state st raw_received))

let lemma_received_server_hello_state_evolves
  (st:CS.connection_state)
  (sh:GSH.serverHello)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientHelloSent /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  }) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_server_hello_state st sh raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_server_hello_state st sh raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_server_hello_state st sh raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_server_hello_state st sh raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_server_hello_state st sh raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_server_hello_state st sh raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_server_hello_state st sh raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_server_hello_state st sh raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_server_hello_state st sh raw_received))

let lemma_sent_server_hello_state_evolves
  (st:CS.connection_state)
  (sh:GSH.serverHello)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_server_hello st sh raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_server_hello_state st sh raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_server_hello_state st sh raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_server_hello_state st sh raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_server_hello_state st sh raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_server_hello_state st sh raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_server_hello_state st sh raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_server_hello_state st sh raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (sent_server_hello_state st sh raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (sent_server_hello_state st sh raw_sent))

let lemma_sent_encrypted_extensions_state_evolves
  (st:CS.connection_state)
  (ee:GEE.encryptedExtensions)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_encrypted_extensions st ee raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_encrypted_extensions_state st ee raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_encrypted_extensions_state st ee raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_encrypted_extensions_state st ee raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_encrypted_extensions_state st ee raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_encrypted_extensions_state st ee raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_encrypted_extensions_state st ee raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_encrypted_extensions_state st ee raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (sent_encrypted_extensions_state st ee raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (sent_encrypted_extensions_state st ee raw_sent))

let lemma_sent_certificate_state_evolves
  (st:CS.connection_state)
  (cert:GCert.certificate)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_certificate st cert raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_certificate_state st cert raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_certificate_state st cert raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.Certificate cert);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_certificate_state st cert raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_certificate_state st cert raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_certificate_state st cert raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_certificate_state st cert raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_certificate_state st cert raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (sent_certificate_state st cert raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (sent_certificate_state st cert raw_sent))

let lemma_signed_certificate_verify_state_evolves
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_sign_certificate_verify st cv)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (signed_certificate_verify_state st cv) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (signed_certificate_verify_state st cv) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (signed_certificate_verify_state st cv))
=
  let ev = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (signed_certificate_verify_state st cv).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (signed_certificate_verify_state st cv));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (signed_certificate_verify_state st cv));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (signed_certificate_verify_state st cv);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (signed_certificate_verify_state st cv));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (signed_certificate_verify_state st cv))

let lemma_sent_certificate_verify_state_evolves
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_certificate_verify st cv raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_certificate_verify_state st cv raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_certificate_verify_state st cv raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_certificate_verify_state st cv raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_certificate_verify_state st cv raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_certificate_verify_state st cv raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_certificate_verify_state st cv raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_certificate_verify_state st cv raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (sent_certificate_verify_state st cv raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (sent_certificate_verify_state st cv raw_sent))

let lemma_sent_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_server_finished st fin raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_server_finished_state st fin raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_server_finished_state st fin raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_server_finished_state st fin raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_server_finished_state st fin raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_server_finished_state st fin raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_server_finished_state st fin raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_server_finished_state st fin raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (sent_server_finished_state st fin raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (sent_server_finished_state st fin raw_sent))

let lemma_received_client_finished_state_evolves
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_receive_client_finished st fin raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_client_finished_state st fin raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_client_finished_state st fin raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_client_finished_state st fin raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty raw_received);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_client_finished_state st fin raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_client_finished_state st fin raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_client_finished_state st fin raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_client_finished_state st fin raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_client_finished_state st fin raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_client_finished_state st fin raw_received))

let lemma_verified_client_finished_state_evolves
  (st:CS.connection_state)
  (fin:GFin.finished)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_verify_client_finished st fin)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (verified_client_finished_state st fin) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (verified_client_finished_state st fin) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_client_finished_state st fin))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_client_finished_state st fin).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (verified_client_finished_state st fin));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (verified_client_finished_state st fin));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (verified_client_finished_state st fin);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (verified_client_finished_state st fin));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (verified_client_finished_state st fin))

let lemma_received_client_hello_state_evolves
  (st:CS.connection_state)
  (ch:GCH.clientHello)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsAwaitingClientHello /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_client_hello_state st ch raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_client_hello_state st ch raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_client_hello_state st ch raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_client_hello_state st ch raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_client_hello_state st ch raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_client_hello_state st ch raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_client_hello_state st ch raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_client_hello_state st ch raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_client_hello_state st ch raw_received))

let lemma_received_encrypted_extensions_state_evolves
  (st:CS.connection_state)
  (ee:GEE.encryptedExtensions)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_encrypted_extensions_state st ee raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_encrypted_extensions_state st ee raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_encrypted_extensions_state st ee raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_encrypted_extensions_state st ee raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_encrypted_extensions_state st ee raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_encrypted_extensions_state st ee raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_encrypted_extensions_state st ee raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_encrypted_extensions_state st ee raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_encrypted_extensions_state st ee raw_received))

let lemma_received_certificate_state_evolves
  (st:CS.connection_state)
  (cert:GCert.certificate)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                (Sem.certificate_entries cert) <> [] /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Certificate cert);
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_certificate_state st cert raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_certificate_state st cert raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Certificate cert);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_certificate_state st cert raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_certificate_state st cert raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_certificate_state st cert raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_certificate_state st cert raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_certificate_state st cert raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_certificate_state st cert raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_certificate_state st cert raw_received))

let lemma_received_certificate_verify_state_evolves
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateValidated /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_certificate_verify_state st cv raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_certificate_verify_state st cv raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_certificate_verify_state st cv raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_certificate_verify_state st cv raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_certificate_verify_state st cv raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_certificate_verify_state st cv raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_certificate_verify_state st cv raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_certificate_verify_state st cv raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_certificate_verify_state st cv raw_received))

let lemma_verified_certificate_signature_state_evolves
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
                st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)))
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (verified_certificate_signature_state st cv) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (verified_certificate_signature_state st cv) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_certificate_signature_state st cv))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_certificate_signature_state st cv).CS.cs_model);
  assert (CS.legal_connection_delta st delta (verified_certificate_signature_state st cv));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (verified_certificate_signature_state st cv));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (verified_certificate_signature_state st cv);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (verified_certificate_signature_state st cv));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (verified_certificate_signature_state st cv))

let lemma_received_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
      CS.event_raw_delta_legal
        st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Finished fin);
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_server_finished_state st fin raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_server_finished_state st fin raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_server_finished_state st fin raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_server_finished_state st fin raw_received).CS.cs_model);
  assert (CS.legal_connection_delta st delta (received_server_finished_state st fin raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (received_server_finished_state st fin raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_server_finished_state st fin raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (received_server_finished_state st fin raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (received_server_finished_state st fin raw_received))

let lemma_protected_handshake_state_evolves
  (st:CS.connection_state)
  (step:CS.protected_handshake_step)
  (raw_received:B.bytes)
  : Lemma
      (requires
        TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
        CS.legal_event st.CS.cs_model (CS.ConnProtectedHandshake step) /\
        Some? (CS.step_protected_handshake st.CS.cs_model step) /\
        CS.event_raw_delta_legal
          st.CS.cs_model
          (CS.ConnProtectedHandshake step)
          B.empty
          raw_received)
      (ensures
        TLS13.Spec.StateMachine.Reachability.connection_state_evolves
          st
          (protected_handshake_state st step raw_received) /\
        TLS13.Spec.StateMachine.Reachability.connection_state_consistent
          (protected_handshake_state st step raw_received) /\
        CS.legal_connection_delta
          st
          {
            CS.delta_event = CS.ConnProtectedHandshake step;
            CS.delta_raw_sent = B.empty;
            CS.delta_raw_received = raw_received;
          }
          (protected_handshake_state st step raw_received))
=
  let ev = CS.ConnProtectedHandshake step in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  match CS.step_protected_handshake st.CS.cs_model step with
  | None -> assert False
  | Some model1 ->
    assert (CS.step_model st.CS.cs_model ev ==
      Some (protected_handshake_state st step raw_received).CS.cs_model);
    assert (CS.legal_connection_delta
      st
      delta
      (protected_handshake_state st step raw_received));
    assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
      st
      (protected_handshake_state st step raw_received));
    FStar.ReflexiveTransitiveClosure.closure_step
      TLS13.Spec.StateMachine.Reachability.connection_state_single_step
      st
      (protected_handshake_state st step raw_received);
    assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
      st
      (protected_handshake_state st step raw_received));
    assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
      (protected_handshake_state st step raw_received))

let lemma_verified_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:GFin.finished)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedReceived /\
                st.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some fin /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalVerifyFinished fin)))
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (verified_server_finished_state st fin) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (verified_server_finished_state st fin) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyFinished fin);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_server_finished_state st fin))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyFinished fin) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_server_finished_state st fin).CS.cs_model);
  assert (CS.legal_connection_delta st delta (verified_server_finished_state st fin));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (verified_server_finished_state st fin));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (verified_server_finished_state st fin);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (verified_server_finished_state st fin));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (verified_server_finished_state st fin))

let lemma_sent_client_finished_state_evolves
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_client_finished st fin raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_client_finished_state st fin raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_client_finished_state st fin raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_client_finished_state st fin raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_client_finished_state st fin raw_sent).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.legal_connection_delta st delta (sent_client_finished_state st fin raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (sent_client_finished_state st fin raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_client_finished_state st fin raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (sent_client_finished_state st fin raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (sent_client_finished_state st fin raw_sent))

let lemma_received_alert_failure_state_evolves
  (st:CS.connection_state)
  (alert:T.alert_description)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                alert <> T.Close_notify /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert alert;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_alert_failure_state st alert raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_alert_failure_state st alert raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert alert;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_alert_failure_state st alert raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert alert;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (CS.fail_model st.CS.cs_model (T.AlertError alert)));
  assert (CS.legal_connection_delta st delta (received_alert_failure_state st alert raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (received_alert_failure_state st alert raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_alert_failure_state st alert raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (received_alert_failure_state st alert raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (received_alert_failure_state st alert raw_received))

let lemma_received_close_notify_state_evolves_for_role
  (role:CS.endpoint_role)
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                (st.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  role /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert T.Close_notify;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_close_notify_state st raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_close_notify_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert T.Close_notify;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_close_notify_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert T.Close_notify;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_close_notify_state st raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_close_notify_state st raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_close_notify_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_close_notify_state st raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_close_notify_state st raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_close_notify_state st raw_received))

let lemma_received_close_notify_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                (st.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert T.Close_notify;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_close_notify_state st raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_close_notify_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert T.Close_notify;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_close_notify_state st raw_received))
=
  lemma_received_close_notify_state_evolves_for_role
    CS.ClientEndpoint
    st
    raw_received

let lemma_sent_close_notify_state_evolves
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_close_notify st raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_close_notify_state st raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_close_notify_state st raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsAlert T.Close_notify;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_close_notify_state st raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.Close_notify;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_close_notify_state st raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_close_notify_state st raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_close_notify_state st raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_close_notify_state st raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (sent_close_notify_state st raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (sent_close_notify_state st raw_sent))

let lemma_received_application_data_state_evolves_for_role
  (role:CS.endpoint_role)
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role == role /\
                CS.application_traffic_available_for_role
                  role
                  st.CS.cs_model.CS.model_handshake
                  CL.Received /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsApplicationData bytes;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_application_data_state st bytes raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_application_data_state st bytes raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_application_data_state st bytes raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsApplicationData bytes;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_tls_message st.CS.cs_model CL.Received (M.TlsApplicationData bytes));
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_application_data_state st bytes raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_application_data_state st bytes raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_application_data_state st bytes raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_application_data_state st bytes raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_application_data_state st bytes raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_application_data_state st bytes raw_received))

let lemma_received_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsApplicationData bytes;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_application_data_state st bytes raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_application_data_state st bytes raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_application_data_state st bytes raw_received))
=
  assert_norm (CS.traffic_label_for_endpoint_direction
    CS.ClientEndpoint
    CS.TrafficRead == CS.ServerTraffic);
  assert (CS.application_traffic_available_for_role
    CS.ClientEndpoint
    st.CS.cs_model.CS.model_handshake
    CL.Received);
  lemma_received_application_data_state_evolves_for_role
    CS.ClientEndpoint
    st
    bytes
    raw_received

let lemma_received_ignored_post_handshake_state_evolves
  (st:CS.connection_state)
  (body:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsIgnoredPostHandshake body;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_ignored_post_handshake_state st body raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_ignored_post_handshake_state st body raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsIgnoredPostHandshake body;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_ignored_post_handshake_state st body raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsIgnoredPostHandshake body;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_ignored_post_handshake_state st body raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_ignored_post_handshake_state st body raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_ignored_post_handshake_state st body raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_ignored_post_handshake_state st body raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_ignored_post_handshake_state st body raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_ignored_post_handshake_state st body raw_received))

let lemma_server_received_key_update_state_evolves
  (st:CS.connection_state)
  (req:M.key_update_request)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ServerEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsKeyUpdate req;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (server_received_key_update_state st req raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (server_received_key_update_state st req raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                      CL.message_value = M.TlsKeyUpdate req;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (server_received_key_update_state st req raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsKeyUpdate req;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (server_received_key_update_state st req raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (server_received_key_update_state st req raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (server_received_key_update_state st req raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (server_received_key_update_state st req raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (server_received_key_update_state st req raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (server_received_key_update_state st req raw_received))

let lemma_received_key_update_state_evolves
  (st:CS.connection_state)
  (req:M.key_update_request)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsKeyUpdate req;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_key_update_state st req raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_key_update_state st req raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                      CL.message_value = M.TlsKeyUpdate req;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_key_update_state st req raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsKeyUpdate req;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_key_update_state st req raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_key_update_state st req raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_key_update_state st req raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (received_key_update_state st req raw_received);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (received_key_update_state st req raw_received));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (received_key_update_state st req raw_received))

let lemma_received_key_update_not_requested_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
                  })
                  B.empty
                  raw_received)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (received_key_update_not_requested_state st raw_received) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (received_key_update_not_requested_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_key_update_not_requested_state st raw_received))
=
  lemma_received_key_update_state_evolves st M.UpdateNotRequested raw_received

let lemma_sent_key_update_state_evolves
  (st:CS.connection_state)
  (req:M.key_update_request)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_key_update_gen st req raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_key_update_state st req raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_key_update_state st req raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsKeyUpdate req;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_key_update_state st req raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsKeyUpdate req;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_key_update_state st req raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_key_update_state st req raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_key_update_state st req raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_key_update_state st req raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (sent_key_update_state st req raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (sent_key_update_state st req raw_sent))

let lemma_server_sent_key_update_state_evolves
  (st:CS.connection_state)
  (req:M.key_update_request)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                server_can_send_key_update st req raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (server_sent_key_update_state st req raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (server_sent_key_update_state st req raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsKeyUpdate req;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (server_sent_key_update_state st req raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsKeyUpdate req;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (server_sent_key_update_state st req raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (server_sent_key_update_state st req raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (server_sent_key_update_state st req raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (server_sent_key_update_state st req raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves
    st
    (server_sent_key_update_state st req raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
    (server_sent_key_update_state st req raw_sent))

let lemma_sent_key_update_response_state_evolves
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_key_update st raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_key_update_response_state st raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_key_update_response_state st raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_key_update_response_state st raw_sent))
=
  lemma_sent_key_update_state_evolves st M.UpdateNotRequested raw_sent

let lemma_delivered_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)))
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (delivered_application_data_state st bytes) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (delivered_application_data_state st bytes) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (delivered_application_data_state st bytes))
=
  let ev = CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (delivered_application_data_state st bytes).CS.cs_model);
  assert (CS.legal_connection_delta st delta (delivered_application_data_state st bytes));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (delivered_application_data_state st bytes));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (delivered_application_data_state st bytes);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (delivered_application_data_state st bytes));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (delivered_application_data_state st bytes))

let lemma_sent_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_sent:B.bytes)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
                can_send_application_data st bytes raw_sent)
      (ensures TLS13.Spec.StateMachine.Reachability.connection_state_evolves
                 st
                 (sent_application_data_state st bytes raw_sent) /\
               TLS13.Spec.StateMachine.Reachability.connection_state_consistent
                 (sent_application_data_state st bytes raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_application_data_state st bytes raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  lemma_application_data_record_count_small bytes;
  lemma_advance_direction_records_one st.CS.cs_model.CS.model_record.CS.record_write;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_application_data_state st bytes raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta st delta (sent_application_data_state st bytes raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_single_step st (sent_application_data_state st bytes raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    st
    (sent_application_data_state st bytes raw_sent);
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves st (sent_application_data_state st bytes raw_sent));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_consistent (sent_application_data_state st bytes raw_sent))
