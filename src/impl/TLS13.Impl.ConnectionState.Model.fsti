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

// Phase 5: handshake_msg payloads are now the QuackyDucky-generated wire
// records; profile-relevant fields are read through the TLS13.Wire.Semantics
// accessors instead of the deleted M.<record> projection fields.
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module U8 = FStar.UInt8
module LL = FStar.List.Tot
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GHN = TLS13.Wire.Generated.HostName
module GSN = TLS13.Wire.Generated.ServerName
module GSNL = TLS13.Wire.Generated.ServerNameList
module GNG = TLS13.Wire.Generated.NamedGroup
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GKSCH = TLS13.Wire.Generated.KeyShareClientHello
module GCS = TLS13.Wire.Generated.CipherSuite
module GSS = TLS13.Wire.Generated.SignatureScheme
module GSSL = TLS13.Wire.Generated.SignatureSchemeList
module GECH = TLS13.Wire.Generated.ExtensionClientHello
// Generated component modules used to build the canonical wire ServerHello
// returned by server_hello_of_selection (mirrors
// TLS13.Impl.Serializer.Handshake.poc_canonical_sh).
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GSHB = TLS13.Wire.Generated.ServerHello_body

open TLS13.Impl.ConnectionState.Bounds



let sizet_lte_plain (x:SZ.t) (y:SZ.t) : bool =
  SZ.lte x y

val lemma_sizet_lte_plain (x:SZ.t) (y:SZ.t)
  : Lemma (sizet_lte_plain x y == (SZ.v x <= SZ.v y))

val lemma_seal_some_of_keys
  (s:R.direction_state)
  (aad:B.bytes)
  (pt:M.plaintext)
  : Lemma
      (requires (match s.R.key, s.R.static_iv with
                 | Some _, Some _ -> True
                 | _, _ -> False))
      (ensures Some? (R.seal s aad pt))

noextract
let bounded_u16_sizet (n:nat) : SZ.t =
  if n < 65536 then SZ.uint_to_t n else 0sz

val lemma_bounded_u16_sizet_of_sizet
  (n:nat)
  (z:SZ.t)
  : Lemma
      (requires n == SZ.v z /\ n < 65536)
      (ensures bounded_u16_sizet n == z)

val lemma_cipher_suites_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites)
      (ensures len == length suites)

val lemma_signature_schemes_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes)
      (ensures len == length schemes)

val lemma_signature_schemes_match_first_rsa_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes /\
                0 < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire 0) == 0x0804)
      (ensures CS.signature_scheme_offered schemes T.Rsa_pss_rsae_sha256)

noextract
let client_hello_server_name_len_for (m:GCH.clientHello) : SZ.t =
  match Sem.clientHello_server_name m with
  | Some sn -> bounded_u16_sizet (B.length sn)
  | None -> 0sz

noextract
let client_hello_cipher_suites_len_for (m:GCH.clientHello) : SZ.t =
  bounded_u16_sizet (length (Sem.clientHello_cipher_suites m))

noextract
let client_hello_signature_schemes_len_for (m:GCH.clientHello) : SZ.t =
  match Sem.clientHello_sig_algs m with
  | Some sas -> bounded_u16_sizet (length sas)
  | None -> 0sz

let tls_decode_error : T.tls_error = T.AlertError T.Decode_error

let tls_unexpected_message_error : T.tls_error = T.AlertError T.Unexpected_message

let tls_hello_retry_request_rejected_error : T.tls_error = T.HelloRetryRequestRejected

let tls_bad_finished_error : T.tls_error = T.BadFinished

val lemma_cipher_suites_match_first_chacha_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites /\
                0 < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire 0) == 0x1303)
      (ensures CS.cipher_suite_offered suites T.TLS_CHACHA20_POLY1305_SHA256)

noextract
let local_fail_state (st:CS.connection_state) (err:T.tls_error) : CS.connection_state =
  {
    CS.cs_model = CS.fail_model st.CS.cs_model err;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log = st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalFail err)];
  }

// Phase 5: the handshake-message payload is now the generated GCH.clientHello
// wire record.  client_hello_of_start builds the faithful canonical 5-extension
// ClientHello from a handshake_start, structurally identical to the verified
// reference TLS13.Impl.Serializer.Handshake.poc_canonical_ch.  It is TOTAL,
// so the (unbounded) start blob/lists are CLAMPED to the generated bounds; the
// clamps are identities under `valid_start start` (see
// lemma_client_hello_of_start_matches and the LocalHandshake bridge lemma).

// valid-start predicate: the unbounded start blob/lists fit the generated bounds
let valid_start (start:CS.handshake_start) : prop =
  1 <= Seq.length start.CS.start_server_name /\
  Seq.length start.CS.start_server_name <= 255 /\
  1 <= LL.length start.CS.start_cipher_suites /\
  LL.length start.CS.start_cipher_suites <= 16 /\
  1 <= LL.length start.CS.start_signature_schemes /\
  LL.length start.CS.start_signature_schemes <= 16

// ---- clamps (identity under valid_start) ----
noextract
let cho_sni (start:CS.handshake_start)
  : (r:B.bytes { 1 <= Seq.length r /\ Seq.length r <= 255 })
  = if 1 <= Seq.length start.CS.start_server_name && Seq.length start.CS.start_server_name <= 255
    then start.CS.start_server_name
    else Seq.create 1 0uy

noextract
let cho_cs (start:CS.handshake_start)
  : (cs:GCH.clientHello_cipher_suites { LL.length cs <= 16 })
  = if 1 <= LL.length start.CS.start_cipher_suites && LL.length start.CS.start_cipher_suites <= 16
    then start.CS.start_cipher_suites
    else [GCS.TLS_CHACHA20_POLY1305_SHA256]

noextract
let cho_sa_list (start:CS.handshake_start)
  : (l:list GSS.signatureScheme { 1 <= LL.length l /\ LL.length l <= 16 })
  = if 1 <= LL.length start.CS.start_signature_schemes && LL.length start.CS.start_signature_schemes <= 16
    then start.CS.start_signature_schemes
    else [GSS.Rsa_pss_rsae_sha256]

// ---- canonical extension builders (each discharges its EverParse refinement) ----
noextract
let cho_sn_ext (sni: B.bytes { 1 <= Seq.length sni /\ Seq.length sni <= 255 })
  : GECH.extensionClientHello
  = let hn : GHN.hostName = sni in
    let sn : GSN.serverName = GSN.Name_host_name hn in
    GSNL.serverNameList_list_bytesize_nil;
    GSNL.serverNameList_list_bytesize_cons sn [];
    GSN.serverName_bytesize_eqn_host_name hn;
    GHN.hostName_bytesize_eqn hn;
    GECH.Extension_data_server_name ([sn] <: GECH.extensionClientHello_extension_data_server_name)

noextract
let cho_sg_ext : GECH.extensionClientHello
  = GECH.Extension_data_supported_groups ([GNG.X25519] <: GECH.extensionClientHello_extension_data_supported_groups)

noextract
let cho_sa_data (l: list GSS.signatureScheme { 1 <= LL.length l /\ LL.length l <= 16 })
  : GECH.extensionClientHello_extension_data_signature_algorithms
  = GSSL.signatureSchemeList_bytesize_eqn (l <: GSSL.signatureSchemeList);
    (l <: GECH.extensionClientHello_extension_data_signature_algorithms)

noextract
let cho_sa_ext (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : GECH.extensionClientHello
  = GECH.Extension_data_signature_algorithms sa

noextract
let cho_ks_ext (ks: B.bytes { Seq.length ks == 32 })
  : GECH.extensionClientHello
  = let ke : GKSE.keyShareEntry_key_exchange = ks in
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = ke } in
    GKSCH.keyShareClientHello_list_bytesize_nil;
    GKSCH.keyShareClientHello_list_bytesize_cons kse [];
    GKSE.keyShareEntry_bytesize_eqn kse;
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn ke;
    GECH.Extension_data_key_share ([kse] <: GECH.extensionClientHello_extension_data_key_share)

noextract
let cho_sv_ext : GECH.extensionClientHello
  = GECH.Extension_data_supported_versions ([GPV.TLS_1p3] <: GECH.extensionClientHello_extension_data_supported_versions)

noextract
let client_hello_of_start (start:CS.handshake_start) : GCH.clientHello
  = let sni = cho_sni start in
    let cs = cho_cs start in
    let sa = cho_sa_data (cho_sa_list start) in
    let r32 : Seq.lseq U8.t 32 = start.CS.start_client_random in
    let ks = start.CS.start_client_key_share_public in
    let sn_ext = cho_sn_ext sni in
    let sg_ext = cho_sg_ext in
    let sa_ext = cho_sa_ext sa in
    let ks_ext = cho_ks_ext ks in
    let sv_ext = cho_sv_ext in
    GCH.clientHello_extensions_list_bytesize_nil;
    GCH.clientHello_extensions_list_bytesize_cons sv_ext [];
    GCH.clientHello_extensions_list_bytesize_cons ks_ext [sv_ext];
    GCH.clientHello_extensions_list_bytesize_cons sa_ext [ks_ext; sv_ext];
    GCH.clientHello_extensions_list_bytesize_cons sg_ext [sa_ext; ks_ext; sv_ext];
    GCH.clientHello_extensions_list_bytesize_cons sn_ext [sg_ext; sa_ext; ks_ext; sv_ext];
    let exts : GCH.clientHello_extensions = [sn_ext; sg_ext; sa_ext; ks_ext; sv_ext] in
    let comp : GCH.clientHello_legacy_compression_methods = Seq.create 1 0uy in
    let sid : GCH.clientHello_legacy_session_id = B.empty in
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = r32;
      GCH.legacy_session_id = sid;
      GCH.cipher_suites = cs;
      GCH.legacy_compression_methods = comp;
      GCH.extensions = exts; }

// Phase 5 (server build direction): server_hello_of_selection builds the
// faithful canonical ServerHello (X25519 32-byte key_share + supported_versions,
// legacy_version TLS 1.2, empty session-id echo, CHACHA cipher suite) from a
// server_handshake_selection.  It is the server mirror of client_hello_of_start
// and is structurally identical to the verified reference
// TLS13.Impl.Serializer.Handshake.poc_canonical_sh applied to
//   (selection.server_random, selection.server_key_share_public, CHACHA).
// It is TOTAL: the (unbounded/unconstrained) selection random is CLAMPED to a
// value differing from the HelloRetryRequest sentinel (serverHello_body_cst).
// Under `valid_selection sel` the clamp is the identity, so every
// TLS13.Wire.Semantics accessor returns the matching selection field (see
// lemma_server_hello_of_selection_matches).

// valid-selection predicate: the selection random differs from the HRR sentinel
// and the selected cipher suite is the single supported one, so the clamp in
// server_hello_of_selection is an identity and the record matches the selection.
let valid_selection (sel:CS.server_handshake_selection) : prop =
  (sel.CS.server_random <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
  sel.CS.server_selected_cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256

// clamp: a 32-byte server random differing from the HRR sentinel (identity under
// valid_selection).  The all-zero fallback differs from serverHello_body_cst at
// index 0 (0uy <> 0xcfuy).
noextract
let sho_random (sel:CS.server_handshake_selection)
  : (r:Seq.lseq U8.t 32 { r <> GSHB.serverHello_body_cst })
  = if (sel.CS.server_random <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst
    then (sel.CS.server_random <: Seq.lseq U8.t 32)
    else (Seq.lemma_index_create 32 0uy 0;
          assert_norm (Seq.index GSHB.serverHello_body_cst 0 == 0xcfuy);
          Seq.create 32 0uy)

#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
noextract
let server_hello_of_selection (sel:CS.server_handshake_selection) : GSH.serverHello
  = let rnd : Seq.lseq U8.t 32 = sho_random sel in
    let ks : B.bytes = sel.CS.server_key_share_public in
    let cs : GCS.cipherSuite = T.TLS_CHACHA20_POLY1305_SHA256 in
    let ke : GKSE.keyShareEntry_key_exchange = ks in
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = ke } in
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn ke;
    let ksesh : GESH.extensionServerHello_extension_data_key_share = kse in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share ksesh in
    let sv_ext : GESH.extensionServerHello =
      GESH.Extension_data_supported_versions
        (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions) in
    GSHBody.serverHelloBody_extensions_list_bytesize_nil;
    GSHBody.serverHelloBody_extensions_list_bytesize_cons sv_ext [];
    GSHBody.serverHelloBody_extensions_list_bytesize_cons ks_ext [sv_ext];
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p3;
    let exts : GSHBody.serverHelloBody_extensions = [ks_ext; sv_ext] in
    let sid : GSHBody.serverHelloBody_legacy_session_id_echo = B.empty in
    let body : GSHBody.serverHelloBody = {
      GSHBody.legacy_session_id_echo = sid;
      GSHBody.cipher_suite = cs;
      GSHBody.legacy_compression_method = 0uy;
      GSHBody.extensions = exts;
    } in
    let bf : GSHB.serverHello_body_false = { GSHB.tag = rnd; GSHB.value = body } in
    { GSH.legacy_version = GPV.TLS_1p2; GSH.body = GSHB.ServerHello_body_false bf }
#pop-options

noextract
let started_handshake_state
  (st:CS.connection_state)
  (start:CS.handshake_start)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with CS.hs_start = Some start }
        CS.HsStarted;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalStartHandshake start)];
  }

let can_start_handshake
  (st:CS.connection_state)
  (start:CS.handshake_start)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlNew /\
  CS.start_matches_config st.CS.cs_model.CS.model_config start /\
  CS.handshake_start_key_share_consistent start /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalStartHandshake start))

noextract
let started_server_state
  (st:CS.connection_state)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        model0.CS.model_handshake
        CS.HsAwaitingClientHello;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent CS.LocalStartServer];
  }

let can_start_server
  (st:CS.connection_state)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlNew /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  Some? st.CS.cs_model.CS.model_config.CS.config_server /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent CS.LocalStartServer)

noextract
let selected_server_parameters_state
  (st:CS.connection_state)
  (selection:CS.server_handshake_selection)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with
            CS.hs_server_selection = Some selection;
            CS.hs_client_hello = Some selection.CS.server_selected_client_hello;
        }
        CS.HsClientHelloReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
        [CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)];
  }

let can_select_server_parameters
  (st:CS.connection_state)
  (selection:CS.server_handshake_selection)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  st.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some selection.CS.server_selected_client_hello /\
  (match st.CS.cs_model.CS.model_config.CS.config_server with
   | Some cfg -> CS.server_selection_acceptable cfg selection
   | None -> False) /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection))

let sent_client_hello_state
  (st:CS.connection_state)
  (ch:GCH.clientHello)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.ClientHello ch in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_client_hello = Some ch;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_client_hello_bytes = W.serialize_handshake msg };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model0 hs1 CS.HsClientHelloSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_client_hello
  (st:CS.connection_state)
  (ch:GCH.clientHello)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsStarted /\
  st.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_start with
   | Some start -> CS.client_hello_matches_start start ch
   | None -> False) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.ClientHello ch)) <= max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    })
    raw_sent
    B.empty

// Under valid_start, the canonical client_hello_of_start satisfies the spec's
// client_hello_matches_start: every TLS13.Wire.Semantics accessor returns the
// corresponding `start` field (the clamps in client_hello_of_start are
// identities under valid_start).
val lemma_client_hello_of_start_matches
  (start:CS.handshake_start)
  : Lemma (requires valid_start start)
          (ensures CS.client_hello_matches_start start (client_hello_of_start start))

// Server mirror of the client bound (see lemma_client_hello_of_start_matches's
// record-size reasoning): the canonical server_hello_of_selection serializes to
// exactly 90 bytes (legacy_version TLS_1p2 + 32-byte random + empty session-id +
// CHACHA cipher suite + null compression + [X25519 key_share; supported_versions]).
// Reveals serialize_handshake to the generated serializer and computes the
// bytesize; used to discharge the transcript-length obligation inside
// can_send_server_hello for the server build direction.
val lemma_server_hello_of_selection_bytesize
  (sel:CS.server_handshake_selection)
  : Lemma (requires valid_selection sel)
          (ensures
            B.length (W.serialize_handshake
              (M.ServerHello (server_hello_of_selection sel))) == 90)

// Server mirror: under valid_selection, the canonical server_hello_of_selection
// satisfies the spec's server_hello_matches_selection: every
// TLS13.Wire.Semantics accessor returns the corresponding `selection` field (the
// clamp in server_hello_of_selection is an identity under valid_selection).
// The <= 16640 conjunct in server_hello_matches_selection is discharged from the
// exact 90-byte bytesize above (lemma_server_hello_of_selection_bytesize).
val lemma_server_hello_of_selection_matches
  (sel:CS.server_handshake_selection)
  : Lemma (requires valid_selection sel)
          (ensures CS.server_hello_matches_selection sel (server_hello_of_selection sel))

// Faithful len-helper bridge: under valid_start the canonical
// client_hello_of_start's TLS13.Wire.Semantics accessor lengths agree with the
// runtime *_len values implied by the structure-match predicates.  (Not on the
// LocalHandshake hot path -- that derives the same equalities directly from the
// serializer postcondition via lemma_client_hello_len_for_from_serializer --
// but proved here for faithfulness of the Model interface.)
val lemma_client_hello_len_helpers_from_start
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

noextract
let derived_shared_secret_state
  (st:CS.connection_state)
  (shared:TLS13.Crypto.Spec.x25519_shared_secret)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let early = K.early_secret B.empty in
  let handshake = K.handshake_secret early shared in
  let master = K.master_secret handshake in
  let keys0 = hs0.CS.hs_keys in
  let keys1 =
    {
      keys0 with
        CS.ks_shared_secret = Some shared;
        CS.ks_early_secret = Some early;
        CS.ks_handshake_secret = Some handshake;
        CS.ks_master_secret = Some master;
    } in
  {
    CS.cs_model =
      CS.with_handshake_state model0 { hs0 with CS.hs_keys = keys1 };
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)];
  }

noextract
let installed_traffic_keys_state
  (st:CS.connection_state)
  (install:CS.traffic_key_install)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model = {
      model0 with
        CS.model_record = CS.install_record_keys model0.CS.model_record install;
        CS.model_handshake = {
          hs0 with
            CS.hs_keys = CS.update_key_schedule_with_install hs0.CS.hs_keys install;
        };
    };
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)];
  }

noextract
let installed_traffic_keys_for_role_state
  (st:CS.connection_state)
  (role_install:CS.role_traffic_key_install)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let install = role_install.CS.install_payload in
  {
    CS.cs_model = {
      model0 with
        CS.model_record =
          CS.install_record_keys_for_role
            role_install.CS.install_role
            model0.CS.model_record
            install;
        CS.model_handshake = {
          hs0 with
            CS.hs_keys =
              CS.update_key_schedule_with_install_for_role
                role_install.CS.install_role
                hs0.CS.hs_keys
                install;
        };
    };
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
        [CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)];
  }

noextract
let validated_certificate_state
  (st:CS.connection_state)
  (peer:X.peer_identity)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with CS.hs_validated_peer = Some peer }
        CS.HsCertificateValidated;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalValidateCertificate peer)];
  }

noextract
let received_hello_retry_request_rejected_state
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : CS.connection_state =
  {
    CS.cs_model = CS.fail_model st.CS.cs_model tls_hello_retry_request_rejected_error;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake M.HelloRetryRequest;
      }];
  }

noextract
let received_change_cipher_spec_state
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : CS.connection_state =
  {
    CS.cs_model = st.CS.cs_model;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsChangeCipherSpec;
      }];
  }

let received_server_hello_state
  (st:CS.connection_state)
  (sh:GSH.serverHello)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.ServerHello sh in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_server_hello = Some sh;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_server_hello_bytes = W.serialize_handshake msg };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model0 hs1 CS.HsServerHelloReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let sent_server_hello_state
  (st:CS.connection_state)
  (sh:GSH.serverHello)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.ServerHello sh in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_server_hello = Some sh;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_server_hello_bytes = W.serialize_handshake msg };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model0 hs1 CS.HsServerHelloSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_server_hello
  (st:CS.connection_state)
  (sh:GSH.serverHello)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  st.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
   | Some selection -> CS.server_hello_matches_selection selection sh
   | None -> False) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.ServerHello sh)) <=
    max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })
    raw_sent
    B.empty

let sent_encrypted_extensions_state
  (st:CS.connection_state)
  (ee:GEE.encryptedExtensions)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.EncryptedExtensions ee in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with CS.hs_encrypted_extensions = Some ee }
      msg in
  {
    CS.cs_model =
      CS.with_handshake_stage
        { model0 with
            CS.model_record =
              { model0.CS.model_record with
                  CS.record_write = R.next_seq model0.CS.model_record.CS.record_write;
              };
        }
        hs1
        CS.HsServerEncryptedFlightSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_encrypted_extensions
  (st:CS.connection_state)
  (ee:GEE.encryptedExtensions)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerHelloSent /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  Sem.encryptedExtensions_alpn ee == None /\
  Some?
    st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.EncryptedExtensions ee)) <=
    max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    })
    raw_sent
    B.empty

let sent_certificate_state
  (st:CS.connection_state)
  (cert:GCert.certificate)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Certificate cert in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_certificate = Some cert;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_certificate_leaf_der =
                  (match (Sem.certificate_entries cert) with
                   | leaf :: _ -> Some leaf
                   | [] -> None);
            };
      }
      msg in
  {
    CS.cs_model =
      CS.with_handshake_stage
        { model0 with
            CS.model_record =
              { model0.CS.model_record with
                  CS.record_write = R.next_seq model0.CS.model_record.CS.record_write;
              };
        }
        hs1
        CS.HsServerEncryptedFlightSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_certificate
  (st:CS.connection_state)
  (cert:GCert.certificate)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  st.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
  st.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
  Some?
    st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  (match st.CS.cs_model.CS.model_config.CS.config_server with
   | Some cfg -> CS.certificate_msg_matches_server_config cfg cert
   | None -> False) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.Certificate cert)) <=
    max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    })
    raw_sent
    B.empty

let signed_certificate_verify_state
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let cv_input = H.certificate_verify_input (Tr.hash hs0.CS.hs_transcript) in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with
            CS.hs_certificate_verify = Some cv;
            CS.hs_buffers =
              { hs0.CS.hs_buffers with
                  CS.hb_certificate_verify_input = Some cv_input;
              };
        }
        CS.HsServerEncryptedFlightSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv)];
  }

let can_sign_certificate_verify
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  st.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
  st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
  st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv))

let sent_certificate_verify_state
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.CertificateVerify cv in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_certificate_verify = Some cv;
          CS.hs_certificate_verify_verified = true;
      }
      msg in
  {
    CS.cs_model =
      CS.with_handshake_stage
        { model0 with
            CS.model_record =
              { model0.CS.model_record with
                  CS.record_write = R.next_seq model0.CS.model_record.CS.record_write;
              };
        }
        hs1
        CS.HsServerEncryptedFlightSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_certificate_verify
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  st.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
  Some?
    st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
   | Some stored_cv -> stored_cv == cv
   | None -> False) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.CertificateVerify cv)) <=
    max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    })
    raw_sent
    B.empty

let sent_server_finished_state
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Finished fin in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with CS.hs_server_finished = Some fin }
      msg in
  {
    CS.cs_model =
      CS.with_handshake_stage
        { model0 with
            CS.model_record =
              { model0.CS.model_record with
                  CS.record_write = R.next_seq model0.CS.model_record.CS.record_write;
              };
        }
        hs1
        CS.HsServerFinishedSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_server_finished
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
   | Some server_hs ->
     H.verify_finished
       server_hs.CS.traffic_secret
       (Tr.hash st.CS.cs_model.CS.model_handshake.CS.hs_transcript)
       fin
   | None -> False) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.Finished fin)) <=
    max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    })
    raw_sent
    B.empty

let received_client_finished_state
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Finished fin in
  {
    CS.cs_model =
      CS.with_handshake_stage
        { model0 with
            CS.model_record =
              { model0.CS.model_record with
                  CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
              };
        }
        { hs0 with CS.hs_client_finished = Some fin }
        CS.HsClientFinishedReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_receive_client_finished
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_received:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedSent /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  st.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
  Some?
    st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    })
    B.empty
    raw_received

let verified_client_finished_state
  (st:CS.connection_state)
  (fin:GFin.finished)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model = {
      model0 with
        CS.model_control = CS.ControlApplicationData;
        CS.model_handshake =
          CS.append_handshake_to_transcript
            { hs0 with CS.hs_client_finished = Some fin }
            (M.Finished fin);
    };
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)];
  }

let can_verify_client_finished
  (st:CS.connection_state)
  (fin:GFin.finished)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientFinishedReceived /\
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    st.CS.cs_model /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
         st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
   | Some stored_fin, Some client_hs ->
     stored_fin == fin /\
     H.verify_finished
       client_hs.CS.traffic_secret
       (Tr.hash st.CS.cs_model.CS.model_handshake.CS.hs_transcript)
       fin
   | _, _ -> False) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.Finished fin)) <=
    max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin))

let received_client_hello_state
  (st:CS.connection_state)
  (ch:GCH.clientHello)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.ClientHello ch in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
         CS.hs_client_hello = Some ch;
         CS.hs_buffers =
           { hs0.CS.hs_buffers with
               CS.hb_client_hello_bytes = W.serialize_handshake msg };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model0 hs1 CS.HsClientHelloReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake msg;
      }];
  }

let received_encrypted_extensions_state
  (st:CS.connection_state)
  (ee:GEE.encryptedExtensions)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.EncryptedExtensions ee in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with CS.hs_encrypted_extensions = Some ee }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model1 hs1 CS.HsEncryptedExtensionsReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let received_certificate_state
  (st:CS.connection_state)
  (cert:GCert.certificate)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Certificate cert in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_certificate = Some cert;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_certificate_leaf_der =
                  (match (Sem.certificate_entries cert) with
                   | leaf :: _ -> Some leaf
                   | [] -> None);
            };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model1 hs1 CS.HsCertificateReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let received_certificate_verify_state
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.CertificateVerify cv in
  let cv_input = H.certificate_verify_input (Tr.hash hs0.CS.hs_transcript) in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_certificate_verify = Some cv;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_certificate_verify_input = Some cv_input;
            };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model1 hs1 CS.HsCertificateVerifyReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

noextract
let verified_certificate_signature_state
  (st:CS.connection_state)
  (cv:GCV.certificateVerify)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with
            CS.hs_certificate_verify = Some cv;
            CS.hs_certificate_verify_verified = true;
        }
        CS.HsCertificateVerifyVerified;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)];
  }

noextract
let received_server_finished_state
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Finished fin in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model1
        { hs0 with CS.hs_server_finished = Some fin }
        CS.HsServerFinishedReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let verified_server_finished_state
  (st:CS.connection_state)
  (fin:GFin.finished)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        (CS.append_handshake_to_transcript
          { hs0 with
              CS.hs_server_finished = Some fin;
              CS.hs_server_finished_verified = true;
          }
          (M.Finished fin))
        CS.HsServerFinishedVerified;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalVerifyFinished fin)];
  }

let sent_client_finished_state
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Finished fin in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with CS.hs_client_finished = Some fin }
      msg in
  let model1 = {
    model0 with
      CS.model_control = CS.ControlApplicationData;
      CS.model_record =
        CS.install_client_application_write_after_finished
          model0.CS.model_record
          hs0.CS.hs_keys;
      CS.model_handshake = hs1;
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_client_finished
  (st:CS.connection_state)
  (fin:GFin.finished)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedVerified /\
  st.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.Finished fin)) <= max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    })
    raw_sent
    B.empty /\
  TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    })
    raw_sent

noextract
let received_alert_failure_state
  (st:CS.connection_state)
  (alert:T.alert_description)
  (raw_received:B.bytes)
  : CS.connection_state =
  {
    CS.cs_model = CS.fail_model st.CS.cs_model (T.AlertError alert);
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsAlert alert;
      }];
  }

noextract
let received_close_notify_state
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let model1 = {
    model0 with
      CS.model_control = CS.ControlClosed;
      CS.model_record = {
        record0 with
          CS.record_read = R.next_seq record0.CS.record_read;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsAlert T.Close_notify;
      }];
  }

noextract
let sent_close_notify_state
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let model1 = {
    model0 with
      CS.model_control = CS.ControlClosing;
      CS.model_record = {
        record0 with
          CS.record_write = R.next_seq record0.CS.record_write;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsAlert T.Close_notify;
      }];
  }

noextract
let received_application_data_state
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let app0 = model0.CS.model_application in
  let model1 = {
    model0 with
      CS.model_record = {
        record0 with
          CS.record_read = R.next_seq record0.CS.record_read;
      };
      CS.model_application = {
        app0 with
          CS.app_log = CL.append_app_received app0.CS.app_log bytes;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsApplicationData bytes;
      }];
  }

noextract
let received_ignored_post_handshake_state
  (st:CS.connection_state)
  (body:B.bytes)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let model1 = {
    model0 with
      CS.model_record = {
        record0 with
          CS.record_read = R.next_seq record0.CS.record_read;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsIgnoredPostHandshake body;
      }];
  }

noextract
let received_key_update_state
  (st:CS.connection_state)
  (req:M.key_update_request)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  match hs0.CS.hs_keys.CS.ks_server_application_traffic with
  | Some old_server_app ->
    let new_server_app = CS.updated_traffic_key_material old_server_app in
    let model1 = {
      model0 with
        CS.model_record = {
          model0.CS.model_record with
            CS.record_read =
              R.install_keys
                (R.next_seq model0.CS.model_record.CS.record_read)
                R.Application
                new_server_app.CS.traffic_key
                new_server_app.CS.traffic_iv;
        };
        CS.model_handshake = {
          hs0 with
            CS.hs_keys = {
              hs0.CS.hs_keys with
                CS.ks_server_application_traffic = Some new_server_app;
            };
        };
        CS.model_application =
          CS.received_key_update_pending
            model0.CS.model_application
            req;
    } in
    {
      CS.cs_model = model1;
      CS.cs_wire_log = {
        CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
        CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
      };
      CS.cs_event_log =
        st.CS.cs_event_log @
        [CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsKeyUpdate req;
        }];
    }
  | None ->
    st

noextract
let received_key_update_not_requested_state
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : CS.connection_state =
  received_key_update_state st M.UpdateNotRequested raw_received

noextract
let sent_key_update_response_state
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  match hs0.CS.hs_keys.CS.ks_client_application_traffic with
  | Some old_client_app ->
    let new_client_app = CS.updated_traffic_key_material old_client_app in
    let model1 = {
      model0 with
        CS.model_record = {
          model0.CS.model_record with
            CS.record_write =
              R.install_keys
                (R.next_seq model0.CS.model_record.CS.record_write)
                R.Application
                new_client_app.CS.traffic_key
                new_client_app.CS.traffic_iv;
        };
        CS.model_handshake = {
          hs0 with
            CS.hs_keys = {
              hs0.CS.hs_keys with
                CS.ks_client_application_traffic = Some new_client_app;
            };
        };
        CS.model_application = {
          model0.CS.model_application with
            CS.app_key_update_response_pending = false;
        };
    } in
    {
      CS.cs_model = model1;
      CS.cs_wire_log = {
        CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
        CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
      };
      CS.cs_event_log =
        st.CS.cs_event_log @
        [CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
        }];
    }
  | None ->
    st

noextract
let delivered_application_data_state
  (st:CS.connection_state)
  (bytes:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let app0 = model0.CS.model_application in
  let model1 = {
    model0 with
      CS.model_application = {
        app0 with
          CS.app_log = CL.append_app_received app0.CS.app_log bytes;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)];
  }

noextract
let sent_application_data_state
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_sent:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let app0 = model0.CS.model_application in
  let model1 = {
    model0 with
      CS.model_record = {
        record0 with
          CS.record_write = R.next_seq record0.CS.record_write;
      };
      CS.model_application = {
        app0 with
          CS.app_log = CL.append_app_sent app0.CS.app_log bytes;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsApplicationData bytes;
      }];
  }

val lemma_application_data_record_count_small
  (bytes:B.bytes)
  : Lemma
      (requires B.length bytes <= SM.max_application_data_fragment_len)
      (ensures SM.application_data_record_count bytes == 1)

val lemma_advance_direction_records_one (s:R.direction_state)
  : Lemma (CS.advance_direction_records s 1 == R.next_seq s)

val lemma_seal_application_success_next_seq
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

let can_send_application_data
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  CS.application_traffic_available_for_role
    st.CS.cs_model.CS.model_config.CS.config_role
    st.CS.cs_model.CS.model_handshake
    CL.Sent /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  B.length bytes <= SM.max_application_data_fragment_len /\
  SM.application_data_record_count bytes == 1 /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    })
    raw_sent
    B.empty /\
  TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    })
    raw_sent

noextract

val close_notify_alert_fragment: unit -> GTot B.bytes

val lemma_close_notify_alert_fragment_generated:
  unit ->
  Lemma (
    close_notify_alert_fragment () ==
    LP.serialize GA.alert_serializer {
      GA.level = GAL.Fatal;
      GA.description = GAD.Close_notify;
    })

noextract

let key_update_response_fragment : B.bytes =
  B.of_list [24uy; 0uy; 0uy; 1uy; 0uy]

let can_send_close_notify
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  CS.application_traffic_available_for_role
    st.CS.cs_model.CS.model_config.CS.config_role
    st.CS.cs_model.CS.model_handshake
    CL.Sent /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.Close_notify;
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.Close_notify;
    })
    raw_sent
    B.empty /\
  TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.Close_notify;
    })
    raw_sent

let can_send_key_update
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  st.CS.cs_model.CS.model_application.CS.app_key_update_response_pending /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
    })
    raw_sent
    B.empty /\
  TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
    })
    raw_sent

let can_send_application_data_sizes
  (payload_len:SZ.t)
  (network_out_len:SZ.t)
  : Pure bool
      (requires True)
      (ensures fun ok ->
        ok ==> SZ.v payload_len <= SM.max_application_data_fragment_len /\
                 SZ.v payload_len + 22 <= SZ.v network_out_len)
=
  assert_norm (SM.max_application_data_fragment_len == 16384);
  let max_payload = 16384sz in
  let payload_fits = sizet_lte_plain payload_len max_payload in
  lemma_sizet_lte_plain payload_len max_payload;
  if payload_fits then
    begin
      assert (SZ.v payload_len <= SM.max_application_data_fragment_len);
      assert (SZ.fits (SZ.v payload_len + 22));
      let needed = SZ.add payload_len 22sz in
      let out_room = sizet_lte_plain needed network_out_len in
      lemma_sizet_lte_plain needed network_out_len;
      assert (out_room ==> SZ.v payload_len + 22 <= SZ.v network_out_len);
      out_room
    end
  else
    false

let can_send_close_notify_sizes
  (network_out_len:SZ.t)
  : Pure bool
      (requires True)
      (ensures fun ok ->
        ok ==> 24 <= SZ.v network_out_len)
=
  let out_room = sizet_lte_plain 24sz network_out_len in
  lemma_sizet_lte_plain 24sz network_out_len;
  out_room

let can_send_key_update_sizes
  (network_out_len:SZ.t)
  : Pure bool
      (requires True)
      (ensures fun ok ->
        ok ==> 27 <= SZ.v network_out_len)
=
  let out_room = sizet_lte_plain 27sz network_out_len in
  lemma_sizet_lte_plain 27sz network_out_len;
  out_room

val lemma_local_fail_state_evolves (st:CS.connection_state) (err:T.tls_error)
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

val lemma_started_handshake_state_evolves
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

val lemma_started_server_state_evolves
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

val lemma_selected_server_parameters_state_evolves
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

val lemma_sent_client_hello_state_evolves
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

val lemma_derived_shared_secret_state_evolves
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

val lemma_installed_traffic_keys_state_evolves
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

val lemma_installed_traffic_keys_for_role_state_evolves
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

val lemma_validated_certificate_state_evolves
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

val lemma_client_handshake_traffic_install_legal
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
                (K.client_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))

val lemma_server_handshake_traffic_install_legal
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
                (K.server_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))

val lemma_server_role_server_handshake_write_traffic_install_legal
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
                 (K.server_handshake_traffic_secret
                   handshake_secret
                   (Tr.hash model.CS.model_handshake.CS.hs_transcript));
           };
          })))

val lemma_server_role_client_handshake_read_traffic_install_legal
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
                 (K.client_handshake_traffic_secret
                   handshake_secret
                   (Tr.hash model.CS.model_handshake.CS.hs_transcript));
           };
          })))

val lemma_client_application_traffic_install_legal
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
                (K.client_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))

val lemma_server_application_traffic_install_legal
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
                (K.server_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))

val lemma_server_role_server_application_write_traffic_install_legal
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
                 (K.server_application_traffic_secret
                   master_secret
                   (Tr.hash model.CS.model_handshake.CS.hs_transcript));
           };
          })))

val lemma_server_role_client_application_read_traffic_install_legal
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
                 (K.client_application_traffic_secret
                   master_secret
                   (Tr.hash model.CS.model_handshake.CS.hs_transcript));
           };
          })))

val lemma_received_hello_retry_request_rejected_state_evolves
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

val lemma_received_change_cipher_spec_state_evolves
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

val lemma_received_server_hello_state_evolves
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

val lemma_sent_server_hello_state_evolves
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

val lemma_sent_encrypted_extensions_state_evolves
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

val lemma_sent_certificate_state_evolves
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

val lemma_signed_certificate_verify_state_evolves
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

val lemma_sent_certificate_verify_state_evolves
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

val lemma_sent_server_finished_state_evolves
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

val lemma_received_client_finished_state_evolves
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

val lemma_verified_client_finished_state_evolves
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

val lemma_received_client_hello_state_evolves
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

val lemma_received_encrypted_extensions_state_evolves
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

val lemma_received_certificate_state_evolves
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

val lemma_received_certificate_verify_state_evolves
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

val lemma_verified_certificate_signature_state_evolves
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

val lemma_received_server_finished_state_evolves
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

val lemma_verified_server_finished_state_evolves
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

val lemma_sent_client_finished_state_evolves
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

val lemma_received_alert_failure_state_evolves
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

val lemma_received_close_notify_state_evolves_for_role
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

val lemma_received_close_notify_state_evolves
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

val lemma_sent_close_notify_state_evolves
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

val lemma_received_application_data_state_evolves_for_role
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

val lemma_received_application_data_state_evolves
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

val lemma_received_ignored_post_handshake_state_evolves
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

val lemma_received_key_update_state_evolves
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

val lemma_received_key_update_not_requested_state_evolves
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

val lemma_sent_key_update_response_state_evolves
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

val lemma_delivered_application_data_state_evolves
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

val lemma_sent_application_data_state_evolves
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
