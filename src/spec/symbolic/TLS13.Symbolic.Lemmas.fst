module TLS13.Symbolic.Lemmas

module B = TLS13.Bytes
module DY = DY.Core
module Events = TLS13.Symbolic.Events
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages

val x25519_shared_agreement:
  client_secret:DY.bytes ->
  server_secret:DY.bytes ->
  Lemma
    (Terms.x25519_shared
       client_secret
       (Terms.x25519_public server_secret) ==
     Terms.x25519_shared
       server_secret
       (Terms.x25519_public client_secret))
let x25519_shared_agreement client_secret server_secret =
  DY.dh_shared_secret_lemma client_secret server_secret

val public_record_nonce_shape:
  nonce:B.bytes ->
  Lemma
    (Terms.public_record_nonce nonce == DY.Literal nonce)
let public_record_nonce_shape nonce = ()

val protected_record_shape:
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (Terms.protected_record key nonce plaintext additional_data ==
     DY.AeadEnc key nonce plaintext additional_data)
let protected_record_shape key nonce plaintext additional_data = ()

val handshake_event_shape:
  principal:DY.principal ->
  kind:Events.event_kind ->
  context:Terms.session_context ->
  details:DY.bytes ->
  Lemma
    (Events.handshake_event_entry principal kind context details ==
     DY.Event
       principal
       (Events.event_tag kind)
       (DY.Concat (Terms.encode_session_context context) details))
let handshake_event_shape principal kind context details = ()

val tls_dh_usage_known_peer:
  client_session:Terms.endpoint_session ->
  server_session:Terms.endpoint_session ->
  Lemma
    (Usages.known_peer_dh_usage
       (Usages.ephemeral_dh_usage client_session)
       (Usages.ephemeral_dh_usage server_session) ==
     Usages.shared_dh_usage)
let tls_dh_usage_known_peer client_session server_session = ()

val public_bytes_well_formed:
  tr:DY.trace ->
  value:B.bytes ->
  Lemma (DY.bytes_well_formed tr (Terms.public_bytes value))
let public_bytes_well_formed tr value =
  normalize_term_spec DY.bytes_well_formed

val x25519_public_well_formed:
  tr:DY.trace ->
  secret:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr (Terms.x25519_public secret) ==
     DY.bytes_well_formed tr secret)
let x25519_public_well_formed tr secret =
  DY.bytes_well_formed_dh_pk tr secret

val x25519_shared_well_formed:
  tr:DY.trace ->
  secret:DY.bytes ->
  peer_public:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.x25519_shared secret peer_public)
     <==>
     DY.bytes_well_formed tr secret /\
     DY.bytes_well_formed tr peer_public)
let x25519_shared_well_formed tr secret peer_public =
  DY.bytes_well_formed_dh tr secret peer_public

val hkdf_info_well_formed:
  tr:DY.trace ->
  output_length_high:B.byte ->
  output_length_low:B.byte ->
  label_length:B.byte ->
  label:B.bytes ->
  context_length:B.byte ->
  context:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.hkdf_info
         output_length_high output_length_low label_length
         label context_length context)
     <==>
     DY.bytes_well_formed tr context)
let hkdf_info_well_formed
  tr output_length_high output_length_low label_length
  label context_length context =
  normalize_term_spec DY.bytes_well_formed

val derive_secret_well_formed:
  tr:DY.trace ->
  secret:DY.bytes ->
  label:B.bytes ->
  label_length:B.byte ->
  context:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.derive_secret secret label label_length context)
     <==>
     DY.bytes_well_formed tr secret /\
     DY.bytes_well_formed tr context)
let derive_secret_well_formed
  tr secret label label_length context =
  normalize_term_spec DY.bytes_well_formed

val certificate_verify_well_formed:
  tr:DY.trace ->
  signing_key:DY.bytes ->
  nonce:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.certificate_verify signing_key nonce transcript)
     <==>
     DY.bytes_well_formed tr signing_key /\
     DY.bytes_well_formed tr nonce /\
     DY.bytes_well_formed tr transcript)
let certificate_verify_well_formed tr signing_key nonce transcript =
  normalize_term_spec DY.bytes_well_formed

val protected_record_well_formed:
  tr:DY.trace ->
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.protected_record key nonce plaintext additional_data)
     <==>
     DY.bytes_well_formed tr key /\
     DY.bytes_well_formed tr nonce /\
     DY.bytes_well_formed tr plaintext /\
     DY.bytes_well_formed tr additional_data)
let protected_record_well_formed tr key nonce plaintext additional_data =
  normalize_term_spec DY.bytes_well_formed

val finished_verify_data_well_formed:
  tr:DY.trace ->
  traffic_secret:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.finished_verify_data traffic_secret transcript)
     <==>
     DY.bytes_well_formed tr traffic_secret /\
     DY.bytes_well_formed tr transcript)
let finished_verify_data_well_formed tr traffic_secret transcript =
  normalize_term_spec DY.bytes_well_formed

val application_plaintext_well_formed:
  tr:DY.trace ->
  content:DY.bytes ->
  content_type_and_padding:B.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.application_plaintext content content_type_and_padding)
     <==>
     DY.bytes_well_formed tr content)
let application_plaintext_well_formed
  tr content content_type_and_padding =
  normalize_term_spec DY.bytes_well_formed

val public_bytes_label:
  tr:DY.trace ->
  value:B.bytes ->
  Lemma
    (DY.get_label tr (Terms.public_bytes value) == DY.public)
let public_bytes_label tr value =
  normalize_term_spec DY.get_label

val x25519_public_label:
  tr:DY.trace ->
  secret:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.x25519_public secret) == DY.public)
let x25519_public_label tr secret =
  DY.get_label_dh_pk tr secret

val transcript_hash_label:
  tr:DY.trace ->
  transcript:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.transcript_hash transcript) ==
     DY.get_label tr transcript)
let transcript_hash_label tr transcript =
  normalize_term_spec Terms.transcript_hash;
  normalize_term_spec DY.get_label

val x25519_shared_label:
  tr:DY.trace ->
  client_secret:DY.bytes ->
  server_secret:DY.bytes ->
  Lemma
    (DY.get_label tr
       (Terms.x25519_shared
         client_secret
         (Terms.x25519_public server_secret)) ==
     DY.join
       (DY.get_label tr client_secret)
       (DY.get_label tr server_secret))
let x25519_shared_label tr client_secret server_secret =
  normalize_term_spec Terms.x25519_shared;
  normalize_term_spec Terms.x25519_public;
  normalize_term_spec DY.get_label;
  normalize_term_spec DY.get_dh_label

val certificate_verify_label:
  tr:DY.trace ->
  signing_key:DY.bytes ->
  nonce:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (DY.get_label tr
       (Terms.certificate_verify signing_key nonce transcript) ==
     DY.get_label tr (Terms.certificate_verify_input transcript))
let certificate_verify_label tr signing_key nonce transcript =
  normalize_term_spec Terms.certificate_verify;
  normalize_term_spec DY.get_label

val protected_record_label:
  tr:DY.trace ->
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (DY.get_label tr
       (Terms.protected_record key nonce plaintext additional_data) ==
     DY.public)
let protected_record_label tr key nonce plaintext additional_data =
  normalize_term_spec Terms.protected_record;
  normalize_term_spec DY.get_label

val public_record_nonce_label:
  tr:DY.trace ->
  nonce:B.bytes ->
  Lemma
    (DY.get_label tr (Terms.public_record_nonce nonce) == DY.public)
let public_record_nonce_label tr nonce =
  public_bytes_label tr nonce

val kdf_expand_label:
  tr:DY.trace ->
  prk:DY.bytes ->
  info:DY.bytes ->
  length:nat{length <> 0} ->
  Lemma
    (DY.get_label tr (DY.KdfExpand prk info length) ==
     DY.get_label tr prk)
let kdf_expand_label tr prk info length =
  normalize_term_spec DY.get_label

val protected_record_not_certificate_verify:
  key:DY.bytes ->
  record_nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  signing_key:DY.bytes ->
  signing_nonce:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (Terms.protected_record
       key record_nonce plaintext additional_data
     =!=
     Terms.certificate_verify signing_key signing_nonce transcript)
let protected_record_not_certificate_verify
  key record_nonce plaintext additional_data
  signing_key signing_nonce transcript = ()

val event_tag_injective:
  left:Events.event_kind ->
  right:Events.event_kind ->
  Lemma
    (requires Events.event_tag left == Events.event_tag right)
    (ensures left == right)
let event_tag_injective left right = ()
