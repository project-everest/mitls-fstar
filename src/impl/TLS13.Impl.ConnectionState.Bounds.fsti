module TLS13.Impl.ConnectionState.Bounds

noextract
let max_hostname_len : nat = 255
noextract
let max_trust_anchors_len : nat = 65535
noextract
let max_public_key_len : nat = 4096
noextract
let max_cipher_suites : nat = 64
noextract
let max_signature_schemes : nat = 32
noextract
let max_client_hello_len : nat = 512
noextract
let max_server_hello_len : nat = 4096
noextract
let max_handshake_flight_len : nat = 32768
noextract
let max_transcript_len : nat = 65535
noextract
let max_certificate_verify_input_len : nat = 256
noextract
let max_server_certificate_chain_len : nat = 16610
noextract
let max_pending_plaintext_len : nat = 32768
noextract
let max_pending_raw_len : nat = 32768

module SZ = FStar.SizeT

(* [SZ.t] companions of the capacity bounds, defined with [sz] literals so they
   extract to plain C [size_t] constants ((size_t)N) rather than a call to
   [FStar_SizeT_uint_to_t].  Use these in executable [SZ.uint_to_t <const>]
   positions; [SZ.v <const>_sz == <const>] holds definitionally. *)
inline_for_extraction let max_hostname_len_sz : SZ.t = 255sz
inline_for_extraction let max_public_key_len_sz : SZ.t = 4096sz
inline_for_extraction let max_cipher_suites_sz : SZ.t = 64sz
inline_for_extraction let max_signature_schemes_sz : SZ.t = 32sz
inline_for_extraction let max_client_hello_len_sz : SZ.t = 512sz
inline_for_extraction let max_server_hello_len_sz : SZ.t = 4096sz
inline_for_extraction let max_handshake_flight_len_sz : SZ.t = 32768sz
inline_for_extraction let max_transcript_len_sz : SZ.t = 65535sz
inline_for_extraction let max_certificate_verify_input_len_sz : SZ.t = 256sz
inline_for_extraction let max_trust_anchors_len_sz : SZ.t = 65535sz
inline_for_extraction let max_pending_plaintext_len_sz : SZ.t = 32768sz
inline_for_extraction let max_pending_raw_len_sz : SZ.t = 32768sz

(* Executable [SZ.t] companion of [max_server_certificate_chain_len].

   Unlike the [inline_for_extraction] [sz] literals above, this one is kept
   ABSTRACT: it is declared here as a [val] with a refinement pinning its value
   to the authoritative spec bound, and realized once in the [.fst].  The abstract
   [val] means KaRaMeL cannot inline it, so the runtime certificate-chain length
   check in the server driver extracts to a reference to the single named C
   constant [..._max_server_certificate_chain_len_sz] rather than baking the
   literal bound into the driver's C at the check site.

   The refinement [SZ.v c == max_server_certificate_chain_len] lets callers relate
   the runtime check to the spec bound directly, with no separate connecting
   lemma. *)
val max_server_certificate_chain_len_sz
  : c:SZ.t { SZ.v c == max_server_certificate_chain_len }

let option_is_some #a (x:option a) : prop =
  match x with
  | Some _ -> True
  | None -> False

val lemma_option_is_some_some : #a:Type0 -> x:option a -> Lemma (requires option_is_some x) (ensures Some? x)
val lemma_option_is_some_some_imp : #a:Type0 -> x:option a -> b:bool -> Lemma (requires b ==> option_is_some x) (ensures b ==> Some? x)
