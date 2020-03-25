module TLS.Cookie

/// Defines stateless retry processing from the server's viewpoint:
///
/// * When issuing a HelloRetryRequest, the server embeds an encrypted
///   cookie for authenticating the first exchange together with some
///   application context.
///
/// * When receiving a ClientHello with a cookie, the server uses it
///   to reconstruct this first exchange, check that the ClientHello
///   complies with its earlier request, and extend its transcript
///   accordingly.
///
/// The encrypted contents of these cookies is implementation
/// specific: see Parsers.MiTLSCookieContents in Parsers.rfc

open Mem
open FStar.Bytes // for the time being
open TLSConstants
open TLS.Result

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

/// Our server implementation uses relatively short cookies This bound
/// is specific to our server implementation, shorter than the RFC's,
/// and probably much larger than what's used in practice. The HRRs
/// are slighly larger.

type extra = Parsers.MiTLSCookieContents_extra.miTLSCookieContents_extra // [ <= Parsers.MiTLSCookieContents_extra.max_len ]
// aka TLS.Callbacks.cookie, earlier in dependencies

inline_for_extraction noextract let contents_max_length = 32872

inline_for_extraction noextract let encrypted_max_length = contents_max_length + 32 // with IV and tag

type encrypted_cookie = c:Parsers.Cookie.cookie {Bytes.length c <= encrypted_max_length}

inline_for_extraction noextract let extensions_max_length = encrypted_max_length + 24 // upper bound for 3 extensions

open HandshakeMessages
open Parsers.HRRExtension
open Parsers.HRRExtensions
// open Parsers.HelloRetryRequest

/// Base contents of all HRR messages produced by our server, with a
/// convenient refinement on its ciphersuite.
///
/// The only potentially-large part of HRR is the encrypted-cookie
/// extension, added last; for the rest we use small static bounds

type hrr13 = x:hrr {
  match cipherSuite_of_name (hrr_cipher_suite x) with
  | Some (CipherSuite13 _ _) -> True
  | _ -> False }
let hrr_ha (x:hrr13) =
  match cipherSuite_of_name (hrr_cipher_suite x) with
  | Some (CipherSuite13 _ ha) -> ha

let hrr_len (x:hrr) = hRRExtensions_bytesize (hrr_extensions x)
type hrr_leq (n:nat) = x:hrr13 { hrr_len x <= n }

let hrr0 sid (cs: cipherSuite13): hrr_leq 8 =
  mk_hrr TLS_1p2 sid (name_of_cipherSuite cs) [ HRRE_supported_versions TLS_1p3 ]

val hRRExtensions_list_bytesize_snoc
  (exts: list hRRExtension)
  (e: hRRExtension)
: Lemma
  (hRRExtensions_list_bytesize (exts `List.append` [e]) == hRRExtensions_list_bytesize exts + hRRExtension_bytesize e)

noextract
inline_for_extraction
let append_extension
  (n: nat)
  (hrr: hrr_leq n)
  (ext: hRRExtension{ n + hRRExtension_bytesize ext <= extensions_max_length }) :
  hrr_leq (n + hRRExtension_bytesize ext)
=
  let exts = hrr_extensions hrr @ [ext] in
  hRRExtensions_list_bytesize_snoc (hrr_extensions hrr) ext;
  mk_hrr (hrr_version hrr) (hrr_session_id hrr) (hrr_cipher_suite hrr) exts

let find_keyshare (hrr: hrr) : option Parsers.NamedGroup.namedGroup =
  match List.Tot.find HRRE_key_share? (hrr_extensions hrr) with
  | Some (HRRE_key_share g) -> Some g
  | _ -> None

let find_cookie (hrr: hrr) : option Parsers.Cookie.cookie =
  match List.Tot.find HRRE_cookie? (hrr_extensions hrr) with
  | Some (HRRE_cookie g) -> Some g
  | _ -> None

let append_keyshare (hrr: hrr_leq 8) (g:Parsers.NamedGroup.namedGroup): hrr_leq 16 =
  append_extension 8 hrr (HRRE_key_share g)

type digest = Parsers.MiTLSCookieContents_clientHelloDigest.miTLSCookieContents_clientHelloDigest

/// The main cookie producers and consumers. This function computes
/// and formats the cookie contents, encrypts it using the current
/// cookie key, and appends it to the HRR The input HRR does not yet
/// include the cookie, and is known to be short and simple. Will be
/// lowered to code that directly outputs the encrypted cookie in the
/// output buffer.

val append:
  chd: digest ->
  app: extra ->
  hrr: hrr_leq 16 ->
  ST (hrr_leq (extensions_max_length))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> B.(modifies loc_none h0 h1))

/// Conversely, this function takes an encrypted cookie (possibly too
/// large) and reconstructs the HRR (for transcript hashing) using
/// both the raw cookie and its decrypted contents.

val decrypt:
  Parsers.Cookie.cookie ->
  ST (result (digest & extra & hrr_leq extensions_max_length))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    B.(modifies loc_none h0 h1))

// TODO idealization using a global table. Unclear how to associate a
// "global" authenticated predicate in the presence of key updates. We
// may need extra parameters, such as the initial client hello and
// server configuration.

val test: unit -> ST bool
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> B.(modifies loc_none h0 h1))
