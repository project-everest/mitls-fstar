module TLS.Cookie

open Mem
open FStar.Bytes // for the time being
open TLSConstants
open TLSError

module CH = Parsers.ClientHello

open Parsers.HRRExtension
open Parsers.HRRExtensions
open Parsers.HelloRetryRequest

module Contents = Parsers.MiTLSCookieContents
module Ticket = Ticket



(**
  Debugging flag.
  F* normalizer will erase debug prints at extraction when set to false.
*)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("CKI| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_NGO then print else (fun _ -> ())

let hRRExtensions_list_bytesize_snoc exts e =
  LowParseWrappers.list_bytesize_snoc
    hRRExtension_bytesize
    hRRExtensions_list_bytesize
    ()
    (fun _ _ -> ())
    exts
    e

let prepare_contents (chd:digest) app (hrr: hrr) =
  { Contents.session_id = hrr_session_id hrr;
    Contents.cipher_suite = hrr_cipher_suite hrr;
    Contents.group_share = (
      match find_keyshare hrr with
      | Some g -> [g]
      | None -> []);
    Contents.clientHelloDigest = chd;
    Contents.extra = app }

let print_contents (x:Contents.miTLSCookieContents) =
  let open Contents in
  trace ("session_id="^hex_of_bytes x.session_id);
  trace ("cipher_suite="^Parsers.CipherSuite.string_of_cipherSuite x.cipher_suite);// not cs printer!?
  ( match x.group_share with
  | []  -> trace "no group_share"
  | [g] -> trace ("group_share="^Parsers.NamedGroup.string_of_namedGroup g));
  trace ("clientHelloDigest="^hex_of_bytes x.clientHelloDigest);
  trace ("extra="^hex_of_bytes x.extra)


/// Failures within this code should be prevented by authenticated
/// encryption, since it covers all contents produced above.

let reconstruct_hrr
  (raw: encrypted_cookie)
  (contents: Contents.miTLSCookieContents): result (hrr_leq extensions_max_length)
=
  cs <-- (
    match cipherSuite_of_name contents.Contents.cipher_suite with
    | Some cs ->
      if CipherSuite13? cs then
        Correct cs
      else
        fatal Handshake_failure "invalid cookie contents"
    | _ -> fatal Handshake_failure "invalid cookie contents");
  let hrr = hrr0 contents.Contents.session_id cs in
  hrr <-- (
    match contents.Contents.group_share with
    | [g] -> correct (append_keyshare hrr g)
    | []  -> correct #(hrr_leq 16) hrr
    | _   -> fatal Handshake_failure "invalid cookie contents" );
  correct #(hrr_leq extensions_max_length) (append_extension 16 hrr (HRRE_cookie raw))

let append chd app hrr =
  let plain = Contents.miTLSCookieContents_serializer32 (prepare_contents chd app hrr) in
  // TODO use EverCrypt.AEAD-based TLS.Store instead of Ticket & prove the bounds statically
  let encrypted = Ticket.ticket_encrypt false plain in
  assume (32 <= length encrypted /\ length encrypted <= encrypted_max_length);
  trace ("Plaintext cookie="^hex_of_bytes plain);
  trace ("Encrypted cookie="^hex_of_bytes encrypted);
  append_extension 16 hrr (HRRE_cookie encrypted)

let decrypt encrypted =
  if length encrypted < 32 || length encrypted > encrypted_max_length then
    fatal Decode_error "bad cookie length"
  else (
    // TODO use EverCrypt.AEAD-based TLS.Store instead of Ticket
    match Ticket.ticket_decrypt false encrypted with
    | None -> fatal Decode_error "cookie decryption failed"
    | Some plain ->
      trace ("Decrypted cookie="^hex_of_bytes plain);
      match LowParseWrappers.wrap_parser32 Contents.miTLSCookieContents_parser32 "invalid cookie contents" plain with
      | Correct v -> (
        if DebugFlags.debug_NGO then print_contents v;
        match reconstruct_hrr encrypted v with
        | Correct hrr -> correct(v.Contents.clientHelloDigest, v.Contents.extra, hrr)
        | Error z -> Error z )
      | Error z -> Error z )


/// Basic testing:
/// - unwrapping our own cookies is an identity on (chd,hrr,extra)

#push-options "--z3rlimit 100"

let test() =
  let chd = Bytes.create 16ul 221uy in
  let hrr = hrr0 empty_bytes (CipherSuite13 EverCrypt.AES128_GCM Spec.Hash.Definitions.SHA2_256) in
  let extra = Bytes.create 8ul 204uy in
  let hrr = append chd extra hrr in
  match find_cookie hrr with
  | None -> trace "cookie not found"; false
  | Some c ->
    match decrypt c with
    | Error _ -> trace "decryption failed"; false
    | Correct (chd', extra', hrr') ->
      (chd' = chd && extra' = extra && hrr' = hrr)

#pop-options
