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

let prepare_contents (chd:digest) app (hrr: helloRetryRequest) =
  { Contents.session_id = hrr.session_id;
    Contents.cipher_suite = hrr.cipher_suite;
    Contents.group_share = (
      match find_keyshare hrr with
      | Some g -> [g]
      | None -> []);
    Contents.clientHelloDigest = chd;
    Contents.extra = app }


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
  // TODO encrypt
  let encrypted = Contents.miTLSCookieContents_serializer32 (prepare_contents chd app hrr) in
  append_extension 16 hrr (HRRE_cookie encrypted)

let decrypt encrypted =
  // TODO decrypt
  if length encrypted > encrypted_max_length then
    fatal Handshake_failure "oversized cookie"
  else
  match Contents.miTLSCookieContents_parser32 encrypted with
  | Some (v,0ul) -> (
    match reconstruct_hrr encrypted v with
    | Correct hrr -> correct(v.Contents.clientHelloDigest, v.Contents.extra, hrr)
    | Error z -> Error z )
  | _ -> fatal Handshake_failure "invalid cookie contents"



/// Basic testing---how do I run it?

// Can we get rid of Evercrypt.algs??

let test() =
  let chd = empty_bytes in
  let hrr = hrr0 empty_bytes (CipherSuite13 EverCrypt.AES128_GCM Spec.Hash.Definitions.SHA2_256) in
  let extra = empty_bytes in
  let hrr = append chd extra hrr in
  match find_cookie hrr with
  | None -> false
  | Some c ->
    match decrypt c with
    | Error _ -> false
    | Correct (chd', extra', hrr') ->
      (chd' = chd && extra' = extra && hrr' = hrr)





// TODO restore debug trace; see below.

(*
  let hrm = HandshakeMessages.HelloRetryRequest hrr in
  let hrb = vlbytes 3 (HandshakeMessages.handshakeMessageBytes None hrm) in
  let plain = hrb @| (vlbytes 1 digest) @| (vlbytes 2 extra) in
  let cipher = ticket_encrypt false plain in
  trace ("Encrypting cookie: "^(hex_of_bytes plain));
  trace ("Encrypted cookie:  "^(hex_of_bytes cipher));
  cipher
*)

(*
  trace ("Decrypting cookie "^(hex_of_bytes b));
  if length b < 32 then None else
  match ticket_decrypt false b with
  | None -> trace ("Cookie decryption failed."); None
  | Some plain ->
    trace ("Plain cookie: "^(hex_of_bytes plain));
    match vlsplit 3 plain with
    | Error _ -> trace ("Cookie decode error: HRR"); None
    | Correct (hrb, b) ->
      let (_, hrb) = split hrb 4ul in // Skip handshake tag and vlbytes 3
      match HandshakeMessages.parseHelloRetryRequest hrb with
      | Error (_, m) -> trace ("Cookie decode error: parse HRR, "^m); None
      | Correct hrr ->
        match vlsplit 1 b with
        | Error _ -> trace ("Cookie decode error: digest"); None
        | Correct (digest, b) ->
          match vlparse 2 b with
          | Error _ -> trace ("Cookie decode error: application data"); None
          | Correct extra ->
            Some (hrr, digest, extra)
*)
