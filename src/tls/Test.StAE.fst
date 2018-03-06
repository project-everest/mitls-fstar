module Test.StAE
// adapted from test/TestGCM

open FStar.Bytes // for @|
open FStar.Error
open FStar.Printf
open TLSError
open TLSConstants
open TLSInfo
open Range

module StAE = StAE
module Range = Range
module DH = CommonDH

open FStar.HyperStack
open FStar.HyperStack.ST
(*
open FStar.Heap
open FStar.HyperHeap
open FStar.IO

open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open StatefulPlain
open AEAD_GCM
open StatefulLHAE
open StAE
*)

let prefix = "Test.StAE"
let ok: ref bool = ralloc root true

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string (prefix^": "^s^".\n"))
// let print = C.String,print
// let print = FStar.HyperStack.IO.print_string

let eprint s : St unit = ok := false; print ("ERROR: "^s)
let nprint s : St unit = print s

// used in other tests too
private let pre_id (role:role) =
  let cr  = Bytes.create 32ul 0z in
  let sr  = Bytes.create 32ul 0z in
  let kdf = PRF_TLS_1p2 kdf_label (HMac Hashing.Spec.SHA256) in
  let msid = StandardMS PMS.DummyPMS (cr @| sr) kdf in
  ID12 TLS_1p2 msid kdf (AEAD CoreCrypto.AES_256_GCM Hashing.Spec.SHA256) cr sr role

let id12 = pre_id Client

#set-options "--lax"

let id13 =
  let cr  = Bytes.create 32ul 0z in
  let ch0 = {
    li_ch0_cr = cr;
    li_ch0_ed_psk = Bytes.utf8_encode "whatever";
    li_ch0_ed_ae = CoreCrypto.AES_256_GCM;
    li_ch0_ed_hash = Hashing.Spec.SHA256; } in
  let li = LogInfo_CH0 ch0 in
  let i = ExpandedSecret
      (EarlySecretID (NoPSK Hashing.Spec.SHA256))
      ClientEarlyTrafficSecret
      (Bytes.utf8_encode "whatever") in
  let kid: keyId = KeyID #li i in
  ID13 kid


let encryptRecord (#id:StAE.stae_id) (wr:StAE.writer id) ct plain : St bytes =
  let rg: Range.frange id = (length plain, length plain) in
  let f: DataStream.fragment id rg = plain in
  let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id wr f

let decryptRecord (#id:StAE.stae_id) (rd:StAE.reader id) ct cipher : St (option bytes) =
  let ctxt: Content.decrypted id = (ct, cipher) in
  match StAE.decrypt #id rd ctxt with
  | Some d -> Some (Content.repr id d)
  | _ -> None


val test: id:StAE.stae_id -> St unit
let test id =
  let text0 = Bytes.utf8_encode "attack at" in
  let text1 = Bytes.utf8_encode "dawn" in
  // For TLS 1.2, key materials consist of an AES256 key plus 4 bytes of IV salt.
  let key =
    if ID13? id then
    bytes_of_hex (
    "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308"^
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
    else
    bytes_of_hex (
    "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308"^
    "01020304")
    in
  let wr = StAE.coerce root id key in
  let rd = StAE.genReader root #id wr in
  let c0 = encryptRecord #id wr Content.Application_data text0 in
  nprint (sprintf "c0 size=%ul data=%s" (Bytes.len c0) (Bytes.hex_of_bytes c0));
  let c1 = encryptRecord #id wr Content.Application_data text1 in
  nprint (sprintf "c1 size=%ul data=%s" (Bytes.len c1) (Bytes.hex_of_bytes c1));
  nprint "start";
  let c = Bytes.utf8_encode "we need a long-enough ciphertext (static pre)" in
  let d = decryptRecord #id rd Content.Application_data c in

  if None? d
  then nprint "decryption fails on wrong cipher"
  else eprint "decryption should fail";

  let d = decryptRecord #id rd Content.Application_data c1 in
  if None? d
  then nprint "decryption fails on wrong sequence number"
  else eprint "decryption should fail on wrong sequence number";

  if id = id13 then
    nprint "TLS 1.3 does not intend to provide outer CT authentication"
  else (
    let d = decryptRecord #id rd Content.Alert c0 in
    if None? d
    then nprint "decryption fails on wrong CT"
    else eprint "decryption should fail on wrong CT" );

  let d = decryptRecord #id rd Content.Application_data c0 in
  ( match d with
    | Some v ->
      if v = text0
      then nprint "first decryption succeeds"
      else eprint "wrong decrypted message"
    | _ -> eprint "first decryption failed" );

  let d = decryptRecord #id rd Content.Application_data c1 in
  ( match d with
    | Some v ->
      if v = text1
      then nprint "second decryption succeeds"
      else eprint "wrong decrypted message"
    | _ -> eprint "second decryption failed" )

// Called from Test.Main
let main () =
  test id12;
  test id13 ;
  if !ok then C.EXIT_SUCCESS else C.EXIT_FAILURE
