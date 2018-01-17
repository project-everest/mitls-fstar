module Test.StAE 
// adapted from test/TestGCM

open FStar.Bytes // for @| 
open FStar.Error
open TLSError
open TLSConstants
open TLSInfo
open Range

module StAE = StAE 
module Range = Range

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
let eprint s = FStar.HyperStack.IO.print_string (prefix^": ERROR: "^s^"\n")
let nprint s = FStar.HyperStack.IO.print_string (prefix^": "^s^"\n")

private let pre_id (role:role) =
  let cr  = Bytes.create 32ul 0z in
  let sr  = Bytes.create 32ul 0z in
  let kdf = PRF_TLS_1p2 kdf_label (HMac Hashing.Spec.SHA256) in
  let Some g = CommonDH.group_of_namedGroup (SEC CoreCrypto.ECC_P256) in
  let gx  = CommonDH.keygen g in
  let gy, gxy = CommonDH.dh_responder #g (CommonDH.pubshare gx) in
  let pms = PMS.DHPMS g (CommonDH.pubshare gx) gy (PMS.ConcreteDHPMS gxy) in
  let msid = StandardMS pms (cr @| sr) kdf in
  ID12 TLS_1p2 msid kdf (AEAD CoreCrypto.AES_256_GCM Hashing.Spec.SHA256) cr sr role

private let id = pre_id Client

#set-options "--lax"

private let encryptRecord (#id:StAE.stae_id) (wr:StAE.writer id) ct plain : St bytes =
  let rg: Range.frange id = (0, length plain) in
  let f: DataStream.fragment id rg = plain in
  let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id wr f

private let decryptRecord (#id:StAE.stae_id) (rd:StAE.reader id) ct cipher : St (option bytes) =
  let ctxt: Content.decrypted id = (ct, cipher) in
  match StAE.decrypt #id rd ctxt with
  | Some d -> Some (Content.repr id d)
  | _ -> None

private let text = Bytes.utf8_encode "Top secret"

val main : unit -> St C.exit_code
let main() = 
  //let wr = StAE.gen root id in

  // For TLS 1.2, key materials consist of an AES256 key plus 4 bytes of IV salt.
  let key = bytes_of_hex ("feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308" ^ "01020304") in
  let wr = StAE.coerce root id key in
  let rd = StAE.genReader root #id wr in
  let ct = Content.Application_data in
  let c = encryptRecord #id wr ct text in
  //print_string ("Encrypted: " ^ (iutf8 c) ^ "\n");
  let d = decryptRecord #id rd ct c in
  match d with
  | None -> 
      eprint ("decryption failed.\n");
      C.EXIT_FAILURE 
  | Some text' ->
    if not(text = text') then (
      eprint ("wrong decrypted message.\n");
      eprint("  expected "^Bytes.hex_of_bytes text^ "\n");
      eprint ("  decrypted "^Bytes.hex_of_bytes text'^"\n");
      C.EXIT_FAILURE)
    else (
      nprint ("OK.\n");
      C.EXIT_SUCCESS )

// will need to move to an Ocaml-specific driver
let _ = 
  if main() = C.EXIT_FAILURE then failwith prefix else ()
