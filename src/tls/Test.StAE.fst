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

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string (prefix^": "^s^".\n"))
// let print = C.String,print
// let print = FStar.HyperStack.IO.print_string

let eprint s = print ("ERROR: "^s)
let nprint s = print s

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

private let id12 = pre_id Client

#set-options "--lax"

private let id13 = 
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


val test: id:StAE.stae_id -> St bool
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
  // how to print bytes? nprint("first encryption is "^c0)
  let c1 = encryptRecord #id wr Content.Application_data text1 in

  nprint "start";
  (
    let c = Bytes.utf8_encode "we need a long-enough ciphertext (static pre)" in 
    let d = decryptRecord #id rd Content.Application_data c in
    if None? d   
    then (nprint "decryption fails on wrong cipher"; true)
    else (eprint "decryption should fail"; false)
  ) &&
  ( let d = decryptRecord #id rd Content.Application_data c1 in
    if None? d   
    then (nprint "decryption fails on wrong sequence number"; true)
    else (eprint "decryption should fail on wrong sequence number"; false)
  ) &&
  ( let d = decryptRecord #id rd Content.Alert c0 in
    if None? d   
    then (nprint "decryption fails on wrong CT"; true)
    else (eprint "decryption should fail on wrong CT"; false)
  ) &&
  ( let d = decryptRecord #id rd Content.Application_data c0 in 
    match d with 
    | Some v ->
      if v = text0 
      then (nprint "first decryption succeeds"; true)
      else (eprint "wrong decrypted message"; false)
    | _ -> eprint ("decryption failed");  false 
  ) &&
  ( let d = decryptRecord #id rd Content.Application_data c1 in 
    match d with 
    | Some v ->
      if v = text1 
      then (nprint "second decryption succeeds"; true)
      else (eprint "wrong decrypted message"; false)
    | _ -> eprint ("decryption failed");  false )

// will need to move to a Kremlin-specific driver
let main() = 
  if test id12 && test id13 then C.EXIT_SUCCESS else C.EXIT_FAILURE 

// will need to move to an Ocaml-specific driver
let _ = 
  if test id12 && test id13 then () else failwith prefix
