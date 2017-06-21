module TestGCM

open Mem
open Mem
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

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("TestKS| "^s^"\n"))


private let pre_id (role:role) =
  let cr  = createBytes 32 0z in
  let sr  = createBytes 32 0z in
  let kdf = PRF_TLS_1p2 kdf_label (HMac Hashing.Spec.SHA256) in
  let Some g = CommonDH.group_of_namedGroup (SEC CoreCrypto.ECC_P256) in
  let gx  = CommonDH.keygen g in
  let gy, gxy = CommonDH.dh_responder #g (CommonDH.pubshare gx) in
  let pms = PMS.DHPMS g (CommonDH.pubshare gx) gy (PMS.ConcreteDHPMS gxy) in
  let msid = StandardMS pms (cr @| sr) kdf in
  ID12 TLS_1p2 msid kdf (AEAD CoreCrypto.AES_256_GCM Hashing.Spec.SHA256) cr sr role

private let id = pre_id Client

#set-options "--lax"

private let encryptRecord (#id:StAE.stae_id) (wr:StAE.writer id) ct plain : ML bytes =
  let rg: Range.frange id = (0, length plain) in
  let f: DataStream.fragment id rg = plain in
  let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id wr f

private let decryptRecord (#id:StAE.stae_id) (rd:StAE.reader id) ct cipher : ML (option bytes) =
  let ctxt: Content.decrypted id = (ct, cipher) in
  match StAE.decrypt #id rd ctxt with
  | Some d -> Some (Content.repr id d)
  | _ -> None

private let text = Platform.Bytes.utf8 "Top secret"

val main : unit -> ML unit
let main () =
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
  | Some text' ->
    if (iutf8 text') <> (iutf8 text) then
      begin
      print ("GCM test: FAIL\n");
      print ("Unexpected output: " ^ (iutf8 text') ^ ",\nexpected = " ^ (iutf8 text) ^ "\n");
      failwith "Error!"
      end
    else
      print ("GCM test: OK\n")
  | None ->
    print ("GCM test: FAIL\n");
    failwith "Error!"
