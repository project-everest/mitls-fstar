module TestGCM

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


private let pre_id (role:role) =
  let cr  = createBytes 32 0z in
  let sr  = createBytes 32 0z in
  let kdf = PRF_TLS_1p2 kdf_label (HMAC CoreCrypto.SHA256) in
  let gx  = CommonDH.keygen (CommonDH.ECDH CoreCrypto.ECC_P256) in
  let g   = CommonDH.key_params gx in
  let gy, gxy = CommonDH.dh_responder gx in
  let pms = PMS.DHPMS (g, (CommonDH.share_of_key gx), (CommonDH.share_of_key gy), (PMS.ConcreteDHPMS gxy)) in
  let msid = StandardMS pms (cr @| sr) kdf in
  ID12 TLS_1p2 msid kdf (AEAD CoreCrypto.AES_256_GCM CoreCrypto.SHA256) cr sr role

private let id = pre_id Client

#set-options "--lax"

private let encryptRecord (#id:StAE.stae_id) (wr:StAE.writer id) ct plain : bytes =
  let rg: Range.frange id = (0, length plain) in
  let f: DataStream.fragment id rg = plain in
  let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id wr f

private let decryptRecord (#id:StAE.stae_id) (rd:StAE.reader id) ct cipher : option bytes =
  let ctxt: Content.decrypted id = (ct, cipher) in
  match StAE.decrypt #id rd ctxt with
  | Some d -> Some (Content.repr id d)
  | _ -> None

private let text = Platform.Bytes.utf8 "Top secret"

val main : unit -> unit
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
    if text' <> text then
      begin
      IO.print_string ("GCM test: FAIL\n");
      IO.print_string ("Unexpected output: " ^ (iutf8 text') ^ ",\nexpected = " ^ (iutf8 text) ^ "\n");
      failwith "Error!"
      end
    else
      IO.print_string ("GCM test: OK\n")
  | None ->
    IO.print_string ("GCM test: FAIL\n");
    failwith "Error!"
