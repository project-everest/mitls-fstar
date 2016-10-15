module TestRecord

open Platform.Bytes

open TLSConstants
open TLSInfo
open StatefulLHAE


let r = HyperHeap.root

private let mk_id pv aeAlg =
  let er = createBytes 32 (Char.char_of_int 0) in
  let kdf = match pv with
  | TLS_1p0 -> PRF_SSL3_concat
  | TLS_1p1 -> PRF_TLS_1p01 kdf_label
  | TLS_1p2 -> PRF_TLS_1p2 kdf_label (HMAC CoreCrypto.SHA256) in
  let gx = CommonDH.keygen (CommonDH.ECDH CoreCrypto.ECC_P256) in
  let g = CommonDH.key_params gx in
  let gy, gxy = CommonDH.dh_responder gx in
  let msid = StandardMS (PMS.DHPMS(g, (CommonDH.share_of_key gx), (CommonDH.share_of_key gy), (PMS.ConcreteDHPMS gxy))) (er @| er) kdf in
  ID12 pv msid kdf aeAlg er er Client

private let mk_id13 aeAlg =
  let hash_alg = CoreCrypto.SHA256 in
  let gx = CommonDH.keygen (CommonDH.ECDH CoreCrypto.ECC_P256) in
  let gy,_ = CommonDH.dh_responder gx in
  let initiator = CommonDH.share_of_key gx in
  let responder = CommonDH.share_of_key gy in
  let hsId = HSID_DHE hash_alg initiator responder in
  let asId = ASID hsId in
  let expandId = ApplicationSecretID asId in
  let cr = CoreCrypto.random 32 in
  let sr = CoreCrypto.random 32 in
  let logInfo = LogInfo_SH ({ li_sh_cr = cr; li_sh_sr = sr; li_sh_ae = aeAlg }) in
  let hashed_log = CoreCrypto.random 32 in
  let keyId = KeyID expandId ApplicationDataKey Client logInfo hashed_log in
  ID13 keyId

private val fake_stream: (aeAlg: (a:aeAlg{is_AEAD a})) -> (key:string) -> (iv:string) -> (plain:string) -> bytes
private let fake_stream (aeAlg: (a:aeAlg{is_AEAD a})) (key:string) (iv:string) (plain:string): bytes =
  let id = mk_id13 aeAlg in

  // StreamAE.writer -> StreamAE.state
  let key: StreamAE.key id = bytes_of_hex key |> unsafe_coerce in
  let iv : StreamAE.iv id  = bytes_of_hex iv  |> unsafe_coerce in
  assume (~(authId id));
  let w: StreamAE.writer id = StreamAE.coerce r id key iv in

  let text = bytes_of_hex plain in

  let len: StreamPlain.plainLen = 64 in

  // Range.frange -> Range.range
  let rg: Range.frange id = 0, 64 in

  // DataStream.fragment -> DataStream.pre_fragment -> bytes
  let f: DataStream.fragment id rg = text in

  // StreamPlain.plain -> StreamPlain.plain -> Content.fragment
  let f: StreamPlain.plain id len = Content.CT_Data #id rg f in

  // StreamLHAE.cipher -> StreamPlain.cipher -> bytes
  StreamAE.encrypt #id w len f


private val fake_aead: (pv: protocolVersion) -> (aeAlg: aeAlg) -> (key: string) -> (iv: string) -> (plain: string) -> bytes
private let fake_aead (pv: protocolVersion) (aeAlg: aeAlg) (key: string) (iv: string) (plain: string): bytes =
  let id = mk_id pv aeAlg in

  // StatefulLHAE.writer -> StatefulLHAE.state
  let w: writer id =
    assume (~(authId id));
    let seqn: HyperStack.ref seqn_t = ralloc r 1 in
    let st: AEAD_GCM.state id Writer =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = bytes_of_hex key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = bytes_of_hex iv |> unsafe_coerce in
      (* let log: HyperStack.rref _ = ralloc r Seq.createEmpty in *)
      let counter = ralloc r 0 in
      AEAD_GCM.State #id #Writer #r #r key iv () counter
    in
    st
  in

  let text = bytes_of_hex plain in
  // StatefulPlain.adata id -> bytes
  let ad: StatefulPlain.adata id = StatefulPlain.makeAD id Content.Application_data in
  // Range.frange -> Range.range
  let rg: Range.frange id = 0, length text in
  // DataStream.fragment -> DataStream.pre_fragment -> bytes
  let f: DataStream.fragment id rg = text |> unsafe_coerce in
  // LHAEPlain.plain -> StatefulPlain.plain -> Content.fragment
  //NS: Not sure about the unsafe_coerce: but, it's presence clearly means that #id cannot be inferred
  let f: LHAEPlain.plain id ad rg = Content.CT_Data #id rg f |> unsafe_coerce in

  // StatefulLHAE.cipher -> StatefulPlain.cipher -> bytes
  // FIXME: without the three additional #-arguments below, extraction crashes
  StatefulLHAE.encrypt #id w ad rg f

private val fake_cbc: (pv: protocolVersion) -> (aeAlg: aeAlg) -> (seqn: seqn_t) -> (key: string) -> (iv: string) -> (plain: string) -> (macKey: string) -> bytes
private let fake_cbc (pv: protocolVersion) (aeAlg: aeAlg) (seqn: seqn_t) (key: string) (iv: string) (plain: string) (macKey: string): bytes =
  let id = mk_id pv aeAlg in

  // ENC.encryptor -> ENC.state
  let w: ENC.encryptor id =
    let key: ENC.key id = bytes_of_hex key in
    let log: HyperStack.ref _ = ralloc r Seq.createEmpty in
    let state: ENC.localState r id =
      let iv: ENC.iv id = bytes_of_hex iv in
      ENC.OldBlockState id iv
    in
    let state: HyperStack.ref (ENC.localState r id) = ralloc r state in
    ENC.StateB #id #Writer #r #r key state log
  in

  let text = bytes_of_hex plain in
  // StatefulPlain.adata id -> bytes
  let ad: StatefulPlain.adata id = StatefulPlain.makeAD id Content.Application_data in
  // Prepends sequence number
  let ad = LHAEPlain.makeAD id seqn ad in 
  // Range.frange -> Range.range
  let rg: Range.frange id = 0, length text in
  // DataStream.fragment -> DataStream.pre_fragment -> bytes
  let f: DataStream.fragment id rg = text |> unsafe_coerce in
  // LHAEPlain.plain -> StatefulPlain.plain -> Content.fragment
  let f: LHAEPlain.plain id ad rg = Content.CT_Data #id rg f |> unsafe_coerce in
  let macKey = MAC.coerce id (fun _ -> True) r (bytes_of_hex macKey) in
  let data = Encode.mac id macKey ad rg f in
  bytes_of_hex iv @| ENC.enc id w ad rg data


private let test_count = FStar.ST.ralloc r 0

private val test_stream: a:aeAlg{is_AEAD a} -> (key:string) -> (iv:string) -> (plain:string) -> (cipher:string) -> unit
private let test_stream aeAlg key iv plain cipher =
  let output = fake_stream aeAlg key iv plain in
  let output = hex_of_bytes output in
  if output <> cipher then begin
    IO.print_string ("Unexpected output: iv = " ^ iv ^ ", key = " ^ key ^
        ", plain = " ^ plain ^ ", output = " ^ output ^ ", expected = " ^ cipher ^
        "\n");
    failwith "Error!"
  end else begin
    test_count := !test_count + 1;
    let test_count = string_of_int !test_count in
    IO.print_string ("Encryption test #" ^ test_count ^ ": OK\n")
  end

private val test_aead: (pv: protocolVersion) -> (aeAlg: aeAlg) -> (key: string) -> (iv: string) -> (plain: string) -> (cipher: string) -> unit
private let test_aead (pv: protocolVersion) (aeAlg: aeAlg) (key: string) (iv: string) (plain: string) (cipher: string) =
  let output = fake_aead pv aeAlg key iv plain in
  let output = hex_of_bytes output in
  if output <> cipher then begin
    IO.print_string ("Unexpected output: iv = " ^ iv ^ ", key = " ^ key ^
        ", plain = " ^ plain ^ "\n output   = " ^ output ^ "\n expected = " ^ cipher ^
        "\n");
    failwith "Error!"
  end else begin
    test_count := !test_count + 1;
    let test_count = string_of_int !test_count in
    IO.print_string ("Encryption test #" ^ test_count ^ ": OK\n")
  end

private val test_cbc: (pv: protocolVersion) -> (aeAlg: aeAlg) -> (seqn: seqn_t) -> (key: string) -> (iv: string) -> (plain: string) -> (cipher: string) -> (macKey: string) -> unit
private let test_cbc (pv: protocolVersion) (aeAlg: aeAlg) (seqn: seqn_t) (key: string) (iv: string) (plain: string) (cipher: string) (macKey: string) =
  let output = fake_cbc pv aeAlg seqn key iv plain macKey in
  let output = hex_of_bytes output in
  if output <> cipher then begin
    IO.print_string ("Unexpected output: iv = " ^ iv ^ ", key = " ^ key ^
        ", plain = " ^ plain ^ ",\noutput   = " ^ output ^ ",\nexpected = " ^ cipher ^
        "\n");
    failwith "Error!"
  end else begin
    test_count := !test_count + 1;
    let test_count = string_of_int !test_count in
    IO.print_string ("Encryption test #" ^ test_count ^ ": OK\n")
  end

val main : unit -> unit
let main () =
  test_stream (AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256)
    "152300c2dc44c8f695d4fb1471791659"
    "b56bf932b56bf932ffffffff"
    "474554202f20485454502f312e310d0a486f73743a20756e646566696e65640d0a0d0a"
    "bd324f59c8ff0eb7fcdc519e0fd84203fbc1efcdca0c7f3160d8856cebe3e340fedc8ea409093a847e9b8d5863bf5a4899d453e11447de6f0068341625120b0d9b03b57595a74fb89d7a6ae6bdb7b3ac";
  test_aead TLS_1p2 (AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256)
    "152300c2dc44c8f695d4fb1471791659"
    "b56bf932"
    "474554202f20485454502f312e310d0a486f73743a20756e646566696e65640d0a0d0a"
    "0000000000000000ed3ca96c8bd2fbb376c2dc417f3ec249e8ab550dab1c421293f0e642a0c152b43a546aa26bbe62e8651214d28ab90e70217b3d";
  test_cbc TLS_1p2 (MtE (Block CoreCrypto.AES_128_CBC) CoreCrypto.SHA1) 1
    "e77f6871e1697b2286416f973aee9ff6"
    "00000000000000000000000000000000"
    "474554202f20485454502f312e310d0a486f73743a20756e646566696e65640d0a0d0a"
    "0000000000000000000000000000000028cf3b38da8358b78aae63e5fcc334c1eac5278a283fa709cb274df85a2a7fa21b767111bc7f73f37cb2697dbb41f903dd2a3e4470767f3cc5e2db1a2e781213"
    "431ad4d620ea0c63bf9afc8124afcae6729593f1";
  ()
