module TestRecord

//
open FStar

open Platform.Bytes

open TLSConstants
open TLSInfo
open StatefulLHAE


let r = HyperHeap.root

let fake_aead (pv: protocolVersion) (aeAlg: aeAlg) (key: string) (iv: string) (plain: string): bytes =
  // AEAD_GCM.gid -> LHAEPlain.id -> TLSInfo.id
  let id = {
    msId = noMsId;
    kdfAlg = PRF_SSL3_nested;
    pv = pv;
    aeAlg = aeAlg; // <- that's the relevant bit! the rest is dummy values 
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_curves = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None;
    };
    writer = Client
  } in

  // StatefulLHAE.writer -> StatefulLHAE.state
  let w: writer id =
    let log: st_log_t r id = ralloc r Seq.createEmpty in
    let seqn: HyperHeap.rref r seqn_t = ralloc r 1 in
    let key: AEAD_GCM.state id Writer =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = bytes_of_hex key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = bytes_of_hex iv |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      AEAD_GCM.State r key iv log counter
    in
    State r log seqn key
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
  StatefulLHAE.encrypt #id #ad #rg w f

let fake_cbc (pv: protocolVersion) (aeAlg: aeAlg) (seqn: seqn_t) (key: string) (iv: string) (plain: string) (macKey: string): bytes =
  // TLSInfo.id
  let id = {
    msId = noMsId;
    kdfAlg = PRF_SSL3_nested;
    pv = pv;
    aeAlg = aeAlg; // <- that's the relevant bit! the rest is dummy values 
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_curves = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None
    };
    writer = Client
  } in

  // ENC.encryptor -> ENC.state
  let w: ENC.encryptor id =
    let key: ENC.key id = bytes_of_hex key in
    let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
    let state: ENC.localState r id =
      let iv: ENC.iv id = bytes_of_hex iv in
      ENC.OldBlockState id iv
    in
    let state: HyperHeap.rref r (ENC.localState r id) = ralloc r state in
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


let test_count = FStar.ST.ralloc r 0

let test_aead (pv: protocolVersion) (aeAlg: aeAlg) (key: string) (iv: string) (plain: string) (cipher: string) =
  let output = fake_aead pv aeAlg key iv plain in
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

let test_cbc (pv: protocolVersion) (aeAlg: aeAlg) (seqn: seqn_t) (key: string) (iv: string) (plain: string) (cipher: string) (macKey: string) =
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

let main () =
  test_aead TLS_1p2 (AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256)
    "152300c2dc44c8f695d4fb1471791659"
    "b56bf932"
    "474554202f20485454502f312e310d0a486f73743a20756e646566696e65640d0a0d0a"
    "0000000000000000ed3ca96c8bd2fbb376c2dc417f3ec249e8ab550dab1c421293f0e642a0c152b43a546a8b49b6128ee6e23454b7e580423ba985";
  test_cbc TLS_1p2 (MtE (Block CoreCrypto.AES_128_CBC) CoreCrypto.SHA1) 1
    "e77f6871e1697b2286416f973aee9ff6"
    "00000000000000000000000000000000"
    "474554202f20485454502f312e310d0a486f73743a20756e646566696e65640d0a0d0a"
    "0000000000000000000000000000000028cf3b38da8358b78aae63e5fcc334c1eac5278a283fa709cb274df85a2a7fa21b767111bc7f73f37cb2697dbb41f903dd2a3e4470767f3cc5e2db1a2e781213"
    "431ad4d620ea0c63bf9afc8124afcae6729593f1";
  ()
