module TestRecord

//
open FStar
open HyperHeap
open STHyperHeap

open TLSConstants
open TLSInfo
open StatefulLHAE

let x = Platform.Bytes.bytes_of_hex
let r = HyperHeap.root

let main =
  // AEAD_GCM.gid -> LHAEPlain.id -> TLSInfo.id
  let id = {
    msId = noMsId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p2;
    aeAlg = AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256; // <- that's the relevant bit! the rest is dummy values 
    csrConn = x"";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_renegotiation_info = None;
      ne_supported_curves = None;
      ne_supported_point_formats = None;
      ne_server_names = None
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
      let key: AEAD_GCM.key id = x"152300c2dc44c8f695d4fb1471791659" |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = x"b56bf932" |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      // FIXME extraction bug: unless I specify the four implicit arguments, F*
      // crashes
      AEAD_GCM.State #id #Writer #r #r key iv log counter
    in
    // FIXME extraction bug: same remark
    State #id #Writer #r #r log seqn key
  in

  let text = x"474554202f20485454502f312e310d0a486f73743a20756e646566696e65640d0a0d0a" in
  // StatefulPlain.adata id -> bytes
  let ad: StatefulPlain.adata id = StatefulPlain.makeAD id Content.Application_data in
  // Range.frange -> Range.range
  let rg: Range.frange id = 0, Platform.Bytes.length text in
  // DataStream.fragment -> DataStream.pre_fragment -> bytes
  let f: DataStream.fragment id rg = text |> unsafe_coerce in
  // LHAEPlain.plain -> StatefulPlain.plain -> Content.fragment
  let f: LHAEPlain.plain id ad rg = Content.CT_Data rg f |> unsafe_coerce in

  // StatefulLHAE.cipher -> StatefulPlain.cipher -> bytes
  // FIXME: without the three additional #-arguments below, extraction crashes
  let c = encrypt #id #ad #rg w f in

  IO.print_string (Platform.Bytes.hex_of_bytes c);
  IO.print_newline ()
  

