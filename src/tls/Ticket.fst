module Ticket

open FStar.Heap

open FStar.HyperStack

open FStar.Bytes
open FStar.Error
open TLSError
open TLSConstants
open Parse
open TLSInfo

module CC = CoreCrypto
module AE = AEADProvider
module MM = FStar.Monotonic.DependentMap

#set-options "--lax"

private let region:rgn = new_region tls_tables_region

let ticketid (a:aeadAlg) : St (AE.id) =
  assume false;
  let h = Hashing.Spec.SHA256 in
  let li = LogInfo_CH0 ({
    li_ch0_cr = CC.random 32;
    li_ch0_ed_psk = empty_bytes;
    li_ch0_ed_ae = a;
    li_ch0_ed_hash = h;
  }) in
  let log : hashed_log li = empty_bytes in
  ID13 (KeyID #li (ExpandedSecret (EarlySecretID (NoPSK h)) ApplicationTrafficSecret log))

type ticket_key =
  | Key: i:AE.id -> wr:AE.writer i -> rd:AE.reader i -> ticket_key

private let ticket_enc : reference ticket_key
  =
  let id0 = ticketid CC.CHACHA20_POLY1305 in
  let salt : AE.salt id0 = CoreCrypto.random (AE.iv_length id0) in
  let key : AE.key id0 = CoreCrypto.random (AE.key_length id0) in
  let wr = AE.coerce id0 region key salt in
  let rd = AE.genReader region #id0 wr in
  ralloc region (Key id0 wr rd)

let set_ticket_key (a:aeadAlg) (kv:bytes) : St (bool) =
  let tid = ticketid a in
  if length kv = AE.key_length tid + AE.iv_length tid then
    let k, s = split_ kv (AE.key_length tid) in
    let wr = AE.coerce tid region k s in
    let rd = AE.genReader region wr in
    ticket_enc := Key tid wr rd; true
  else false

// TODO absolute bare bone for functionality
// We should expand with certificates, mode, etc
type ticket =
  // 1.2 ticket
  | Ticket12:
    pv: protocolVersion ->
    cs: cipherSuite{CipherSuite? cs} ->
    ems: bool ->
    msId: msId ->
    ms: bytes ->
    ticket
  // 1.3 RMS PSK
  | Ticket13:
    cs: cipherSuite{CipherSuite13? cs} ->
    li: logInfo ->
    rmsId: pre_rmsId li ->
    rms: bytes ->
    ticket

// Currently we use dummy indexes until we can serialize them properly
let dummy_rmsid ae h =
  let li = {
    li_sh_cr = CC.random 32;
    li_sh_sr = CC.random 32;
    li_sh_ae = ae;
    li_sh_hash = h;
    li_sh_psk = None;
  } in
  let li = LogInfo_CF ({
    li_cf_sf = ({ li_sf_sh = li; li_sf_certificate = None; });
    li_cf_certificate = None;
  }) in
  let log : hashed_log li = empty_bytes in
  let i : rmsId li = RMSID (ASID (Salt (EarlySecretID (NoPSK h)))) log in
  (| li, i |)

// Dummy msId TODO serialize and encrypt them properly
let dummy_msId pv cs ems =
  StandardMS PMS.DummyPMS (CC.random 64) (kefAlg pv cs ems)

let parse (b:bytes) =
  if length b < 8 then None
  else
    let (pvb, r) = split b 2ul in
    match parseVersion pvb with
    | Error _ -> None
    | Correct pv ->
      let (csb, r) = split r 2ul in
      match parseCipherSuite csb, vlparse 2 r with
      | Error _, _ -> None
      | _, Error _ -> None
      | Correct cs, Correct rms ->
        match pv, cs with
        | TLS_1p3, CipherSuite13 ae h ->
          let (| li, rmsId |) = dummy_rmsid ae h in
          Some (Ticket13 cs li rmsId rms)
        | TLS_1p2, CipherSuite _ _ _ ->
          let (emsb, ms) = split rms 1ul in
          let ems = 0z <> emsb.[0ul] in
          let msId = dummy_msId pv cs ems in
          Some (Ticket12 pv cs ems msId ms)

let check_ticket (b:bytes{length b <= 65551}) =
  let Key tid _ rd = !ticket_enc in
  let salt = AE.salt_of_state rd in
  if length b < AE.iv_length tid + AE.taglen tid + 8 then None else
  let (nb, b) = split_ b (AE.iv_length tid) in
  let iv = AE.coerce_iv tid (xor_ #(AE.iv_length tid) nb salt) in
  match AE.decrypt #tid #(length b) rd iv empty_bytes b with
  | None -> None
  | Some plain -> parse plain

let serialize t =
  let pv, cs, b = match t with
    | Ticket12 pv cs ems _ ms -> pv, cs, abyte (if ems then 1z else 0z) @| ms
    | Ticket13 cs _ _ rms -> TLS_1p3, cs, rms in
  (versionBytes pv) @| (cipherSuiteBytes cs) @| (vlbytes 2 b)

let create_ticket t =
  let Key tid wr _ = !ticket_enc in
  let plain = serialize t in
  let nb = CC.random 12 in
  let salt = AE.salt_of_state wr in
  let iv = AE.coerce_iv tid (xor 12ul nb salt) in
  let ae = AE.encrypt #tid #(length plain) wr iv empty_bytes plain in
  nb @| ae

let check_ticket13 b =
  match check_ticket b with
  | Some (Ticket13 cs li _ _) ->
    let CipherSuite13 ae h = cs in
    let nonce, _ = split b 12ul in
    Some PSK.({
      ticket_nonce = Some nonce;
      time_created = 0;
      allow_early_data = true;
      allow_dhe_resumption = true;
      allow_psk_resumption = true;
      early_ae = ae;
      early_hash = h;
      identities = (empty_bytes, empty_bytes);
    })
  | _ -> None

let check_ticket12 b =
  match check_ticket b with
  | Some (Ticket12 pv cs ems msId ms) -> Some (pv, cs, ems, msId, ms)
  | _ -> None
