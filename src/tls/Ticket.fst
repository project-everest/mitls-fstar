module Ticket

open Platform.Bytes
open FStar.Error

open Mem
open TLSError
open TLSConstants
open Parse
open TLSInfo

module CC = CoreCrypto
module AE = AEADOpenssl
module MM = FStar.Monotonic.Map
#set-options "--lax"

type hostname = string
type tlabel (h:hostname) = t:bytes * tls13:bool
private let region:rgn = new_region tls_tables_region
private let tickets : MM.t region hostname tlabel (fun _ -> True) =
  MM.alloc #region #hostname #tlabel #(fun _ -> True)

let lookup (h:hostname) = MM.lookup tickets h
let extend (h:hostname) (t:tlabel h) = MM.extend tickets h t

type session12 (tid:bytes) = protocolVersion * cipherSuite * ems:bool * msId * ms:bytes
private let sessions12 : MM.t region bytes session12 (fun _ -> True) =
  MM.alloc #region #bytes #session12 #(fun _ -> True)

let s12_lookup (tid:bytes) = MM.lookup sessions12 tid
let s12_extend (tid:bytes) (s:session12 tid) = MM.extend sessions12 tid s

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
  | Key: i:AE.id -> iv:AE.iv i -> wr:AE.writer i -> rd:AE.reader i -> ticket_key

private let ticket_enc: ref ticket_key
  =
  let id0 = ticketid CC.CHACHA20_POLY1305 in
  let salt: AE.iv id0 = CoreCrypto.random (AE.ivlen id0) in
  let key: AE.key id0 = CoreCrypto.random (AE.keylen id0) in
  let wr = AE.coerce region id0 key in
  let rd = AE.genReader region #id0 wr in
  ralloc region (Key id0 salt wr rd)

let set_ticket_key (a:aeadAlg) (kv:bytes) : St (bool) =
  let tid = ticketid a in
  if length kv = AE.keylen tid + AE.ivlen tid then
    let k, s = split kv (AE.keylen tid) in
    let wr = AE.coerce region tid k in
    let rd = AE.genReader region wr in
    ticket_enc := Key tid s wr rd; true
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
    let (pvb, r) = split b 2 in
    match parseVersion pvb with
    | Error _ -> None
    | Correct pv ->
      let (csb, r) = split r 2 in
      match parseCipherSuite csb, vlparse 2 r with
      | Error _, _ -> None
      | _, Error _ -> None
      | Correct cs, Correct rms ->
        match pv, cs with
        | TLS_1p3, CipherSuite13 ae h ->
          let (| li, rmsId |) = dummy_rmsid ae h in
          Some (Ticket13 cs li rmsId rms)
        | TLS_1p2, CipherSuite _ _ _ ->
          let (emsb, ms) = split rms 1 in
          let ems = 0z <> cbyte emsb in
          let msId = dummy_msId pv cs ems in
          Some (Ticket12 pv cs ems msId ms)

let check_ticket (b:bytes{length b <= 65551}) =
  let Key tid salt _ rd = !ticket_enc in
  if length b < AE.ivlen tid + AE.taglen tid + 8 then None else
  let (nb, b) = split b (AE.ivlen tid) in
  let iv = xor (AE.ivlen tid) nb salt in
  match AE.decrypt #tid #65535 rd iv empty_bytes b with
  | None -> None
  | Some plain -> parse plain

let serialize t =
  let pv, cs, b = match t with
    | Ticket12 pv cs ems _ ms -> pv, cs, abyte (if ems then 1z else 0z) @| ms
    | Ticket13 cs _ _ rms -> TLS_1p3, cs, rms in
  (versionBytes pv) @| (cipherSuiteBytes cs) @| (vlbytes 2 b)

let create_ticket t =
  let Key tid salt wr _ = !ticket_enc in
  let plain = serialize t in
  let nb = CC.random 12 in
  let iv = xor 12 nb salt in
  let ae = AE.encrypt #tid #65535 wr iv empty_bytes plain in
  nb @| ae

let check_ticket13 b =
  match check_ticket b with
  | Some (Ticket13 cs li _ _) ->
    let CipherSuite13 ae h = cs in
    let nonce, _ = split b 12 in
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
