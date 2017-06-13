(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
module Ticket

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open Parse
open TLSInfo

module CC = CoreCrypto
module AE = AEADOpenssl
module MM = MonotoneMap
#set-options "--lax"

type hostname = string
type tlabel (h:hostname) = bytes
private let region:rgn = new_region tls_tables_region
private let tickets : MM.t region hostname tlabel (fun _ -> True) =
  MM.alloc #region #hostname #tlabel #(fun _ -> True)

let lookup h = MM.lookup tickets h
let extend h t = MM.extend tickets h t

let ticketid (a:aeadAlg) : St (AE.id) =
  assume false;
  let h = Hashing.Spec.SHA256 in
  let li = LogInfo_CH0 ({
    li_ch0_cr = CC.random 32;
    li_ch0_ed_psk = empty_bytes;
    li_ch0_ed_ae = AEAD a h;
    li_ch0_ed_hash = h;
  }) in
  let log : hashed_log li = empty_bytes in
  ID13 (KeyID #li (ExpandedSecret (EarlySecretID (NoPSK h)) ApplicationTrafficSecret log))

type ticket_key =
  | Key: i:AE.id -> iv:AE.iv i -> wr:AE.writer i -> rd:AE.reader i -> ticket_key

private let ticket_enc
  =
  let id0 = ticketid CC.CHACHA20_POLY1305 in
  let salt : AE.iv id0 = CoreCrypto.random (AE.ivlen id0) in
  let key : AE.key id0 = CoreCrypto.random (AE.keylen id0) in
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

type ticket =
| Ticket12: protocolVersion -> cs:cipherSuite{CipherSuite? cs} -> ms:bytes -> ticket
| Ticket13: cs:cipherSuite{CipherSuite13? cs} -> li:logInfo -> pre_rmsId li -> rms:bytes -> ticket

let dummy_rmsid ae h =
  let li = {
    li_sh_cr = CC.random 32;
    li_sh_sr = CC.random 32;
    li_sh_ae = AEAD ae h;
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

let check_ticket (b:bytes{length b <= 65551}) =
  let Key tid salt _ rd = !ticket_enc in
  if length b < AE.ivlen tid + 7 then None else
  let (nb, b) = split b (AE.ivlen tid) in
  let iv = xor (AE.ivlen tid) nb salt in
  match AE.decrypt #tid #65535 rd iv empty_bytes b with
  | None -> None
  | Some plain ->
    if length plain < 7 then None
    else
      let (pvb, r) = split plain 2 in
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
          | TLS_1p2, CipherSuite _ _ _ -> Some (Ticket12 pv cs rms)

let create_ticket t =
  let Key tid salt wr _ = !ticket_enc in
  let pv, cs, b = match t with
    | Ticket12 pv cs ms -> pv, cs, ms
    | Ticket13 cs _ _ rms -> TLS_1p3, cs, rms in
  let plain = (versionBytes pv) @| (cipherSuiteBytes cs) @| (vlbytes 2 b) in
  let nb = CC.random 12 in
  let iv = xor 12 nb salt in
  let ae = AE.encrypt #tid #65535 wr iv empty_bytes plain in
  nb @| ae

let check_ticket13 b =
  match check_ticket b with
  | Some (Ticket13 cs li _ _) ->
    let CipherSuite13 ae h = cs in
    Some PSK.({
      is_ticket = true;
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
  | Some (Ticket12 pv cs ms) -> Some (pv, cs, ms)
  | _ -> None
