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
#set-options "--lax"

private let region:rgn = new_region tls_tables_region
let tid =
  assume false;
  let h = Hashing.Spec.SHA256 in
  let li = LogInfo_CH0 ({
    li_ch0_cr = CC.random 32;
    li_ch0_ed_psk = empty_bytes;
    li_ch0_ed_ae = AEAD CC.CHACHA20_POLY1305 h;
    li_ch0_ed_hash = h;
  }) in
  let log : hashed_log li = empty_bytes in
  ID13 (KeyID #li (ExpandedSecret (EarlySecretID (NoPSK h)) ApplicationTrafficSecret log))

// ADL TODO: add config setting for ticket keys
private let ticket_enc = AE.gen tid region
private let ticket_dec = AE.genReader region ticket_enc
private let nonce = CC.random 12
private let ctr = ralloc region 0

type ticket =
| Ticket12: protocolVersion -> cs:cipherSuite{CipherSuite? cs} -> pms:bytes -> ticket
| Ticket13: cs:cipherSuite{CipherSuite13? cs} -> li:logInfo -> pre_rmsId li -> rms:bytes -> ticket

let check_ticket (b:bytes{length b <= 65551}) =
  if length b < 28 then None else
  let (nb, b) = split b 12 in
  let iv = xor 12 nb salt in
  match AE.decrypt #tid #65535 ticket_dec iv empty_bytes b with
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
            let rmsId = RMSID (ASID (Salt (EarlySecretID (NoPSK h)))) log in
            Some (Ticket13 cs li rmsId rms)
          | TLS_1p2, CipherSuite _ _ _ -> Some (Ticket12 pv cs rms)

let create_ticket t =
  let pv, cs, b = match t with
    | Ticket12 pv cs pms -> pv, cs, pms
    | Ticket13 cs _ _ rms -> TLS_1p3, cs, rms in
  let plain = (versionBytes pv) @| (cipherSuiteBytes cs) @| (vlbytes 2 b) in
  let nb = bytes_of_int 12 !ctr in
  ctr := !ctr + 1;
  let iv = xor 12 nb nonce in
  let ae = AE.encrypt #tid #65535 ticket_enc iv empty_bytes plain in
  nb @| ae

let check_ticket13 b =
  match check_ticket b with
  | Some (Ticket13 cs li _ _) ->
    let CipherSuite13 ae h = cs in
    Some PSK.({
      time_created = 0;
      allow_early_data = true;
      allow_dhe_resumption = true;
      allow_psk_resumption = true;
      early_ae = ae;
      early_hash = h;
      identities = (empty_bytes, empty_bytes);
    })
  | _ -> None
