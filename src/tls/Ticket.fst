module Ticket

open FStar.Bytes
open FStar.Error

open Mem
open Parse
open TLSError
open TLSConstants
open TLSInfo

module CC = CoreCrypto
module AE = AEADProvider
module MM = FStar.Monotonic.DependentMap

#set-options "--lax"

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("TCK| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_NGO then print else (fun _ -> ())

// verification-only
type hostname = string
type tlabel (h:hostname) = t:bytes * tls13:bool
private let region:rgn = new_region tls_tables_region
private let tickets : MM.t region hostname tlabel (fun _ -> True) =
  MM.alloc () // #region #hostname #tlabel #(fun _ -> True)

let ticketid (a:aeadAlg) : St AE.id =
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

private let dummy_id (a:aeadAlg) : St AE.id =
  assume false;
  let h = Hashing.Spec.SHA256 in
  let li = LogInfo_CH0 ({
    li_ch0_cr = Bytes.create 32ul 0z;
    li_ch0_ed_psk = empty_bytes;
    li_ch0_ed_ae = a;
    li_ch0_ed_hash = h;
  }) in
  let log : hashed_log li = empty_bytes in
  ID13 (KeyID #li (ExpandedSecret (EarlySecretID (NoPSK h)) ApplicationTrafficSecret log))

// The ticket encryption key is a module global, but it must be lazily initialized
// because the RNG may not yet be seeded when kremlinit_globals is called
private let ticket_enc : reference (option ticket_key) = ralloc region None

private let keygen(): St ticket_key  =
  let id0 = dummy_id CC.CHACHA20_POLY1305 in
  let salt : AE.salt id0 = CC.random (AE.iv_length id0) in
  let key : AE.key id0 = CC.random (AE.key_length id0) in
  let wr = AE.coerce id0 region key salt in
  let rd = AE.genReader region #id0 wr in
  Key id0 wr rd

let get_ticket_key () : St ticket_key =
  match !ticket_enc with
  | Some k -> k
  | None ->
    let k = keygen () in
    ticket_enc := Some k; k

let set_ticket_key (a:aeadAlg) (kv:bytes) : St bool =
  let tid = ticketid a in
  if length kv = AE.key_length tid + AE.iv_length tid then
    let k, s = split_ kv (AE.key_length tid) in
    let wr = AE.coerce tid region k s in
    let rd = AE.genReader region wr in
    ticket_enc := Some (Key tid wr rd); true
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
    ticket_created: UInt32.t ->
    ticket_age_add: UInt32.t ->
    ticket

// Currently we use dummy indexes until we can serialize them properly
let dummy_rmsid ae h =
  let li = {
    li_sh_cr = Bytes.create 32ul 0z;
    li_sh_sr = Bytes.create 32ul 0z;
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
  StandardMS PMS.DummyPMS (Bytes.create 64ul 0z) (kefAlg pv cs ems)

let parse (b:bytes) =
  trace ("Parsing ticket "^(hex_of_bytes b));
  if length b < 8 then None
  else
    let (pvb, r) = split b 2ul in
    match parseVersion pvb with
    | Error _ -> None
    | Correct pv ->
      let (csb, r) = split r 2ul in
      match parseCipherSuite csb, vlparse 2 r with
      | _, Error _ -> None
      | Error _, _ -> None
      | Correct cs, Correct rms ->
        match pv, cs with
        | TLS_1p3, CipherSuite13 ae h ->
            let created, rms = split rms 4ul in
            let age_add, rms = split rms 4ul in
            let (| li, rmsId |) = dummy_rmsid ae h in
            let age_add = uint32_of_bytes age_add in
            let created = uint32_of_bytes created in
            Some (Ticket13 cs li rmsId rms created age_add)
        | _, CipherSuite _ _ _ ->
            let emsb, ms = split rms 1ul in
            let ems = 0z <> emsb.[0ul] in
            let msId = dummy_msId pv cs ems in
            Some (Ticket12 pv cs ems msId ms)
        | _ -> None

let ticket_decrypt cipher : St (option bytes) =
  let Key tid _ rd = get_ticket_key () in
  let salt = AE.salt_of_state rd in
  let (nb, b) = split_ cipher (AE.iv_length tid) in
  let plain_len = length b - AE.taglen tid in
  let iv = AE.coerce_iv tid (xor_ #(AE.iv_length tid) nb salt) in
  AE.decrypt #tid #plain_len rd iv empty_bytes b

let check_ticket (b:bytes{length b <= 65551}) : St (option bytes) =
  trace ("Decrypting ticket "^(hex_of_bytes b));
  if length b < AE.iv_length tid + AE.taglen tid + 8 (*was: 32*) 
  then None 
  else
    match ticket_decrypt b with
    | None -> trace ("Ticket decryption failed."); None
    | Some plain -> parse plain

let serialize t =
  let pv, cs, b = match t with
    | Ticket12 pv cs ems _ ms ->
      pv, cs, abyte (if ems then 1z else 0z) @| ms
    | Ticket13 cs _ _ rms created age ->
      TLS_1p3, cs, (bytes_of_int32 created @| bytes_of_int32 age @| rms)
    in
  (versionBytes pv) @| (cipherSuiteBytes cs) @| (vlbytes 2 b)

let ticket_encrypt plain =
  let Key tid wr _ = get_ticket_key () in
  let nb = CC.random (AE.iv_length tid) in
  let salt = AE.salt_of_state wr in
  let iv = AE.coerce_iv tid (xor 12ul nb salt) in
  let ae = AE.encrypt #tid #(length plain) wr iv empty_bytes plain in
  nb @| ae

let create_ticket t =
  let plain = serialize t in
  ticket_encrypt plain

let create_cookie (hrr:HandshakeMessages.hrr) (digest:bytes) (extra:bytes) =
  let hrb = (vlbytes 3 (HandshakeMessages.helloRetryRequestBytes hrr)) in
  let plain = hrb @| (vlbytes 1 digest) @| (vlbytes 2 extra) in
  let cipher = ticket_encrypt plain in
  trace ("Encrypting cookie: "^(hex_of_bytes plain));
  trace ("Encrypted cookie:  "^(hex_of_bytes cipher));
  cipher

let check_cookie b =
  trace ("Decrypting cookie "^(hex_of_bytes b));
  if length b < 32 then None else
  match ticket_decrypt b with
  | None -> trace ("Cookie decryption failed."); None
  | Some plain ->
    trace ("Plain cookie: "^(hex_of_bytes plain));
    match vlsplit 3 plain with
    | Error _ -> trace ("Cookie decode error: HRR"); None
    | Correct (hrb, b) ->
      let (_, hrb) = split hrb 4ul in // Skip handshake tag and vlbytes 3
      match HandshakeMessages.parseHelloRetryRequest hrb with
      | Error (_, m) -> trace ("Cookie decode error: parse HRR, "^m); None
      | Correct hrr ->
        match vlsplit 1 b with
        | Error _ -> trace ("Cookie decode error: digest"); None
        | Correct (digest, b) ->
          match vlparse 2 b with
          | Error _ -> trace ("Cookie decode error: application data"); None
          | Correct extra ->
            Some (hrr, digest, extra)

let check_ticket13 b =
  match check_ticket b with
  | Some (Ticket13 cs li _ _ created age_add) ->
    let CipherSuite13 ae h = cs in
    let nonce, _ = split b 12ul in
    Some PSK.({
      ticket_nonce = Some nonce;
      time_created = created;
      ticket_age_add = age_add;
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
