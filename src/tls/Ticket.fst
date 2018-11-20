module Ticket

open FStar.Bytes
open FStar.Error

open Mem
open Parse
open TLSError
open TLSConstants
open TLSInfo

module AE = AEADProvider

module PTL = Parsers.Ticket.Low // just to 1/ verify that module, and 2/ pollute the context with some Spec definitions (integers, vlbytes), and see what happens

#set-options "--admit_smt_queries true"

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("TCK| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_NGO then print else (fun _ -> ())

// verification-only
type hostname = string
type tlabel (h:hostname) = t:bytes * tls13:bool

noextract
private let region:rgn = new_region tls_tables_region

type ticket_key =
  | Key: i:AE.id -> wr:AE.writer i -> rd:AE.reader i -> ticket_key

private let dummy_id (a:aeadAlg) : St AE.id =
  assume false;
  let h = Hashing.Spec.SHA2_256 in
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

// Sealing key (for client-side sealing, e.g. of session local state)
private let sealing_enc : reference (option ticket_key) = ralloc region None

private let keygen () : St ticket_key =
  let id0 = dummy_id EverCrypt.CHACHA20_POLY1305 in
  let salt : AE.salt id0 = Random.sample (AE.iv_length id0) in
  let key : AE.key id0 = Random.sample (AE.key_length id0) in
  let wr = AE.coerce id0 region key salt in
  let rd = AE.genReader region #id0 wr in
  Key id0 wr rd

let get_ticket_key () : St ticket_key =
  match !ticket_enc with
  | Some k -> k
  | None ->
    let k = keygen () in
    ticket_enc := Some k; k

let get_sealing_key () : St ticket_key =
  match !sealing_enc with
  | Some k -> k
  | None ->
    let k = keygen () in
    sealing_enc := Some k; k

private let set_internal_key (sealing:bool) (a:aeadAlg) (kv:bytes) : St bool =
  let tid = dummy_id a in
  if length kv = AE.key_length tid + AE.iv_length tid then
    let k, s = split_ kv (AE.key_length tid) in
    let wr = AE.coerce tid region k s in
    let rd = AE.genReader region wr in
    let _ =
      if sealing then
        sealing_enc := Some (Key tid wr rd)
      else
        ticket_enc := Some (Key tid wr rd)
      in
    true
  else false

let set_ticket_key (a:aeadAlg) (kv:bytes) : St bool =
  set_internal_key false a kv

let set_sealing_key (a:aeadAlg) (kv:bytes) : St bool =
  set_internal_key true a kv

[@unifier_hint_injective]
inline_for_extraction
let vlbytespl (min max: nat) = (x: bytes { min <= length x /\ length x <= max })

// TODO absolute bare bone for functionality
// We should expand with certificates, mode, etc
type ticket =
  // 1.2 ticket
  | Ticket12:
    pv: protocolVersion ->
    cs: cipherSuite{CipherSuite? cs} ->
    ems: bool ->
    msId: msId ->
    ms: lbytes 48 ->
    ticket
  // 1.3 RMS PSK
  | Ticket13:
    cs: cipherSuite{CipherSuite13? cs} ->
    li: logInfo ->
    rmsId: pre_rmsId li ->
    rms: vlbytespl 32 255 ->
    nonce: vlbytespl 0 255 ->
    ticket_created: UInt32.t ->
    ticket_age_add: UInt32.t ->
    custom: vlbytespl 0 65535 ->
    ticket

// Currently we use dummy indexes until we can serialize them properly
let dummy_rmsid (ae: aeadAlg) (h: hash_alg): (li: logInfo & rmsId li) =
  let li: logInfo_SH = {
    li_sh_cr = Bytes.create 32ul 0z;
    li_sh_sr = Bytes.create 32ul 0z;
    li_sh_ae = ae;
    li_sh_hash = h;
    li_sh_psk = None;
  } in
  let li_cf: logInfo_CF = {
    li_cf_sf = ({ li_sf_sh = li; li_sf_certificate = None; });
    li_cf_certificate = None;
  } in
  let li: logInfo = LogInfo_CF li_cf in
  let log : hashed_log li = empty_bytes in
  let i : rmsId li = RMSID (ASID (Salt (EarlySecretID (NoPSK h)))) log in
  (| li, i |)

// Dummy msId TODO serialize and encrypt them properly
let dummy_msId pv cs ems =
  StandardMS PMS.DummyPMS (Bytes.create 64ul 0z) (kefAlg pv cs ems)

// not pure because of trace, but should be
let parse (b:bytes) (nonce:bytes) : St (option ticket) =
  trace ("Parsing ticket "^(hex_of_bytes b));
  if length b < 8 then None
  else
    let (pvb, r) = split b 2ul in
    match parseVersion pvb with
    | Error _ -> None
    | Correct pv ->
      let (csb, r) = split r 2ul in
      let csn = parseCipherSuiteName csb in
      match cipherSuite_of_name csn with // FIXME: move to check_ticket. Needs to be disentangled with dummy_rmsid, dummy_msId
      | None -> None
      | Some cs ->
        match pv, cs with
        | TLS_1p3, CipherSuite13 ae h ->
         begin
          let created, r = split r 4ul in
          let age_add, r = split r 4ul in
          match vlsplit 2 r with
          | Error _ -> None
          | Correct (custom, rms) ->
            match vlparse 2 rms with
            | Error _ -> None
            | Correct rms ->
              let (| li, rmsId |) = dummy_rmsid ae h in
              let age_add = uint32_of_bytes age_add in
              let created = uint32_of_bytes created in
              Some (Ticket13 cs li rmsId rms nonce created age_add custom)
         end
        | _ , CipherSuite _ _ _ ->
         begin
          let (emsb, ms) = split r 1ul in
          match vlparse 2 ms with
          | Error _ -> None
          | Correct rms ->
            let ems = 0z <> emsb.[0ul] in
            let msId = dummy_msId pv cs ems in
            Some (Ticket12 pv cs ems msId ms)
         end
        | _ -> None

let ticket_decrypt (seal:bool) cipher : St (option bytes) =
  let Key tid _ rd = if seal then get_sealing_key () else get_ticket_key () in
  let salt = AE.salt_of_state rd in
  let (nb, b) = split_ cipher (AE.iv_length tid) in
  let plain_len = length b - AE.taglen tid in
  let iv = AE.coerce_iv tid (xor_ #(AE.iv_length tid) nb salt) in
  AE.decrypt #tid #plain_len rd iv empty_bytes b

let check_ticket (seal:bool) (b:bytes{length b <= 65551}) : St (option ticket) =
  trace ("Decrypting ticket "^(hex_of_bytes b));
  let Key tid _ rd = get_ticket_key () in
  if length b < AE.iv_length tid + AE.taglen tid + 8 (*was: 32*) 
  then None 
  else match ticket_decrypt seal b with
    | None -> trace ("Ticket decryption failed."); None
    | Some plain ->
      let nonce, _ = split b 12ul in
      parse plain nonce

let serialize = function
  | Ticket12 pv cs ems _ ms ->
    (versionBytes pv) @| (cipherSuiteNameBytes (name_of_cipherSuite cs))
    @| abyte (if ems then 1z else 0z) @| (vlbytes 2 ms)
  | Ticket13 cs _ _ rms _ created age custom ->
    (versionBytes TLS_1p3) @| (cipherSuiteNameBytes (name_of_cipherSuite cs))
    @| (bytes_of_int32 created) @| (bytes_of_int32 age)
    @| (vlbytes 2 custom) @| (vlbytes 2 rms)

#reset-options

module PTL = Parsers.Ticket.Low
module TC = Parsers.TicketContents
module TC12 = Parsers.TicketContents12
module TC13 = Parsers.TicketContents13
module PB = Parsers.Boolean
module LPB = LowParse.Low.Bytes
module U32 = FStar.UInt32
module B = LowStar.Buffer

let ticketContents_of_ticket (t: ticket) : GTot TC.ticketContents =
  match t with
  | Ticket12 pv cs ems _ ms ->
    TC.Case_ticket12 ({
      TC12.pv = pv;
      TC12.cs = name_of_cipherSuite cs;
      TC12.ems = (if ems then PB.B_true else PB.B_false);
      TC12.master_secret = ms;
    })
  | Ticket13 cs _ _ rms nonce created age custom ->
    TC.Case_ticket13 ({
      TC13.cs = name_of_cipherSuite cs;
      TC13.rms = rms;
      TC13.nonce = nonce;
      TC13.creation_time = created;
      TC13.age_add = age;
      TC13.custom_data = custom;
    })

#reset-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 64 --z3cliopt smt.arith.nl=false --z3refresh --using_facts_from '* -FStar.Tactics -FStar.Reflection' --log_queries"

let write_ticket12 (t: ticket) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ Ticket12? t ))
  (ensures (fun h pos' h' ->
    let tc = ticketContents_of_ticket t in
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= match t with
  | Ticket12 pv cs ems _ ms ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` 54ul
    then LPB.max_uint32
    else begin
      let pos1 = pos `U32.add` 1ul in
      let pos2 = PTL.write_protocolVersion pv sl pos1 in
      let pos3 = PTL.write_cipherSuite (name_of_cipherSuite cs) sl pos2 in
      let pos4 = PTL.write_boolean (if ems then PB.B_true else PB.B_false) sl pos3 in
      let _ = LPB.write_flbytes 48ul ms sl pos4 in
      let h = get () in
      PTL.valid_ticketContents12_intro h sl pos1;
      PTL.finalize_case_ticketContents12 sl pos
    end

// #reset-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 64 --z3cliopt smt.arith.nl=false --z3cliopt trace=true --z3refresh --using_facts_from '* -FStar.Tactics -FStar.Reflection' --log_queries"

module HS = FStar.HyperStack

let write_ticket13_interm
  (h: HS.mem) (t: ticket) (sl: LPB.slice) (pos: U32.t) (pos6: U32.t)
: GTot Type0
= LPB.live_slice h sl /\ (
  match t with
  | Ticket13 cs _ _ rms nonce created age custom ->
    U32.v pos + U32.v (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom) <= U32.v sl.LPB.len /\ (
    let pos1 = pos `U32.add` 1ul in
    LPB.valid_content cipherSuite_parser h sl pos1 (name_of_cipherSuite cs) /\ (
    let pos2 = LPB.get_valid_pos cipherSuite_parser h sl pos1 in
    LPB.valid_content (LPB.parse_bounded_vlbytes 32 255) h sl pos2 rms /\ (
    let pos3 = LPB.get_valid_pos (LPB.parse_bounded_vlbytes 32 255) h sl pos2 in
    LPB.valid_content (LPB.parse_bounded_vlbytes 0 255) h sl pos3 nonce /\ (
    let pos4 = LPB.get_valid_pos (LPB.parse_bounded_vlbytes 0 255) h sl pos3 in
    LPB.valid_content LPB.parse_u32 h sl pos4 created /\ (
    let pos5 = LPB.get_valid_pos LPB.parse_u32 h sl pos4 in
    LPB.valid_content_pos LPB.parse_u32 h sl pos5 age pos6
    )))))
  | _ -> False
  )

let write_ticket13_part1 (t: ticket) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h ->
    LPB.live_slice h sl /\ (
    match t with
    | Ticket13 cs _ _ rms nonce created age custom ->
      U32.v pos + U32.v (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom) <= U32.v sl.LPB.len
    | _ -> False
  )))
  (ensures (fun h pos6 h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\
    write_ticket13_interm h' t sl pos pos6
  ))
= 
  match t with
  | Ticket13 cs _ _ rms nonce created age custom ->
    let pos1 = pos `U32.add` 1ul in
    let pos2 = PTL.write_cipherSuite (name_of_cipherSuite cs) sl pos1 in
    let len_rms = len rms in
    let _ = LPB.write_flbytes len_rms rms sl (pos2 `U32.add` 1ul) in
    let pos3 = LPB.finalize_bounded_vlbytes 32 255 sl pos2 len_rms in
    let len_nonce = len nonce in
    let _ = LPB.write_flbytes len_nonce nonce sl (pos3 `U32.add` 1ul) in
    let pos4 = LPB.finalize_bounded_vlbytes 0 255 sl pos3 len_nonce in
    let pos5 = LPB.write_u32 created sl pos4 in
    let pos6 = LPB.write_u32 age sl pos5 in
    pos6

let write_ticket13 (t: ticket) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ U32.v sl.LPB.len <= U32.v LPB.max_uint32 /\ Ticket13? t))
  (ensures (fun h pos' h' ->
    let tc = ticketContents_of_ticket t in
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match t with
  | Ticket13 cs _ _ rms nonce created age custom ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
      let pos6 = write_ticket13_part1 t sl pos in
      let len_custom = len custom in
      let pos6' = pos6 `U32.add` 2ul in
      let _ = LPB.write_flbytes len_custom custom sl (pos6 `U32.add` 2ul) in
      let _ = LPB.finalize_bounded_vlbytes 0 65535 sl pos6 len_custom in
      let h = get () in
      PTL.valid_ticketContents13_intro h sl (pos `U32.add` 1ul);
      PTL.finalize_case_ticketContents13 sl pos
    end

let write_ticket (t: ticket) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ U32.v sl.LPB.len <= U32.v LPB.max_uint32 ))
  (ensures (fun h pos' h' ->
    let tc = ticketContents_of_ticket t in
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= match t with
  | Ticket12 _ _ _ _ _ ->
    write_ticket12 t sl pos
  | Ticket13 cs _ _ rms nonce created age custom ->
    write_ticket13 t sl pos

#set-options "--admit_smt_queries true"

let ticket_encrypt (seal:bool) plain : St bytes =
  let Key tid wr _ = if seal then get_sealing_key () else get_ticket_key () in
  let nb = Random.sample (AE.iv_length tid) in
  let salt = AE.salt_of_state wr in
  let iv = AE.coerce_iv tid (xor 12ul nb salt) in
  let ae = AE.encrypt #tid #(length plain) wr iv empty_bytes plain in
  nb @| ae

let create_ticket (seal:bool) t =
  let plain = serialize t in
  ticket_encrypt seal plain

let create_cookie (hrr:HandshakeMessages.hrr) (digest:bytes) (extra:bytes) =
  let hrm = HandshakeMessages.HelloRetryRequest hrr in
  let hrb = vlbytes 3 (HandshakeMessages.handshakeMessageBytes None hrm) in
  let plain = hrb @| (vlbytes 1 digest) @| (vlbytes 2 extra) in
  let cipher = ticket_encrypt false plain in
  trace ("Encrypting cookie: "^(hex_of_bytes plain));
  trace ("Encrypted cookie:  "^(hex_of_bytes cipher));
  cipher

val check_cookie: b:bytes -> St (option (HandshakeMessages.hrr * bytes * bytes))
let check_cookie b =
  trace ("Decrypting cookie "^(hex_of_bytes b));
  if length b < 32 then None else
  match ticket_decrypt false b with
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

let ticket_pskinfo (t:ticket) =
  match t with
  | Ticket13 cs li _ _ nonce created age_add custom ->
    let CipherSuite13 ae h = cs in
    Some ({
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

let check_ticket13 b =
  match check_ticket false b with
  | Some t -> ticket_pskinfo t
  | _ -> None

let check_ticket12 b =
  match check_ticket false b with
  | Some (Ticket12 pv cs ems msId ms) -> Some (pv, cs, ems, msId, ms)
  | _ -> None
