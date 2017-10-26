module FFI

// A thin layer on top of TLS, adapting a bit our main API:
// - for TCP send & receive, we use callbacks provided by the application
// - for output traffic, we send fragment and send the whole message at once
// - for client connects, we block until the connection is sucessfully established
//
// We rely on higher-order; to be reconsidered once we compile to C/C++.

// TODO: guarantee (by typing) that we don't do stdio, and don't throw
//       exceptions, notably for incomplete pattern matching

open Platform.Bytes
open Platform.Error

open TLSConstants
open TLSInfo
module Range = Range
let range = Range.range
let frange = Range.frange

open DataStream
open TLS
open FFICallbacks

open FStar.HyperStack.All

#set-options "--lax"

(* A flag for runtime debugging of ffi data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("FFI| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_FFI then print else (fun _ -> ())

private let fragment_1 i (b:bytes { length b <= max_TLSPlaintext_fragment_length }) : fragment i (point (length b)) =
  let rg : frange i = point(length b) in
  appFragment i rg b

// move to Bytes
private let sub (buffer:bytes) (first:nat) (len:nat { first + len <= length buffer }) =
  let before, now = split buffer first in
  let now, after = split buffer len in
  now

private val write_all': c:Connection.connection -> i:id -> buffer:bytes -> sent:nat {sent <= length buffer} -> St ioresult_w
let rec write_all' c i buffer sent =
  if sent = length buffer then Written
  else
  let size = min (length buffer - sent) max_TLSPlaintext_fragment_length in
  let payload = sub buffer sent size in
  let rg : frange i = point(length payload) in
  let f : fragment i rg = fragment_1 i payload in
  match assume false; write c f with
  | Written -> write_all' c i buffer (sent+size)
  | r       -> r

private let write_all c i b : ML ioresult_w = write_all' c i b 0

// an integer carrying the fatal alert descriptor
// we could also write txt into the application error log
private let errno description txt : ML int =
  let txt0 =
    match description with
    | Some ad -> TLSError.string_of_ad ad
    | None    -> "(None)" in (
  trace ("returning error: "^txt0^" "^txt^"\n"); (
  match description with
  | Some ad -> Char.int_of_char (snd (cbyte2 (Alert.alertBytes ad)))
  | None    -> -1 ))


let connect send recv config_1 psks : ML (Connection.connection * int) =
  // we assume the configuration specifies the target SNI;
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in
  let c = TLS.resume here tcp config_1 None psks in
  let rec read_loop c : ML int =
    let i = currentId c Reader in
    match read c i with
    | Complete -> 0
    | ReadError description txt -> errno description txt
    | Update false -> read_loop c
    | Update true -> 0 // 0-RTT: ready to send early data
    | _ -> failwith "FFI: Unexpected TLS read signal in connect"
    in
  let firstResult = read_loop c in
  c, firstResult

val getCert: Connection.connection -> ML bytes // bytes of the first certificate in the server-certificate chain.
let getCert c =
  let mode = TLS.get_mode c in
  match mode.Negotiation.n_server_cert with
  | Some ((c,_)::_) -> c
  | _ -> empty_bytes

let accept_connected send recv config_1 : ML (Connection.connection * int) =
  // we assume the configuration specifies the target SNI;
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in
  let c = TLS.accept_connected here tcp config_1 in
  let rec read_loop c : ML int =
    let i = currentId c Reader in
    match read c i with
    | Complete -> 0
    | ReadError description txt -> errno description txt
    | Update false -> read_loop c
    | Update true -> 0 // 0.5-RTT: ready to write
    | _ -> failwith "FFI: Unexpected TLS read signal in accept_connected"
    in
  let firstResult = read_loop c in
  c, firstResult

type read_result = // is it convenient?
  | Received of bytes
  | WouldBlock
  | Errno of int

let rec read c : ML read_result =
  let i = currentId c Reader in
  match TLS.read c i with
  | Complete                  -> read c // because of 0.5-RTT the complete may come late
  | Read (Data d)             -> Received (appBytes d)
  | Read Close                -> Errno 0
  | Read (Alert a)            -> Errno(errno (Some a) "alert")
  | ReadError description txt -> Errno(errno description txt)
  | ReadWouldBlock            -> WouldBlock
  | _                         -> failwith "unexpected FFI read result"

let write c msg : ML int =
  let i = currentId c Writer in
  match write_all c i msg with
  | Written                    -> 0
  | WriteError description txt -> errno description txt
  | _                          -> -1

// sending "CLOSE_NOTIFY"; should be followed by a read to wait for
// the full shutdown (but many servers don't acknowledge).

let close c : ML int =
  trace ("FFI close\n");
  match writeCloseNotify c with
  | WriteClose                 -> 0
  | WriteError description txt -> errno description txt
  | _                          -> -1

let close_extraction_bug c : ML int =
  match writeCloseNotify c with
  | writeClose                 -> 0
  | WriteError description txt -> errno description txt
  | _                          -> -1


(* ************** Native FFI support  ************** *)

let s2pv = function
  | "1.2" -> TLS_1p2
  | "1.3" -> TLS_1p3
  | "1.1" -> TLS_1p1
  | "1.0" -> TLS_1p0
  | s -> failwith ("Invalid protocol version specified: "^s)

let css = [
  ("TLS_AES_128_GCM_SHA256", TLS_AES_128_GCM_SHA256);
  ("TLS_AES_256_GCM_SHA384", TLS_AES_256_GCM_SHA384);
  ("TLS_CHACHA20_POLY1305_SHA256", TLS_CHACHA20_POLY1305_SHA256);
  ("TLS_AES_128_CCM_SHA256", TLS_AES_128_CCM_SHA256);
  ("TLS_AES_128_CCM_8_SHA256", TLS_AES_128_CCM_8_SHA256);
  ("ECDHE-RSA-AES256-GCM-SHA384", TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384);
  ("ECDHE-RSA-AES128-GCM-SHA256", TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256);
  ("ECDHE-RSA-CHACHA20-POLY1305-SHA256", TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256);
  ("ECDHE-ECDSA-AES256-GCM-SHA384", TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384);
  ("ECDHE-ECDSA-AES128-GCM-SHA256", TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256);
  ("ECDHE-ECDSA-CHACHA20-POLY1305-SHA256", TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256);
  ("DHE-RSA-AES256-GCM-SHA384", TLS_DHE_RSA_WITH_AES_256_GCM_SHA384);
  ("DHE-RSA-AES128-GCM-SHA256", TLS_DHE_RSA_WITH_AES_128_GCM_SHA256);
  ("DHE-RSA-CHACHA20-POLY1305-SHA256", TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256);
]

let sas = [
  ("RSAPSS+SHA512", RSA_PSS_SHA512);
  ("RSAPSS+SHA384", RSA_PSS_SHA384);
  ("RSAPSS+SHA256", RSA_PSS_SHA256);
  ("RSA+SHA512",    RSA_PKCS1_SHA512);
  ("RSA+SHA384",    RSA_PKCS1_SHA384);
  ("RSA+SHA256",    RSA_PKCS1_SHA256);
  ("RSA+SHA1",      RSA_PKCS1_SHA1);
  ("ECDSA+SHA512",  ECDSA_SECP521R1_SHA512);
  ("ECDSA+SHA384",  ECDSA_SECP384R1_SHA384);
  ("ECDSA+SHA256",  ECDSA_SECP256R1_SHA256);
  ("ECDSA+SHA1",    ECDSA_SHA1);
]

let ngs = [
  ("P-521", Parse.SEC CoreCrypto.ECC_P521);
  ("P-384", Parse.SEC CoreCrypto.ECC_P384);
  ("P-256", Parse.SEC CoreCrypto.ECC_P256);
  ("X25519", Parse.SEC CoreCrypto.ECC_X25519);
  ("X448",  Parse.SEC CoreCrypto.ECC_X448);
  ("FFDHE4096", Parse.FFDHE Parse.FFDHE4096);
  ("FFDHE3072", Parse.FFDHE Parse.FFDHE3072);
  ("FFDHE2048", Parse.FFDHE Parse.FFDHE2048);
]

let aeads = [
  ("AES128-GCM", CoreCrypto.AES_128_GCM);
  ("AES256-GCM", CoreCrypto.AES_256_GCM);
  ("CHACHA20-POLY1305", CoreCrypto.CHACHA20_POLY1305);
]

let ffiConfig version host =
  let v = s2pv version in
  {defaultConfig with
    min_version = TLS_1p2;
    max_version = v;
    peer_name = Some host;
    check_peer_certificate = false;
    cert_chain_file = "c:\\Repos\\mitls-fstar\\data\\test_chain.pem";
    private_key_file = "c:\\Repos\\mitls-fstar\\data\\server.key";
    ca_file = "c:\\Repos\\mitls-fstar\\data\\CAFile.pem";
  }

val ffiSetCertChainFile: cfg:config -> f:string -> ML config
let ffiSetCertChainFile cfg f =
  { cfg with
  cert_chain_file = f;
  }

val ffiSetPrivateKeyFile: cfg:config -> f:string -> ML config
let ffiSetPrivateKeyFile cfg f =
  { cfg with
  private_key_file = f;
  }

val ffiSetCAFile: cfg:config -> f:string -> ML config
let ffiSetCAFile cfg f =
  { cfg with
  ca_file = f;
  }

let rec findsetting f l =
  match l with
  | [] -> None
  | (s, i)::tl -> if s = f then Some i else findsetting f tl

let rec updatecfg cfg l : ML config =
  match l with
  | [] -> cfg
  | "EDI" :: t -> updatecfg ({cfg with enable_early_data = true;}) t
  | r :: t -> failwith ("Unknown flag: "^r)

(** SZ: FStar.List opens FStar.All.
    Should we have a version that uses FStar.HyperStack.All?
*)
val map: ('a -> ML 'b) -> list 'a -> ML (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

val ffiSetCipherSuites: cfg:config -> x:string -> ML config
let ffiSetCipherSuites cfg x =
  let x :: t = String.split ['@'] x in
  let cfg = updatecfg cfg t in
  let csl = String.split [':'] x in
  let csl = map (fun x -> match findsetting x css with
    | None -> failwith ("Unknown ciphersuite: "^x)
    | Some a -> a
    ) csl in
  { cfg with
  cipher_suites = cipherSuites_of_nameList csl
  }

val ffiSetSignatureAlgorithms: cfg:config -> x:string -> ML config
let ffiSetSignatureAlgorithms cfg x =
  let sal = String.split [':'] x in
  let sal = map (fun x -> match findsetting x sas with
    | None -> failwith ("Unknown signature algorithm: "^x)
    | Some a -> a
    ) sal in
  { cfg with
  signature_algorithms = sal
  }

val ffiSetNamedGroups: cfg:config -> x:string -> ML config
let ffiSetNamedGroups cfg x =
  let ng_parse x = match findsetting x ngs with
    | None -> failwith ("Unknown named group: "^x)
    | Some a -> a in
  let supported :: offered = String.split ['@'] x in
  let ngl = String.split [':'] supported in
  let ngl = map ng_parse ngl in
  let ogl = match offered with
    | [] -> ngl
    | [og] -> map ng_parse (String.split [':'] og)
    | _ -> failwith "Use @G1:..:Gn to set groups on which to offer shares" in
  { cfg with
    named_groups = ngl;
    offer_shares = ogl;
  }

val ffiSetALPN: cfg:config -> x:string -> ML config
let ffiSetALPN cfg x =
  let apl = if x = "" then [] else String.split [':'] x in
  if List.Tot.length apl > 255 then failwith "ffiSetALPN: too many entries";
  let apl = map (fun x ->
    if String.length x < 256 then utf8 x
    else failwith ("ffiSetALPN: protocol <"^x^"> is too long")
  ) apl in
  { cfg with alpn = if apl=[] then None else Some apl }

val ffiSetEarlyData: cfg:config -> x:bool -> ML config
let ffiSetEarlyData cfg x =
  trace ("setting early data to "^(if x then "true" else "false"));
  { cfg with
  enable_early_data = x;
  }

val ffiSetTicketKey: a:string -> k:string -> ML bool
let ffiSetTicketKey a k =
  (match findsetting a aeads with
  | None -> false
  | Some a -> TLS.set_ticket_key a (abytes k))

type callbacks = FFICallbacks.callbacks

val sendTcpPacket: callbacks:callbacks -> buf:bytes -> EXT (Platform.Error.optResult string unit)
let sendTcpPacket callbacks buf =
  let result = FFICallbacks.ocaml_send_tcp callbacks (get_cbytes buf) in
  if result < 0 then
    Platform.Error.Error ("socket send failure")
  else
    Platform.Error.Correct ()

val recvTcpPacket: callbacks:callbacks -> max:nat -> EXT (Platform.Tcp.recv_result max)
let recvTcpPacket callbacks max =
  let (result,str) = FFICallbacks.recvcb callbacks max in
  if result then
    let b = abytes str in
    if length b = 0
    then Platform.Tcp.RecvWouldBlock
    else Platform.Tcp.Received b
  else
    Platform.Tcp.RecvError ("socket recv failure")

let install_ticket config ticket : ML (list PSK.psk_identifier) =
  match ticket with
  | Some (t, si) ->
    (match Ticket.parse si with
    | Some (Ticket.Ticket13 cs li rmsId rms) ->
      (match PSK.psk_lookup t with
      | Some _ ->
        trace ("input ticket "^(print_bytes t)^" is in PSK database")
      | None ->
        trace ("installing ticket "^(print_bytes t)^" in PSK database");
        let CipherSuite13 ae h = cs in
        PSK.coerce_psk t PSK.({
          // TODO(adl) store in session info
          // N.B. FFi.ffiGetTicket returns the PSK - no need to derive RMS again
          ticket_nonce = Some empty_bytes;
          time_created = 0;
          // FIXME(adl): we should preserve the server flag somewhere
          allow_early_data = config.enable_early_data;
          allow_dhe_resumption = true;
          allow_psk_resumption = true;
          early_ae = ae;
          early_hash = h;
          // TODO(adl) store identities
          identities = (empty_bytes, empty_bytes)
        }) rms);
      [t]
    | _ -> failwith ("QUIC: Cannot use the input ticket, session info failed to decode: "^(print_bytes si)))
  | None -> []

val ffiConnect: config -> callbacks -> option (bytes * bytes) -> ML (Connection.connection * int)
let ffiConnect config cb ticket =
  connect (sendTcpPacket cb) (recvTcpPacket cb) config (install_ticket config ticket)

val ffiAcceptConnected: config:config -> callbacks:callbacks -> ML (Connection.connection * int)
let ffiAcceptConnected config cb =
  accept_connected (sendTcpPacket cb) (recvTcpPacket cb) config

val ffiRecv: Connection.connection -> ML cbytes
let ffiRecv c =
  match read c with
    | Received response -> get_cbytes response
    | WouldBlock
    | Errno _ -> get_cbytes empty_bytes

val ffiSend: Connection.connection -> cbytes -> ML int
let ffiSend c b =
  let msg = abytes b in
  write c msg

// ADL july 24: now returns both the ticket and the
// entry in the PSK database to allow inter-process ticket reuse
// Beware! this exports crypto materials!
let ffiGetTicket c: ML (option (ticket:bytes * rms:bytes)) =
  match (Connection.c_cfg c).peer_name with
  | Some n ->
    (match Ticket.lookup n with
    | Some (t, true) ->
      (match PSK.psk_lookup t with
      | None -> None
      | Some ctx ->
        let ae = ctx.PSK.early_ae in
        let h = ctx.PSK.early_hash in
        let pskb = PSK.psk_value t in
        // FIXME(adl): serialize rmsId
        let (| li, rmsid |) = Ticket.dummy_rmsid ae h in
        let si = Ticket.serialize (Ticket.Ticket13
          (CipherSuite13 ae h) li rmsid pskb) in
        Some (t, si))
    | _ -> None)
  | None -> None

val ffiGetCert: Connection.connection -> ML cbytes
let ffiGetCert c =
  let cert = getCert c in
  get_cbytes cert

// some basic sanity checks
let ffiGetExporter (c:Connection.connection) (early:bool)
  : ML (option (Hashing.Spec.alg * aeadAlg * bytes))
  =
  let keys = Handshake.xkeys_of c.Connection.hs in
  if Seq.length keys = 0 then None
  else
    let i = if Seq.length keys = 2 && not early then 1 else 0 in
    let (| li, expId, b|) = Seq.index keys i in
    let h = exportId_hash expId in
    let ae = logInfo_ae li in
    match early, expId with
    | false, ExportID _ _ -> Some (h, ae, b)
    | true, EarlyExportID _ _ -> Some (h, ae, b)
    | _ -> None
