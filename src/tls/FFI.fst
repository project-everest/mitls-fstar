module FFI
module HS = FStar.HyperStack //Added automatically

// A thin layer on top of TLS, adapting a bit our main API:
// - for TCP send & receive, we use callbacks provided by the application
// - for output traffic, we send fragment and send the whole message at once
// - for client connects, we block until the connection is sucessfully established
//
// We rely on higher-order; to be reconsidered once we compile to C/C++.

// TODO: guarantee (by typing) that we don't do stdio, and don't throw
//       exceptions, notably for incomplete pattern matching

open FStar.Bytes
open FStar.Error

open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS
open FFICallbacks

open FStar.HyperStack.All
type cbytes = string
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
  let before, now = split_ buffer first in
  let now, after = split_ buffer len in
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
  | Some ad ->  let _, e = split_ (Alert.alertBytes ad) 2 in int_of_bytes e
  | None    -> -1 ))

let connect ctx send recv config_1 psks : ML (Connection.connection * int) =
  // we assume the configuration specifies the target SNI;
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks ctx send recv in
  let here = new_region HS.root in
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
  | Some ((c,_)::_, _) -> c
  | _ -> empty_bytes

let accept_connected ctx send recv config_1 : ML (Connection.connection * int) =
  // we assume the configuration specifies the target SNI;
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks ctx send recv in
  let here = new_region HS.root in
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
  }

let rec findsetting f l =
  match l with
  | [] -> None
  | (s, i)::tl -> if s = f then Some i else findsetting f tl

let rec updatecfg cfg l : ML config =
  match l with
  | [] -> cfg
  | "EDI" :: t -> updatecfg ({cfg with max_early_data = Some 16384}) t
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
    if String.length x < 256 then utf8_encode x
    else failwith ("ffiSetALPN: protocol <"^x^"> is too long")
  ) apl in
  { cfg with alpn = if apl=[] then None else Some apl }

val ffiSetEarlyData: cfg:config -> x:nat -> ML config
let ffiSetEarlyData cfg x =
  trace ("setting early data limit to "^(string_of_int x));
  { cfg with
  max_early_data = if x>0 then Some x else None;
  }

val ffiSetTicketKey: a:string -> k:string -> ML bool
let ffiSetTicketKey a k =
  (match findsetting a aeads with
  | None -> false
  | Some a -> TLS.set_ticket_key a (bytes_of_string k))

type callbacks = FFICallbacks.callbacks

val sendTcpPacket: callbacks:callbacks -> buf:bytes -> EXT (FStar.Error.optResult string unit)
let sendTcpPacket callbacks buf =
  let result = FFICallbacks.ocaml_send_tcp callbacks (print_bytes buf) in
  if result < 0 then
    FStar.Error.Error ("socket send failure")
  else
    FStar.Error.Correct ()

val recvTcpPacket: callbacks:callbacks -> max:nat -> EXT (FStar.Tcp.recv_result max)
let recvTcpPacket callbacks max =
  let (result,str) = FFICallbacks.recvcb callbacks max in
  if result then
    let b = bytes_of_string str in
    if length b = 0
    then FStar.Tcp.RecvWouldBlock
    else FStar.Tcp.Received b
  else
    FStar.Tcp.RecvError ("socket recv failure")

let install_ticket config ticket : ML (list PSK.psk_identifier) =
  match ticket with
  | Some (t, si) ->
    (match Ticket.parse si with
    | Some (Ticket.Ticket12 pv cs ems msId ms) ->
      PSK.s12_extend t (pv, cs, ems, ms); [t]
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
          allow_early_data = (Some? config.max_early_data);
          allow_dhe_resumption = true;
          allow_psk_resumption = true;
          early_ae = ae;
          early_hash = h;
          // TODO(adl) store identities
          identities = (empty_bytes, empty_bytes)
        }) rms);
      [t]
    | _ -> failwith ("FFI: Cannot use the input ticket, session info failed to decode: "^(print_bytes si)))
  | None -> []

// 18-01-24 changed calling convention; now almost like connect
val ffiConnect: 
  Transport.pvoid -> Transport.pfn_send -> Transport.pfn_recv -> 
  config -> option (bytes * bytes) -> ML (Connection.connection * int)
let ffiConnect ctx snd rcv config ticket =
  connect ctx snd rcv config (install_ticket config ticket)

// 18-01-24 changed calling convention; now just like accept_connected
val ffiAcceptConnected: 
  Transport.pvoid -> Transport.pfn_send -> Transport.pfn_recv -> 
  config -> ML (Connection.connection * int)
let ffiAcceptConnected ctx snd rcv config =
  accept_connected ctx snd rcv config 

// 18-01-24 not needed anymore?
val ffiRecv: Connection.connection -> ML cbytes
let ffiRecv c =
  match read c with
    | Received response -> print_bytes response
    | WouldBlock
    | Errno _ -> print_bytes empty_bytes

// 18-01-24 not needed anymore?
val ffiSend: Connection.connection -> cbytes -> ML int
let ffiSend c b =
  let msg = bytes_of_string b in
  write c msg


let ffiSetTicketCallback (cfg:config) (cb:ticket_cb) =
  trace "Setting a new ticket callback.";
  {cfg with ticket_callback = cb}

let ffiSetCertCallbacks (cfg:config) (cb:cert_cb) =
  trace "Setting up certificate callbacks.";
  {cfg with cert_callbacks = cb}

// ADL july 24: now returns both the ticket and the
// entry in the PSK database to allow inter-process ticket reuse
// Beware! this exports crypto materials!
(*
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
        let (| li, rmsid |) = Ticket.dummy_rmsid ae h in
        let si = Ticket.serialize (Ticket.Ticket13 (CipherSuite13 ae h) li rmsid psk) in
        Some (t, si))
    | _ -> None)
  | None -> None
*)

val ffiGetCert: Connection.connection -> ML cbytes
let ffiGetCert c =
  let cert = getCert c in
  print_bytes cert

// some basic sanity checks
let ffiGetExporter (c:Connection.connection) (early:bool)
  : ML (option (Hashing.Spec.alg * aeadAlg * bytes))
  =
  let keys = Handshake.xkeys_of c.Connection.hs in
  (* Rewrote this around broken `=` comparison compilation, we should revisit - jroesch *)
  match Seq.length keys with
  | 0 -> None
  | _ ->
    let i = (match Seq.length keys with 2 when not early -> 1 | _ -> 0) in
    let (| li, expId, b|) = Seq.index keys i in
    let h = exportId_hash expId in
    let ae = logInfo_ae li in
    match early, expId with
    | false, ExportID _ _ -> Some (h, ae, b)
    | true, EarlyExportID _ _ -> Some (h, ae, b)
    | _ -> None


//   (sni:string -> ticket:bytes -> info:ticketInfo -> rawkey:bytes -> ST unit
let ffiTicketCallback (cb_state:callbacks) (cb:callbacks) (sni:string) (ticket:bytes) (info:ticketInfo) (key:bytes) =
  let si = match info with
    | TicketInfo_13 ctx ->
      let ae = ctx.early_ae in
      let h = ctx.early_hash in
      let (| li, rmsid |) = Ticket.dummy_rmsid ae h in
      Ticket.Ticket13 (CipherSuite13 ae h) li rmsid key
    | TicketInfo_12 (pv, cs, ems) ->
      Ticket.Ticket12 pv cs ems (Ticket.dummy_msId pv cs ems) key
    in
  ocaml_ticket_cb cb_state cb sni ticket (Ticket.serialize si)

let ffiCertSelectCallback (cb_state:callbacks) (cb:callbacks) (sni:string) (sal:signatureSchemeList)
  : ML (option (cert_type * signatureScheme)) =
  trace ("Certificate select callback: SNI=<"^sni^">, SA=<"^(Negotiation.string_of_signatureSchemes sal)^">");
  let sab = signatureSchemeListBytes_aux [] empty_bytes sal in
  match ocaml_cert_select_cb cb_state cb sni sab with
  | None -> None
  | Some (cert_ptr, sa) ->
    let b = bytes_of_int 2 (FStar.UInt16.v sa) in
    let Correct sa = parseSignatureScheme b in
    if List.Tot.mem sa sal then Some (cert_ptr, sa)
    else failwith "Callback error: selected a signature scheme that was not offered."

let ffiCertFormatCallback (cb_state:callbacks) (cb:callbacks) (cert:cert_type)
  : ML (list cert_repr) =
  trace ("Certificate format callback");
  let chain = ocaml_cert_format_cb cb_state cb cert in
  match Cert.parseCertificateList chain with
  | Error (_, msg) -> failwith ("ffiCertFormatCallback: formatted chain was invalid, "^msg)
  | Correct chain -> chain

let ffiCertSignCallback (cb_state:callbacks) (cb:callbacks) (cert:cert_type)
  (sig:signatureScheme) (tbs:bytes) : ML (option bytes) =
  trace ("Certificate sign callback for "^(Negotiation.string_of_signatureScheme sig));
  let sa = UInt16.uint_to_t (int_of_bytes (signatureSchemeBytes sig)) in
  ocaml_cert_sign_cb cb_state cb cert sa tbs

let ffiCertVerifyCallback (cb_state:callbacks) (cb:callbacks) (cert:list cert_repr)
  (sig:signatureScheme) (tbs:bytes) (sigv:bytes) : ML bool =
  trace ("Certificate verify callback for "^(Negotiation.string_of_signatureScheme sig));
  let sa = UInt16.uint_to_t (int_of_bytes (signatureSchemeBytes sig)) in
  ocaml_cert_verify_cb cb_state cb (Cert.certificateListBytes cert) sa (tbs, sigv)
