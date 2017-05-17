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

open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS
open FFICallbacks

#set-options "--lax"

(* A flag for runtime debugging of ffi data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("EPO| "^s^"\n"))
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

 
let connect send recv config_1 : ML (Connection.connection * int) = 
  // we assume the configuration specifies the target SNI; 
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in 
  let c = TLS.connect here tcp config_1 in 
  let i_0 = currentId c Reader in 
  let firstResult = 
    match read c i_0 with 
    | Complete -> 0
    | ReadError description txt -> errno description txt 
    | CertQuery _ _ -> failwith "unsupported certificate request from the server"
    | Read _ -> failwith "unexpected early read" in
  c, firstResult

let accept_connected send recv config_1 : ML (Connection.connection * int) =
  // we assume the configuration specifies the target SNI;
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in
  let c = TLS.accept_connected here tcp config_1 in
  let i_0 = currentId c Reader in
  let firstResult =
    match read c i_0 with
    | Complete -> 0
    | ReadError description txt -> errno description txt
    | CertQuery _ _ -> failwith "unsupported certificate request from the client"
    | Read _ -> failwith "unexpected early read" in
  c, firstResult

type read_result = // is it convenient?
  | Received of bytes 
  | Errno of int

let read c : ML read_result = 
  let i = currentId c Reader in 
  match read c i with
  | Read (Data d)             -> Received (appBytes d)
  | Read Close                -> Errno 0 
  | Read (Alert a)            -> Errno(errno (Some a) "alert") 
  | ReadError description txt -> Errno(errno description txt) 
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
  ("RSA+SHA512",   RSA_PKCS1_SHA512);
  ("RSA+SHA384",   RSA_PKCS1_SHA384);
  ("RSA+SHA256",   RSA_PKCS1_SHA256);
  ("RSA+SHA1",     RSA_PKCS1_SHA1);
  ("ECDSA+SHA512", ECDSA_SECP521R1_SHA512);
  ("ECDSA+SHA384", ECDSA_SECP384R1_SHA384);
  ("ECDSA+SHA256", ECDSA_SECP256R1_SHA256);
  ("ECDSA+SHA1",   ECDSA_SHA1);
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

let ffiConfig version host =
  let v = s2pv version in 
  {defaultConfig with
    minVer = v;
    maxVer = v;
    check_peer_certificate = false;
    cert_chain_file = "c:\\Repos\\mitls-fstar\\data\\test_chain.pem";
    private_key_file = "c:\\Repos\\mitls-fstar\\data\\server.key";
    ca_file = "c:\\Repos\\mitls-fstar\\data\\CAFile.pem";
    safe_resumption = true;
    ciphersuites = cipherSuites_of_nameList [
                    (* mitls.ml ciphersuites *)
		      TLS_AES_128_GCM_SHA256;
		      TLS_AES_256_GCM_SHA384;
		      TLS_CHACHA20_POLY1305_SHA256;
		      TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256;
		      TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256;
		      TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
                    (* default ciphersuites from TLSInfo.fst follow: *)
                      TLS_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_DSS_WITH_AES_128_GCM_SHA256;
                      TLS_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_DSS_WITH_AES_128_CBC_SHA;
                      TLS_RSA_WITH_3DES_EDE_CBC_SHA;
                      ];
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

let rec findsetting f l = match l with
  | [] -> None
  | (s, i)::tl -> if s = f then Some i else findsetting f tl

val ffiSetCipherSuites: cfg:config -> x:string -> ML config
let ffiSetCipherSuites cfg x =
  let csl = String.split [':'] x in
  let csl = List.map (fun x-> match findsetting x css with
    | None -> failwith ("Unknown ciphersuite: "^x)
    | Some a -> a
    ) csl in
  { cfg with 
  ciphersuites = cipherSuites_of_nameList csl
  }

val ffiSetSignatureAlgorithms: cfg:config -> x:string -> ML config
let ffiSetSignatureAlgorithms cfg x =
  let sal = String.split [':'] x in
  let sal = List.map (fun x-> match findsetting x sas with
    | None -> failwith ("Unknown signature algorithm: "^x)
    | Some a -> a
  ) sal in
  { cfg with 
  signatureAlgorithms = sal
  }

val ffiSetNamedGroups: cfg:config -> x:string -> ML config
let ffiSetNamedGroups cfg x =
  let ngl = String.split [':'] x in
  let ngl = List.map (fun x-> match findsetting x ngs with
    | None -> failwith ("Unknown named group: "^x)
    | Some a -> a
  ) ngl in
  { cfg with 
  namedGroups = ngl
  }  

type callbacks = FFICallbacks.callbacks

val sendTcpPacket: callbacks:callbacks -> buf:bytes -> Platform.Tcp.EXT (Platform.Error.optResult string unit) 
let sendTcpPacket callbacks buf =  
  let result = FFICallbacks.ocaml_send_tcp callbacks (get_cbytes buf) in 
  if result < 0 then 
    Platform.Error.Error ("socket send failure") 
  else 
    Platform.Error.Correct () 
    
val recvTcpPacket: callbacks:callbacks -> max:nat -> Platform.Tcp.EXT (Platform.Error.optResult string (b:bytes{length b <= max}))
let recvTcpPacket callbacks max =
  let (result,str) = FFICallbacks.recvcb callbacks max in
  if result then
    Platform.Error.Correct(abytes str)
  else
    Platform.Error.Error ("socket recv failure")
  
val ffiConnect: config:config -> callbacks:callbacks -> ML (Connection.connection * int)
let ffiConnect config cb =
  connect (sendTcpPacket cb) (recvTcpPacket cb) config
  
val ffiAcceptConnected: config:config -> callbacks:callbacks -> ML (Connection.connection * int)
let ffiAcceptConnected config cb =
  accept_connected (sendTcpPacket cb) (recvTcpPacket cb) config

val ffiRecv: Connection.connection -> ML cbytes  
let ffiRecv c =
  match read c with
    | Received response -> get_cbytes response
    | Errno _ -> get_cbytes empty_bytes
  
val ffiSend: Connection.connection -> cbytes -> ML int
let ffiSend c b =
  let msg = abytes b in
  write c msg
