(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
(**
This modules defines TLS 1.3 Extensions. 

- An AST, and it's associated parsing and formatting functions. 
- Nego calls prepareExtensions : config -> list extensions. 

@summary: TLS 1.3 Extensions. 
*)
module Extensions

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants

(*************************************************
 Define extension. 
 *************************************************)

(* As a static invariant, we record that any intermediate, parsed
extension and extension lists can be formatted into bytes without
overflowing 2^16. This create dependencies on the formatting
functions, at odd with recursive extensions. *)

let error s = Error (AD_decode_error, ("Extensions parsing: "^s))

//17-05-01 deprecated---use TLSError.result instead? 
(** local, failed-to-parse exc. *)
private type canFail (a:Type) =
| ExFail of alertDescription * string
| ExOK of list a


(* PRE-SHARED KEYS AND KEY EXCHANGES *) 

noeq type psk = 
  // this is the truncated PSK extension, without the list of binder tags.
  | ClientPSK of list (PSK.preSharedKey * PSK.obfuscated_ticket_age)
  // this is just an index in the client offer's PSK extension
  | ServerPSK of UInt16.t 

//TODO
//let psk_bytes: psk -> Tot bytes = admit()
//let parse_psk: pinverse_t psk_bytes = admit()

// https://tlswg.github.io/tls13-spec/#rfc.section.4.2.8
// restricting both proposed PSKs and future ones sent by the server
// will also be used in the PSK table, and possibly in the configs
type psk_kex =
  | PSK_KE 
  | PSK_DHE_KE 

type client_psk_kexes = l:list psk_kex 
  { l = [PSK_KE] \/ l = [PSK_DHE_KE] \/ l = [PSK_KE; PSK_DHE_KE] \/ l = [PSK_DHE_KE; PSK_KE] }

let client_psk_kexes_length (l:client_psk_kexes): Lemma (List.Tot.length l < 3) = ()

val psk_kex_bytes: psk_kex -> Tot (lbytes 1)
let psk_kex_bytes = function 
  | PSK_KE -> abyte 0z 
  | PSK_DHE_KE -> abyte 1z
let parse_psk_kex: pinverse_t psk_kex_bytes = fun b -> match cbyte b with 
  | 0z -> Correct PSK_KE
  | 1z -> Correct PSK_DHE_KE
  | _ -> error  "psk_key"

let client_psk_kexes_bytes (ckxs: client_psk_kexes): b:bytes {length b <= 3} = 
  let content: b:bytes {length b = 1 || length b = 2} = 
    match ckxs with 
    | [x] -> psk_kex_bytes x
    | [x;y] -> psk_kex_bytes x @| psk_kex_bytes y in
  lemma_repr_bytes_values (length content);
  vlbytes 1 content

let parse_client_psk_kexes: pinverse_t client_psk_kexes_bytes = fun b -> 
  if equalBytes b (client_psk_kexes_bytes [PSK_KE]) then Correct [PSK_KE] else 
  if equalBytes b (client_psk_kexes_bytes [PSK_DHE_KE]) then Correct [PSK_DHE_KE] else
  if equalBytes b (client_psk_kexes_bytes [PSK_KE; PSK_DHE_KE]) then Correct [PSK_KE; PSK_DHE_KE]  else
  if equalBytes b (client_psk_kexes_bytes [PSK_DHE_KE; PSK_KE]) then Correct [PSK_DHE_KE; PSK_KE] 
  else error "PSK KEX payload"
  // redundants lists yield an immediate decoding error.


(* EARLY DATA INDICATION *) 

type earlyDataIndication = option UInt32.t // Some  max_early_data_size, only in  NewSessionTicket

val earlyDataIndicationBytes: edi:earlyDataIndication -> Tot bytes
let earlyDataIndicationBytes = function
  | None -> empty_bytes // ClientHello, EncryptedExtensions
  | Some max_early_data_size -> // NewSessionTicket
    let n = UInt32.v max_early_data_size in    
    lemma_repr_bytes_values n;
    bytes_of_int 4 n

val parseEarlyDataIndication: bytes -> result earlyDataIndication
let parseEarlyDataIndication data =
  match length data with 
  | 0 -> Correct None 
  | 4 -> 
      let n = int_of_bytes data in
      lemma_repr_bytes_values n;
      assert_norm (pow2 32 == 4294967296);
      Correct (Some (UInt32.uint_to_t n))
  | _ -> error "early data indication" 
  

(* EC POINT FORMATS *) 

let rec ecpfListBytes_aux: list ECGroup.point_format -> bytes = function
  | [] -> empty_bytes
  | ECGroup.ECP_UNCOMPRESSED :: r -> abyte 0z @| ecpfListBytes_aux r
  | ECGroup.ECP_UNKNOWN t :: r -> bytes_of_int 1 t @| ecpfListBytes_aux r

val ecpfListBytes: l:list ECGroup.point_format{length (ecpfListBytes_aux l) < 256} -> Tot bytes
let ecpfListBytes l =
  let al = ecpfListBytes_aux l in
  lemma_repr_bytes_values (length al);
  let bl:bytes = vlbytes 1 al in
  bl


(* PROTOCOL VERSIONS *) 

// The length exactly reflects the RFC format constraint <2..254> 
type protocol_versions =
  l:list protocolVersion {0 < List.Tot.length l /\ List.Tot.length l < 128}

val protocol_versions_bytes: protocol_versions -> b:bytes {length b <= 255}
let protocol_versions_bytes vs =
  vlbytes 1 (List.Tot.fold_left (fun acc v -> acc @| TLSConstants.versionBytes v) empty_bytes vs)
  // todo length bound; do we need an ad hoc variant of fold? 
  
//17-05-01 added a refinement to control the list length; this function verifies.
//17-05-01 should we use generic code to parse such bounded lists?
//REMARK: This is not tail recursive, contrary to most of our parsing functions
val parseVersions: 
  b:bytes -> 
  Tot (result (l:list TLSConstants.protocolVersion {FStar.Mul.( length b == 2 * List.Tot.length l)})) (decreases (length b))
let rec parseVersions b =
  match length b with 
  | 0 -> let r = [] in assert_norm (List.Tot.length [] = 0); Correct r
  | 1 -> Error (AD_decode_error, "malformed version list") 
  | _ -> 
    let b2, b' = split b 2 in
    match TLSConstants.parseVersion_draft b2 with 
    | Error z -> Error z
    | Correct v -> 
      match parseVersions b' with 
      | Error z -> Error z 
      | Correct vs -> (
          let r = v::vs in 
          assert_norm (List.Tot.length (v::vs) = 1 + List.Tot.length vs); // did not find usable length lemma in List.Tot
          Correct r)

val parseSupportedVersions: b:bytes{2 < length b /\ length b < 256} -> result protocol_versions
let parseSupportedVersions b =
  match vlparse 1 b with
  | Error z -> error "protocol versions"
  | Correct b ->
    begin
    match parseVersions b with
    | Error z -> Error z
    | Correct vs ->
      let n = List.Tot.length vs in
      if 1 <= n && n <= 127 
      then Correct vs 
      else  error "too many or too few protocol versions"
    end


(* SERVER NAME INDICATION *) 

private val serverNameBytes: list serverName -> Tot bytes
let serverNameBytes l =
  let rec (aux:list serverName -> Tot bytes) = function
  | [] -> empty_bytes
  | SNI_DNS x :: r -> abyte 0z @| bytes_of_int 2 (length x) @| x @| aux r
  | SNI_UNKNOWN(t, x) :: r -> bytes_of_int 1 t @| bytes_of_int 2 (length x) @| x @| aux r
  in
  aux l
 
private val parseServerName: r:role -> b:bytes -> Tot (result (list serverName))
let parseServerName r b  =
  let rec aux: b:bytes -> Tot (canFail serverName) (decreases (length b)) = fun b ->
    if equalBytes b empty_bytes then ExOK []
    else if length b >= 3 then
      let ty,v = split b 1 in
      begin
      match vlsplit 2 v with
      | Error(x,y) ->
	ExFail(x, "Failed to parse SNI length: "^ (Platform.Bytes.print_bytes b))
      | Correct(cur, next) ->
	begin
	match aux next with
	| ExFail(x,y) -> ExFail(x,y)
	| ExOK l ->
	  let cur =
	    begin
	    match cbyte ty with
	    | 0z -> SNI_DNS(cur)
	    | v  -> SNI_UNKNOWN(int_of_bytes ty, cur)
	    end
	  in
	  let snidup: serverName -> Tot bool = fun x ->
	    begin
	    match x,cur with
	    | SNI_DNS _, SNI_DNS _ -> true
	    | SNI_UNKNOWN(a,_), SNI_UNKNOWN(b,_) -> a = b
	    | _ -> false
	    end
	  in
	  if List.Tot.existsb snidup l then
	    ExFail(AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Duplicate SNI type")
	  else ExOK(cur :: l)
	end
      end
    else ExFail(AD_decode_error, "Failed to parse SNI")
    in
    match r with
    | Server ->
      if length b = 0 then correct []
      else
	let msg = "Failed to parse SNI list: should be empty in ServerHello, has size " ^ string_of_int (length b) in
	Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ msg)
    | Client ->
      if length b >= 2 then
	begin
	match vlparse 2 b with
	| Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse SNI list")
	| Correct b ->
	match aux b with
	| ExFail(x,y) -> Error(x,y)
	| ExOK [] -> Error(AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Empty SNI extension")
	| ExOK l -> correct l
	end
      else
	Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse SNI list")

(* TODO: supported_groups and signature_algorithms *) 

// ExtensionType and Extension Table in https://tlswg.github.io/tls13-spec/#rfc.section.4.2 
noeq type extension =
  | E_server_name of list serverName (* M, AF *) (* RFC 6066 *)
  | E_supported_groups of list namedGroup (* M, AF *) (* RFC 7919 *)  
  | E_signature_algorithms of signatureSchemeList (* M, AF *) (* RFC 5246 *)
  | E_key_share of CommonDH.keyShare (* M, AF *)
  | E_pre_shared_key of (list psk) (* M, AF *)
  | E_early_data of earlyDataIndication
  | E_supported_versions of protocol_versions   (* M, AF *) 
  | E_cookie of b:bytes {0 < length b /\ length b < 65536}  (* M *)
  | E_psk_key_exchange_modes of client_psk_kexes (* client-only; mandatory when proposing PSKs *)  
  | E_extended_ms
  | E_ec_point_format of list ECGroup.point_format
  | E_unknown_extension of (lbytes 2 * bytes) (* header, payload *)
(* 
We do not yet support the extensions below (authenticated but ignored)
  | E_max_fragment_length
  | E_status_request
  | E_use_srtp 
  | E_heartbeat 
  | E_application_layer_protocol_negotiation
  | E_signed_certifcate_timestamp 
  | E_client_certificate_type 
  | E_server_certificate_type 
  | E_certificate_authorities 
  | E_oid_filters 
  | E_post_handshake_auth 
  | E_renegotiation_info of renegotiationInfo
*)

let string_of_extension = function
  | E_server_name _ -> "server_name"
  | E_supported_groups _ -> "supported_groups"
  | E_signature_algorithms _ -> "signature_algorithms"
  | E_key_share _ -> "key_share"
  | E_pre_shared_key _ -> "pre_shared_key"
  | E_early_data _ -> "early_data"
  | E_supported_versions _ -> "supported_versions"
  | E_cookie _ -> "cookie"
  | E_psk_key_exchange_modes _ -> "psk_key_exchange_modes"
  | E_extended_ms -> "extended_master_secret"
  | E_ec_point_format _ -> "ec_point_formats"
  | E_unknown_extension (n,_) -> print_bytes n

let rec string_of_extensions = function
  | e0 :: es -> string_of_extension e0 ^ " " ^ string_of_extensions es
  | [] -> ""

(** shallow equality *)
private let sameExt e1 e2 =
  match e1, e2 with
  | E_server_name _, E_server_name _ -> true
  | E_supported_groups _, E_supported_groups _ -> true 
  | E_signature_algorithms _, E_signature_algorithms _ -> true
  | E_key_share _, E_key_share _ -> true
  | E_pre_shared_key _, E_pre_shared_key _ -> true
  | E_early_data _, E_early_data _ -> true
  | E_supported_versions _, E_supported_versions _ -> true
  | E_cookie _, E_cookie _ -> true 
  | E_psk_key_exchange_modes _, E_psk_key_exchange_modes _ -> true
  | E_extended_ms, E_extended_ms -> true
  | E_ec_point_format _, E_ec_point_format _ -> true 
  // same, if the header is the same: mimics the general behaviour
  | E_unknown_extension(h1,_), E_unknown_extension(h2,_) -> equalBytes h1 h2
  | _ -> false

(*************************************************
 extension formatting
 *************************************************)

//17-05-05 no good reason to pattern match twice when formatting? follow the same structure as for parsing?
private val extensionHeaderBytes: extension -> lbytes 2
let extensionHeaderBytes ext =
  match ext with             // 4.2 ExtensionType enum value
  | E_server_name _            -> abyte2 (0x00z, 0x00z)
  | E_supported_groups _       -> abyte2 (0x00z, 0x0Az) // 10 
  | E_signature_algorithms _   -> abyte2 (0x00z, 0x0Dz) // 13
  | E_key_share _              -> abyte2 (0x00z, 0x28z) // 40
  | E_pre_shared_key _         -> abyte2 (0x00z, 0x29z) // 41
  | E_early_data _             -> abyte2 (0x00z, 0x2az) // 42
  | E_supported_versions _     -> abyte2 (0x00z, 0x2bz) // 43
  | E_cookie _                 -> abyte2 (0x00z, 0x2cz) // 44 
  | E_psk_key_exchange_modes _ -> abyte2 (0x00z, 0x2dz) // 45
  | E_extended_ms              -> abyte2 (0x00z, 0x17z) // 45
  | E_ec_point_format _        -> abyte2 (0x00z, 0x0Bz) // 11 
  | E_unknown_extension (h,b)  -> h

(* API *)

// Missing refinements in `extension` type constructors to be able to prove the length bound
(** Serializes an extension payload *)
val extensionPayloadBytes: extension -> b:bytes { length b < 65536 - 4 }
let rec extensionPayloadBytes = function
  | E_server_name []           -> empty_bytes // ServerHello, EncryptedExtensions
  | E_server_name l            -> vlbytes 2 (serverNameBytes l) // ClientHello
  | E_supported_groups l       -> namedGroupsBytes l  
  | E_signature_algorithms sha -> signatureSchemeListBytes sha
  | E_key_share ks             -> CommonDH.keyShareBytes ks
  | E_pre_shared_key psk       -> admit() //PSK.preSharedKeyBytes psk //17-04-21 TODO parse/format the list with ota
  | E_early_data edi           -> earlyDataIndicationBytes edi
  | E_supported_versions vv    ->
    // Sending TLS 1.3 draft versions, as other implementations are doing
    vlbytes 1 (List.Tot.fold_left (fun acc v -> acc @| versionBytes_draft v) empty_bytes vv)
  | E_cookie c                 -> (lemma_repr_bytes_values (length c); vlbytes 2 c)
  | E_psk_key_exchange_modes _ -> admit()
  | E_extended_ms              -> empty_bytes
  | E_ec_point_format l        -> ecpfListBytes l
  | E_unknown_extension (_,b)  -> b

(** Serializes an extension *)
val extensionBytes: ext:extension -> b:bytes { length b < 65536 }
let rec extensionBytes ext =
  let head = extensionHeaderBytes ext in
  let payload = extensionPayloadBytes ext in
  lemma_repr_bytes_values (length payload);
  let payload = vlbytes 2 payload in
  head @| payload

type extensions = 
  exts:list extension {repr_bytes (length (List.Tot.fold_left (fun l s -> l @| extensionBytes s) empty_bytes exts)) <= 2}

val extensionsBytes: extensions -> b:bytes { length b < 2 + 65536 }
let extensionsBytes exts =
  let b = List.Tot.fold_left (fun l s -> l @| extensionBytes s) empty_bytes exts in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

// opaque cert_data<1..2^24-1>
type cert = b:bytes {length b < 16777216}

// CertificateEntry certificate_list<0..2^24-1>;
// See https://tlswg.github.io/tls13-spec/#rfc.section.4.4.2
type chain = l:list cert // { ... }
type chain13 = l:list (cert * extensions) // { ... }


(*************************************************
 Extension parsing
**************************************************)

private val addOnce: extension -> list extension -> Tot (result (list extension))
let addOnce ext extList =
  if List.Tot.existsb (sameExt ext) extList then
    Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
  else
    let res = FStar.List.Tot.append extList [ext] in
    correct res

val parseEcpfList: bytes -> result (list ECGroup.point_format)
let parseEcpfList b =
    let rec aux: (b:bytes -> Tot (result (list ECGroup.point_format)) (decreases (length b))) = fun b -> 
        if equalBytes b empty_bytes then Correct []
        else if length b = 0 then error "malformed curve list" 
        else
          let u,v = split b 1 in
          ( match aux v with
            | Error z -> Error z 
            | Correct l ->
              let cur = 
              match cbyte u with
              | 0z -> ECGroup.ECP_UNCOMPRESSED
              | _ -> ECGroup.ECP_UNKNOWN(int_of_bytes u) in 
              Correct (cur :: l))
    in match aux b with
    | Error z -> Error z
    | Correct l -> 
      if List.Tot.mem ECGroup.ECP_UNCOMPRESSED l 
      then correct l
      else error "uncompressed point format not supported"

(* We don't care about duplicates, not formally excluded. *)

val parseExtension: role -> bytes -> result extension
let parseExtension role b =
  if length b < 4 then error "extension type: not enough bytes" else 
  let head, payload = split b 2 in
  match vlparse 2 payload with
  | Error (_,s) -> error ("extension: "^s)
  | Correct data -> ( 
    match cbyte2 head with
    | (0x00z, 0x00z) -> mapResult E_server_name (parseServerName role data)
    | (0x00z, 0x0Az) -> // supported groups
      if length data < 2 || length data >= 65538 then error "supported groups" else
      mapResult E_supported_groups (Parse.parseNamedGroups data)

    | (0x00z, 0x0Dz) -> // sigAlgs
      if length data < 2 ||  length data >= 65538 then error "supported signature algorithms" else 
      mapResult E_signature_algorithms (TLSConstants.parseSignatureSchemeList data)
      
    | (0x00z, 0x28z) -> mapResult E_key_share (CommonDH.parseKeyShare (Client? role) data)

    | (0x00z, 0x29z) -> // head TBD, PSK
      if length data < 2 then error "PSK" else 
      mapResult E_pre_shared_key (admit()) (* 17-04-21 TODO PSK.parsePreSharedKey data *) 

    | (0x00z, 0x2az) ->
      if length data <> 0 && length data <> 4 then error "early data indication" else
      mapResult E_early_data (parseEarlyDataIndication data)
    | (0x00z, 0x2bz) ->
      if length data <= 2 || length data >= 256 then error "supported versions" else
      mapResult E_supported_versions (parseSupportedVersions data)

    | (0xffz, 0x2cz) -> // cookie
      if length data <= 2 || length data >= 65538 then error "cookie" else
      Correct (E_cookie data)
      
    (* ToDo: | E_psk_key_exchange_modes _ *)

    | (0x00z, 0x17z) -> // extended ms
      if length data > 0 then error "extended master secret" else 
      Correct E_extended_ms
      
    | (0x00z, 0x0Bz) -> // ec point format
      if length data < 1 || length data >= 256 then error "ec point format" else (
      lemma_repr_bytes_values (length data);
      match vlparse 1 data with
      | Error z -> Error z
      | Correct ecpfs -> mapResult E_ec_point_format (parseEcpfList ecpfs))
      
    | _ -> Correct (E_unknown_extension (head,data)))

val parseExtensions: role -> b:bytes -> result (list extension)
let parseExtensions role b =
  let rec aux: 
    b:bytes -> list extension -> Tot (result (list extension)) (decreases (length b)) = fun b exts ->
    if length b >= 4 then
      let ht, b = split b 2 in
      match vlsplit 2 b with
      | Error(z) -> error "extension length"
      | Correct(ext, bytes) -> (
	(* assume (Prims.precedes (Prims.LexCons b) (Prims.LexCons (ht @| vlbytes 2 ext))); *)
	match parseExtension role (ht @| vlbytes 2 ext) with
	| Correct ext ->
	  (match addOnce ext exts with // fails if the extension already is in the list
	  | Correct exts -> aux bytes exts
	  | Error z -> Error z)
	| Error z -> Error z)
    else Correct exts in
  if length b < 2 then error "extensions" else
  match vlparse 2 b with
  | Correct b -> aux b []
  | Error z -> error "extensions" 

(* SI: API. Called by HandshakeMessages. *)
val parseOptExtensions: r:role -> data:bytes -> result (option (list extension))
let parseOptExtensions r data =
  if length data = 0 
  then Correct None
  else mapResult Some (parseExtensions r data)


(*************************************************
 Other extension functionality
 *************************************************)

(* JK: Need to get rid of such functions *)
private let rec list_valid_cs_is_list_cs (l:valid_cipher_suites): list cipherSuite =
  match l with 
  | [] -> [] 
  | hd :: tl -> hd :: list_valid_cs_is_list_cs tl
  
private let rec list_valid_ng_is_list_ng (l:list valid_namedGroup) : list namedGroup = 
  match l with 
  | [] -> [] 
  | hd :: tl -> hd :: list_valid_ng_is_list_ng tl

(* SI: API. Called by Nego. *)
(* RFC 4.2:
When multiple extensions of different types are present, the
extensions MAY appear in any order, with the exception of
“pre_shared_key” Section 4.2.10 which MUST be the last extension in
the ClientHello. There MUST NOT be more than one extension of the same
type in a given extension block.

RFC 8.2. ClientHello msg must: 
If not containing a “pre_shared_key” extension, it MUST contain both a
“signature_algorithms” extension and a “supported_groups” extension.
If containing a “supported_groups” extension, it MUST also contain a
“key_share” extension, and vice versa. An empty KeyShare.client_shares
vector is permitted.

*)

val prepareExtensions: 
  protocolVersion ->
  protocolVersion -> 
  k:valid_cipher_suites{List.Tot.length k < 256} -> 
  bool -> 
  bool -> 
  signatureSchemeList ->
  list (x:namedGroup{SEC? x \/ FFDHE? x}) -> 
  option (cVerifyData * sVerifyData) ->
  option CommonDH.keyShare -> 
  l:list extension{List.Tot.length l < 256}
(* SI: implement this using prep combinators, of type exts->data->exts, per ext group. 
   For instance, PSK, HS, etc extensions should all be done in one function each. 
   This seems to make this prepareExtensions more modular. *)
let prepareExtensions minpv pv cs sres sren sigAlgs namedGroups ri ks =
    let res = [] in 
    (* Always send supported extensions.
       The configuration options will influence how strict the tests will be *)
    (* let cri = *)
    (*    match ri with *)
    (*    | None -> FirstConnection *)
    (*    | Some (cvd, svd) -> ClientRenegotiationInfo cvd in *)
    (* let res = [E_renegotiation_info(cri)] in *)
    let res =
      match minpv, pv with
      | TLS_1p3, TLS_1p3 -> E_supported_versions [TLS_1p3] :: res
      | TLS_1p2, TLS_1p3 -> E_supported_versions [TLS_1p3;TLS_1p2] :: res
      // REMARK: The case below is not mandatory. This behaviour should be configurable
      // | TLS_1p2, TLS_1p2 -> E_supported_versions [TLS_1p2] :: res
      | _ -> res
    in
    let res = 
      match pv, ks with
      | TLS_1p3, Some ks -> E_key_share ks::res
      | _,_ -> res
    in
    // Include extended_master_secret when resuming
    let res = if sres then E_extended_ms :: res else res in
    let res = E_signature_algorithms sigAlgs :: res in
    let res =
      if List.Tot.existsb isECDHECipherSuite (list_valid_cs_is_list_cs cs) then
	E_ec_point_format [ECGroup.ECP_UNCOMPRESSED] :: res
      else res
    in
    let res =
      if List.Tot.existsb (fun cs -> isDHECipherSuite cs || CipherSuite13? cs) (list_valid_cs_is_list_cs cs) then
        E_supported_groups (list_valid_ng_is_list_ng namedGroups) :: res
      else res
    in
    assume (List.Tot.length res < 256);  // JK: Specs in type config in TLSInfo unsufficient
    res

(*
// TODO the code above is too restrictive, should support further extensions
// TODO we need an inverse; broken due to extension ordering. Use pure views instead?
val matchExtensions: list extension{List.Tot.length l < 256} -> Tot ( 
  protocolVersion *
  k:valid_cipher_suites{List.Tot.length k < 256} *
  bool *
  bool * 
  list signatureScheme -> list (x:namedGroup{SEC? x \/ FFDHE? x}) *
  option (cVerifyData * sVerifyData) *
  option CommonDH.keyShare )
let matchExtensions ext = admit()

let prepareExtensions_inverse pv cs sres sren sigAlgs namedGroups ri ks:
  Lemma(
    matchExtensions (prepareExtensions pv cs sres sren sigAlgs namedGroups ri ks) =
    (pv, cs, sres, sren, sigAlgs, namedGroups, ri, ks)) = ()
*)

(*************************************************
 SI: 
 The rest of the code might be dead. 
 Some of the it is called by Nego, but it might be that
 it needs to move to Nego. 
 *************************************************)

(* SI: is renego deadcode? *)
(*
type renegotiationInfo =
  | FirstConnection
  | ClientRenegotiationInfo of (cVerifyData)
  | ServerRenegotiationInfo of (cVerifyData * sVerifyData)

val renegotiationInfoBytes: renegotiationInfo -> Tot bytes
let renegotiationInfoBytes ri =
  match ri with
  | FirstConnection ->
    lemma_repr_bytes_values 0;
    vlbytes 1 empty_bytes
  | ClientRenegotiationInfo(cvd) ->
    lemma_repr_bytes_values (length cvd);
    vlbytes 1 cvd
  | ServerRenegotiationInfo(cvd, svd) ->
    lemma_repr_bytes_values (length (cvd @| svd));
    vlbytes 1 (cvd @| svd)

val parseRenegotiationInfo: pinverse_t renegotiationInfoBytes
let parseRenegotiationInfo b =
  if length b >= 1 then
    match vlparse 1 b with
    | Correct(payload) ->
	let (len, _) = split b 1 in
	(match int_of_bytes len with
	| 0 -> Correct (FirstConnection)
	| 12 | 36 -> Correct (ClientRenegotiationInfo payload) // TLS 1.2 / SSLv3 client verify data sizes
	| 24 -> // TLS 1.2 case
	    let cvd, svd = split payload 12 in
	    Correct (ServerRenegotiationInfo (cvd, svd))
	| 72 -> // SSLv3
	    let cvd, svd = split payload 36 in
	    Correct (ServerRenegotiationInfo (cvd, svd))
	| _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Inappropriate length for renegotiation info data (expected 12/24 for client/server in TLS1.x, 36/72 for SSL3"))
    | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse renegotiation info length")
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Renegotiation info bytes are too short")
*)


// TODO
// ADL the negotiation of renegotiation indication is incorrect
// ADL needs to be consistent with clientToNegotiatedExtension
private val serverToNegotiatedExtension: config -> list extension -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> result negotiatedExtensions -> extension -> Tot (result (negotiatedExtensions))
let serverToNegotiatedExtension cfg cExtL cs ri (resuming:bool) res sExt : result (negotiatedExtensions)=
    match res with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
      if List.Tot.existsb (sameExt sExt) cExtL then
      match sExt with
(*
      | E_renegotiation_info (sri) ->
	(match sri, replace_subtyping ri with
	| FirstConnection, None -> correct ({l with ne_secure_renegotiation = RI_Valid})
	| ServerRenegotiationInfo(cvds,svds), Some(cvdc, svdc) ->
	   if equalBytes cvdc cvds && equalBytes svdc svds then
	      correct ({l with ne_secure_renegotiation = RI_Valid})
	   else
	      Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Mismatch in contents of renegotiation indication")
	| _ -> Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Detected a renegotiation attack"))
*)
      | E_server_name _ ->
	  if List.Tot.existsb (fun x->match x with |E_server_name _ -> true | _ -> false) cExtL then
            correct(l)
	  else
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an SNI acknowledgement without an SNI provided")
      | E_extended_ms -> correct ({l with ne_extended_ms = true})
      | E_ec_point_format spf ->
	  if resuming then
            correct l
          else
            correct ({l with ne_supported_point_formats = Some spf})
      | E_key_share (CommonDH.ServerKeyShare sks) ->
        Correct ({l with ne_keyShare = Some sks})
      | E_supported_groups named_group_list ->
        Correct ({l with ne_supported_groups = Some named_group_list})
      | _ -> Error (AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Unexpected pattern in serverToNegotiatedExtension")
     else
       Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an extension not present in client hello")


(* SI: API. Called by Negotiation. *)
val negotiateClientExtensions: protocolVersion -> config -> option (list extension) -> option (list extension) -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> Tot (result (negotiatedExtensions))
let negotiateClientExtensions pv cfg cExtL sExtL cs ri (resuming:bool) =
  match pv with
  | SSL_3p0 ->
     begin
     match sExtL with
     | None -> Correct ne_default
     | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Received extensions in SSL 3.0 server hello")
     end
  | _ ->
     begin 
     match cExtL, sExtL with
     | Some cExtL, Some sExtL -> (
        let nes = ne_default in
        match List.Tot.fold_left (serverToNegotiatedExtension cfg cExtL cs ri resuming) (correct nes) sExtL with
        | Error(x,y) -> Error(x,y)
        | Correct l ->
          if resuming then correct l
          else
	  begin
	    match List.Tot.tryFind E_signature_algorithms? cExtL with
	    | Some (E_signature_algorithms shal) ->
	      correct({l with ne_signature_algorithms = Some shal})
	    | None -> correct l
	    | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Unappropriate sig algs in negotiateClientExtensions")
	  end )
     | _, None -> 
       if pv <> TLS_1p3 then Correct ne_default
       else Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "negoClientExts missing extensions in TLS hello message")
     | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "negoClientExts missing extensions in TLS hello message")
     end 

private val clientToServerExtension: protocolVersion -> config -> cipherSuite -> option (cVerifyData * sVerifyData) -> option CommonDH.keyShare -> bool -> extension -> option extension
let clientToServerExtension pv cfg cs ri ks resuming cext =
  match cext with
  | E_key_share _ ->
    Option.map E_key_share ks // ks should be in one of client's groups
  | E_server_name server_name_list ->
    begin
    // See https://tools.ietf.org/html/rfc6066
    match pv, List.Tot.tryFind SNI_DNS? server_name_list with
    | TLS_1p3, _   -> None // TODO: SNI goes in EncryptedExtensions in TLS 1.3
    | _, Some name -> Some (E_server_name []) // Acknowledge client's choice
    | _ -> None
    end
  | E_extended_ms -> Some E_extended_ms // REMARK: not depending on cfg.safe_resumption
  | E_ec_point_format ec_point_format_list -> // REMARK: ignores client's list
    if resuming || pv = TLS_1p3 then
      None // No ec_point_format in TLS 1.3
    else
      Some (E_ec_point_format [ECGroup.ECP_UNCOMPRESSED])
  | E_supported_groups named_group_list -> // REMARK: Purely informative
    Some (E_supported_groups (list_valid_ng_is_list_ng cfg.namedGroups)) 
  // TODO: handle all remaining cases
  | E_early_data b -> None
  | E_pre_shared_key b -> None
  | _ -> None

(* SI: API. Called by Handshake. *)
val negotiateServerExtensions: protocolVersion -> option (list extension) -> valid_cipher_suites -> config -> cipherSuite -> option (cVerifyData * sVerifyData) -> option CommonDH.keyShare -> bool -> result (option (list extension))
let negotiateServerExtensions pv cExtL csl cfg cs ri ks resuming =
   match cExtL with
   | Some cExtL ->
     let sexts = List.Tot.choose (clientToServerExtension pv cfg cs ri ks resuming) cExtL in
     Correct (Some sexts)
   | None ->
     begin
     match pv with
(* SI: deadcode ?
       | SSL_3p0 ->
          let cre =
              if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (list_valid_cs_is_list_cs csl) then
                 Some [E_renegotiation_info (FirstConnection)] //, {ne_default with ne_secure_renegotiation = RI_Valid})
              else None //, ne_default in
          in Correct cre
*)	  
     | _ -> 
       Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "No extensions in ClientHello")
     end

// https://tools.ietf.org/html/rfc5246#section-7.4.1.4.1
private val default_signatureScheme_fromSig: protocolVersion -> sigAlg ->
  ML (l:list signatureScheme{List.Tot.length l == 1})
let default_signatureScheme_fromSig pv sigAlg =
  let open CoreCrypto in
  let open Hashing.Spec in
  match sigAlg with
  | RSASIG ->
    begin
    match pv with
    | TLS_1p2 -> [ RSA_PKCS1_SHA1 ]
    | TLS_1p0 | TLS_1p1 | SSL_3p0 -> [ RSA_PKCS1_SHA1 ] // was MD5SHA1
    | TLS_1p3 -> unexpected "[default_signatureScheme_fromSig] invoked on TLS 1.3"
    end
  | ECDSA -> [ ECDSA_SHA1 ]
  | _ -> unexpected "[default_signatureScheme_fromSig] invoked on an invalid signature algorithm"

(* SI: API. Called by HandshakeMessages. *)
val default_signatureScheme: protocolVersion -> cipherSuite -> ML signatureSchemeList
let default_signatureScheme pv cs =
  default_signatureScheme_fromSig pv (sigAlg_of_ciphersuite cs)
