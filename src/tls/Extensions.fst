(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
(**
This modules defines TLS 1.3 Extensions. 

- An ast, and it's associated parsing and formatting functions. 
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

noeq type psk = 
  // this is the truncated PSK extension, without the list of binder tags.
  | ClientPSK of list (PSK.preSharedKey * PSK.obfuscated_ticket_age)
  // this is just an index in the client offer's PSK extension
  | ServerPSK of UInt16.t 

// https://tlswg.github.io/tls13-spec/#rfc.section.4.2.8
// restricting both proposed PSKs and future ones sent by the server
// will also be used in the PSK table, and possibly in the configs
type psk_kex =
  | PSK_KE 
  | PSK_DHE_KE 

type client_psk_kexes = l:list psk_kex 
  { l = [PSK_KE] \/ l = [PSK_DHE_KE] \/ l = [PSK_KE; PSK_DHE_KE] \/ l = [PSK_DHE_KE; PSK_KE] }

// The length reflects the RFC format constraint <2..254> 
type protocol_versions =
  l:list protocolVersion {0 < List.Tot.length l /\ List.Tot.length l < 128}

type earlyDataIndication = option UInt32.t // Only Some for NewSessionTicket

(** RFC 4.2 'Extension' Table's type definition. *)
noeq 
type extension =
  | E_server_name of list serverName (* M, AF *) (* RFC 6066 *)
  | E_supported_groups of list namedGroup (* M, AF *) (* RFC 7919 *)  
  | E_signature_algorithms of signatureSchemes (* M, AF *) (* RFC 5246 *)
  | E_key_share of CommonDH.keyShare (* M, AF *)
  | E_pre_shared_key of (list psk) (* M, AF *)
  | E_early_data of earlyDataIndication
  | E_supported_versions of protocol_versions   (* M, AF *) 
  | E_cookie of b:bytes {0 < length b /\ length b < 65536}  (* M *)
  | E_psk_key_exchange_modes of client_psk_kexes (* client-only; mandatory when proposing PSKs *)  | E_extended_ms
  | E_ec_point_format of list ECGroup.point_format
  | E_unknown_extension of (lbytes 2 * bytes) (* header, payload *)
(*
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

(* string_of_ *)
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

private val serverNameBytes: list serverName -> Tot bytes
let serverNameBytes l =
  let rec (aux:list serverName -> Tot bytes) = function
  | [] -> empty_bytes
  | SNI_DNS(x) :: r -> (abyte 0z) @| bytes_of_int 2 (length x) @| x @| aux r
  | SNI_UNKNOWN(t, x) :: r -> (bytes_of_int 1 t) @| bytes_of_int 2 (length x) @| x @| aux r
  in
  (aux l)
 
val earlyDataIndicationBytes: edi:earlyDataIndication -> Tot bytes
let earlyDataIndicationBytes = function
  | None -> empty_bytes // ClientHello, EncryptedExtensions
  | Some max_early_data_size -> // NewSessionTicket
    let n = UInt32.v max_early_data_size in    
    lemma_repr_bytes_values n;
    bytes_of_int 4 n

let rec ecpfListBytes_aux : list ECGroup.point_format -> bytes = function
  | [] -> empty_bytes
  | ECGroup.ECP_UNCOMPRESSED :: r -> (abyte 0z) @| ecpfListBytes_aux r
  | ECGroup.ECP_UNKNOWN t :: r -> (bytes_of_int 1 t) @| ecpfListBytes_aux r

val ecpfListBytes: l:list ECGroup.point_format{length (ecpfListBytes_aux l) < 256} -> Tot bytes
let ecpfListBytes l =
  let al = ecpfListBytes_aux l in
  lemma_repr_bytes_values (length al);
  let bl:bytes = vlbytes 1 al in
  bl

(* API *)

// Missing refinements in `extension` type constructors to be able to prove the length bound
(** Serializes an extension payload *)
val extensionPayloadBytes: extension -> b:bytes { length b < 65536 - 4 }
let rec extensionPayloadBytes = function
  | E_server_name []           -> empty_bytes // ServerHello, EncryptedExtensions
  | E_server_name l            -> vlbytes 2 (serverNameBytes l) // ClientHello
  | E_supported_groups l       -> namedGroupsBytes l  
  | E_signature_algorithms sha -> signatureSchemesBytes sha
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
type chain = l:list (cert * extensions) // { ... }


(*************************************************
 Extension parsing
**************************************************)

//17-05-01 why not using TLSError.result ?? 
// SZ: NO idea. We should.
(** local, failed-to-parse exc. *)
private type canFail (a:Type) =
| ExFail of alertDescription * string
| ExOK of list a

private val parseserverName: r:role -> b:bytes -> result (list serverName)
let parseserverName r b  =
  let rec aux: b:bytes -> Tot (canFail serverName) (decreases (length b)) = fun b ->
    if length b = 0 then ExOK []
    else if length b >= 3 then
      let ty,v = split b 1 in
      begin
      match vlsplit 2 v with
      | Error (x,y) ->
	ExFail (x, "Failed to parse SNI length: "^ (Platform.Bytes.print_bytes b))
      | Correct (cur, next) ->
	begin
	match aux next with
	| ExFail z -> ExFail z
	| ExOK l ->
	  let cur =
	    begin
	    match cbyte ty with
	    | 0z -> SNI_DNS cur
	    | v  -> SNI_UNKNOWN (int_of_bytes ty, cur)
	    end
	  in
	  let snidup: serverName -> Tot bool = fun x ->
	    begin
	    match x,cur with
	    | SNI_DNS _, SNI_DNS _ -> true
	    | SNI_UNKNOWN (a,_), SNI_UNKNOWN (b,_) -> a = b
	    | _ -> false
	    end
	  in
	  if List.Tot.existsb snidup l then
	    ExFail(AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Duplicate SNI type")
	  else ExOK (cur :: l)
	end
      end
    else ExFail (AD_decode_error, "Failed to parse SNI")
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
          | ExFail z -> Error z
          | ExOK [] -> Error (AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Empty SNI extension")
          | ExOK l -> correct l
        end
      else
        Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse SNI list")

private let err_msg s = "Got inapproprite bytes for " ^ s

private val addOnce: extension -> list extension -> Tot (result (list extension))
let addOnce ext extList =
  if List.Tot.existsb (sameExt ext) extList then
    Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
  else
    let res = FStar.List.Tot.append extList [ext] in
    correct res

val parseEcpfList: bytes -> result (list ECGroup.point_format)
let parseEcpfList b =
  let rec aux:b:bytes -> Tot (canFail (ECGroup.point_format)) (decreases (length b)) = fun b ->
    if equalBytes b empty_bytes then ExOK []
    else
      if 0 < length b then 
        let u, v = split b 1 in
        begin
	match aux v with
	| ExFail (x, y) -> ExFail (x, y)
	| ExOK l ->
	  let cur = 
            match cbyte u with
	    | 0z -> ECGroup.ECP_UNCOMPRESSED
	    | _  -> ECGroup.ECP_UNKNOWN (int_of_bytes u)
	  in ExOK (cur :: l)
        end
      else ExFail (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Malformed curve list")
  in
  match aux b with
  | ExFail z -> Error z
  | ExOK l -> 
    if List.Tot.mem ECGroup.ECP_UNCOMPRESSED l then
      correct l
    else
      Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Uncompressed point format not supported")


//17-05-01 added a refinement to control the list length; this function verifies.
//17-05-01 should we use generic code to parse such bounded lists?
//REMARK: We don't care about duplicates, not formally excluded.
//REMARK: This is not tail recursive, contrary to most of our parsing functions
val parseVersions: 
  b:bytes -> 
  Tot (result (l:list protocolVersion {length b == FStar.Mul.(2 * List.Tot.length l)}))
      (decreases (length b))
let rec parseVersions b =
  match length b with 
  | 0 -> let r = [] in assert_norm (List.Tot.length [] = 0); Correct r
  | 1 -> Error (AD_decode_error, "malformed version list")
  | _ -> 
    let b2, b' = split b 2 in
    match parseVersion_draft b2 with
    | Error z -> Error z
    | Correct v -> 
      match parseVersions b' with 
      | Error z -> Error z 
      | Correct vs ->
        begin
 	let r = v::vs in 
	assert_norm (List.Tot.length (v::vs) = 1 + List.Tot.length vs); // did not find usable length lemma in List.Tot
	Correct r
        end
  
val parseSupportedVersions: b:bytes{2 < length b /\ length b < 256} -> result protocol_versions
let parseSupportedVersions b =
  match vlparse 1 b with
  | Correct b ->
    begin
    match parseVersions b with // Necessary for verification
    | Correct l -> Correct l
    | Error z -> Error z
    end
  | Error z -> Error z

val parseEarlyDataIndication: b:bytes{length b == 0 \/ length b == 4} -> earlyDataIndication
let parseEarlyDataIndication b =
  if length b = 0 then None
  else
    begin
    let n = int_of_bytes b in
    lemma_repr_bytes_values n;
    assert_norm (pow2 32 == 4294967296);
    Some (UInt32.uint_to_t n)
    end

val parseExtension: role -> b:bytes -> result extension
let rec parseExtension role b =
  if length b < 4 then
    Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Extension bytes are too short to store even the extension type")
  else
    let head, payload = split b 2 in
    match vlparse 2 payload with
    | Error _ -> 
      Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extension length 1")
    | Correct data ->
      begin
      match cbyte2 head with
      | (0x00z, 0x00z) -> // SNI
        mapResult E_server_name (parseserverName role data)
      | (0x00z, 0x0Az) -> // supported groups
        if 2 <= length data && length data < 65538 then
         (match parseNamedGroups data with
          | Correct l -> Correct (E_supported_groups l)
          | Error z -> Error z)
        else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "SNI"))
      | (0x00z, 0x0Dz) -> // sigAlgs
        if 2 <= length data && length data < 65538 then
          (match parseSignatureSchemes data with
           | Correct algs -> Correct (E_signature_algorithms algs)
           | Error z -> Error z)
        else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "sigAlgs"))
      | (0x00z, 0x28z) -> // keyShare
        (match CommonDH.parseKeyShare (Client? role) data with
         | Correct ks -> Correct (E_key_share ks)
         | Error z -> Error z)
      | (0x00z, 0x29z) -> // head TBD, PSK
        if length data >= 2 then
          (match admit() (* 17-04-21 TODO PSK.parsePreSharedKey data *) with
           | Correct psk -> Correct psk
           | Error z -> Error z)
        else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "PSK"))
      | (0x00z, 0x2az) -> // EDI
        if length data = 0 || length data = 4 then
          (match parseEarlyDataIndication data with
           | None -> Correct (E_early_data None)
           | Some n -> Correct (E_early_data (Some n)))
        else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "early_data")) 
      | (0x00z, 0x2bz) -> // supported_versions
        if 2 < length data && length data < 256 then
          (match parseSupportedVersions data with
           | Correct v -> Correct (E_supported_versions v)
           | Error z -> Error z)
        else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "supported_versions"))
      | (0xffz, 0x2cz) -> // cookie
        if 0 < length data && length data < 65536 then
	  Correct (E_cookie data)
	else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "cookie"))
(* ToDo: | E_psk_key_exchange_modes _ *)
(*
	| (0xFFz, 0x01z) -> // renego (* OLD *)
	  (match parseRenegotiationInfo data with
	  | Correct(ri) -> Correct (E_renegotiation_info(ri))
	  | Error z -> Error z
*)	 
	| (0x00z, 0x17z) -> // extended ms
	  if length data = 0 then Correct (E_extended_ms)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for extended MS extension")
	| (0x00z, 0x0Bz) -> // ec point format
	  if 1 <= length data && length data < 256 then
	    (lemma_repr_bytes_values (length data);
	     match vlparse 1 data with
	     | Error z -> Error z
	     | Correct data ->
	       match parseEcpfList data with
	       | Correct ecpfs -> Correct (E_ec_point_format ecpfs)
	       | Error z -> Error z)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "ec_point_fmt"))
	| _ -> // Unknown extension
          Correct (E_unknown_extension (head,data))
        end

val parseExtensions: role -> b:bytes -> result (list extension)
let rec parseExtensions role b =
  let rec aux: 
    b:bytes -> list extension -> Tot (result (list extension)) (decreases (length b)) = fun b exts ->
    if length b >= 4 then
      let ht, b = split b 2 in
      match vlsplit 2 b with
      | Correct (ext, bytes) ->
        begin
	match parseExtension role (ht @| vlbytes 2 ext) with
	| Correct ext ->
          begin
	  match addOnce ext exts with // fails if the extension already is in the list
	  | Correct exts -> aux bytes exts
	  | Error z -> Error z
          end
	| Error z -> Error z
        end
      | Error z -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extension length 2")
    else Correct exts in
  if length b >= 2 then
    match vlparse 2 b with
    | Correct b -> aux b []
    | Error z -> 
      Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Incorrect extension data length")
  else 
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extensions length")

(* SI: API. Called by HandshakeMessages. *)
val parseOptExtensions: r:role -> data:bytes -> result (option (list extension))
let parseOptExtensions r data =
  if length data = 0 then Correct None
  else mapResult Some (parseExtensions r data)


(*************************************************
 Other extension functionality
 *************************************************)

(* JK: Need to get rid of such functions *)
(* API. Called by Negotiation *)
let rec list_valid_cs_is_list_cs (l:valid_cipher_suites): list cipherSuite =
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
  signatureSchemes -> 
  list (x:namedGroup{SEC? x \/ FFDHE? x}) -> 
  option (cVerifyData * sVerifyData) ->
  option CommonDH.keyShare -> 
  l:list extension{List.Tot.length l < 256}
(* SI: implement this using prep combinators, of type exts->data->exts, per ext group. 
   For instance, PSK, HS, etc extensions should all be done in one function each. 
   This seems to make this prepareExtensions more modular. *)
let prepareExtensions minpv pv cs sres sren sigAlgs namedGroups ri ks =
    let res = [] in 
    (* Always send supported extensions. The configuration options will influence how strict the tests will be *)
// SI: is renego deadcode? 
    (* let cri = *)
    (*    match ri with *)
    (*    | None -> FirstConnection *)
    (*    | Some (cvd, svd) -> ClientRenegotiationInfo cvd in *)
    (* let res = [E_renegotiation_info(cri)] in *)
//    let res = (E_draftVersion (abyte2 (0z, 13z)))::res in
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
  list sigHashAlg -> list (x:namedGroup{SEC? x \/ FFDHE? x}) *
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

(* TODO: remove *)
private val replace_subtyping: (o:(option (cVerifyData * sVerifyData))) -> Tot (option (bytes*bytes))
let replace_subtyping (o:(option (cVerifyData * sVerifyData))) : Tot (option (bytes*bytes)) =
  match o with
  | None -> None
  | Some (a,b) -> Some (a,b)

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
// SI:. What's happened to E_renego?
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
(* not allowed for server
      | E_signature_algorithms sha ->
          if resuming then correct l
	  else correct ({l with ne_signature_algorithms = Some (sha)})
*)
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
private val default_sigHashAlg_fromSig: protocolVersion -> sigAlg ->
  ML (l:list signatureScheme{List.Tot.length l == 1})
let default_sigHashAlg_fromSig pv sigAlg =
  let open CoreCrypto in
  let open Hashing.Spec in
  match sigAlg with
  | RSASIG ->
    begin
    match pv with
    | TLS_1p2 -> [ RSA_PKCS1_SHA1 ]
    | TLS_1p0 | TLS_1p1 | SSL_3p0 -> [ RSA_PKCS1_SHA1 ] // was MD5SHA1
    | TLS_1p3 -> unexpected "[default_sigHashAlg_fromSig] invoked on TLS 1.3"
    end
  | ECDSA -> [ ECDSA_SHA1 ]
  | _ -> unexpected "[default_sigHashAlg_fromSig] invoked on an invalid signature algorithm"

(* SI: API. Called by HandshakeMessages. *)
val default_sigHashAlg: protocolVersion -> cipherSuite -> ML signatureSchemes
let default_sigHashAlg pv cs =
  default_sigHashAlg_fromSig pv (sigAlg_of_ciphersuite cs)


(* Dead code?

val sigHashAlg_contains: list sigHashAlg -> sigHashAlg -> Tot bool
let sigHashAlg_contains (algList:list sigHashAlg) (alg:sigHashAlg) =
    List.Tot.mem alg algList

val sigHashAlg_bySigList: list sigHashAlg -> list sigAlg -> Tot (list sigHashAlg)
let sigHashAlg_bySigList (algList:list sigHashAlg) (sigAlgList:list sigAlg) =
    List.Tot.choose (fun alg -> let (sigA,_) = alg in if (List.Tot.existsb (fun a -> a = sigA) sigAlgList) then Some(alg) else None) algList

val cert_type_to_SigHashAlg: certType -> protocolVersion -> ML (list sigHashAlg)
let cert_type_to_SigHashAlg ct pv =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> default_sigHashAlg_fromSig pv CoreCrypto.DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> default_sigHashAlg_fromSig pv CoreCrypto.RSASIG

val cert_type_list_to_SigHashAlg: list certType -> protocolVersion -> ML (list sigHashAlg)
let rec cert_type_list_to_SigHashAlg ctl pv =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> List.Tot.(cert_type_to_SigHashAlg h pv @ cert_type_list_to_SigHashAlg t pv)

val cert_type_to_SigAlg: certType -> Tot sigAlg
let cert_type_to_SigAlg ct =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> CoreCrypto.DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> CoreCrypto.RSASIG

val cert_type_list_to_SigAlg: list certType -> ML (list sigAlg)
let rec cert_type_list_to_SigAlg ctl =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> (cert_type_to_SigAlg h) :: (cert_type_list_to_SigAlg t)

val cert_type_to_SigHashAlg: certType -> protocolVersion -> list sigHashAlg
let cert_type_to_SigHashAlg ct pv =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> default_sigHashAlg_fromSig pv DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> default_sigHashAlg_fromSig pv RSASIG
*)
