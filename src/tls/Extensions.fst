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

module TI = TLSInfo

(*************************************************
 Define extension. 
 *************************************************)

type psk = 
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

(** RFC 4.2 'Extension' Table's type definition. *)
noeq type preEarlyDataIndication : Type0 =
  { ped_configuration_id: configurationId;
    ped_cipher_suite:valid_cipher_suite;
    ped_extensions:list extension;
    ped_context:b:bytes{length b < 256};
    //ped_early_data_type:earlyDataType;
    }
and earlyDataIndication =
  | ClientEarlyDataIndication of preEarlyDataIndication
  | ServerEarlyDataIndication
(* SI: we currently only define Mandatory-to-Implement Extensions 
   as listed in the RFC's Section 8.2. Labels in the variants below are: 
     M  - "MUST implement"
     AF - "MUST ... when offering applicable features" *)
and extension =
  | E_server_name of list TI.serverName (* M, AF *) (* RFC 6066 *)
(*| E_max_fragment_length
  | E_status_request *)
  | E_supported_groups of list namedGroup (* M, AF *) (* RFC 7919 *)  
  | E_signature_algorithms of (list sigHashAlg) (* M, AF *) (* RFC 5246 *)
(*| E_use_srtp 
  | E_heartbeat 
  | E_application_layer_protocol_negotiation
  | E_signed_certifcate_timestamp 
  | E_client_certificate_type 
  | E_server_certificate_type 
  | E_padding *)
  | E_key_share of CommonDH.keyShare (* M, AF *)
  | E_pre_shared_key of (list psk) (* M, AF *)
  | E_early_data of earlyDataIndication
  | E_supported_versions of list TLSConstants.protocolVersion (* M, AF *) 
  | E_cookie of b:bytes { 1 <= length b /\ length b <= (pow2 16 - 1)}  (* M *)
  | E_psk_key_exchange_modes of client_psk_kexes (* client-only; mandatory when proposing PSKs *)  
(*| E_certificate_authorities 
  | E_oid_filters 
  | E_post_handshake_auth *)
// Previous extension types
(*| E_renegotiation_info of renegotiationInfo 
  | E_extended_ms 
  | E_extended_padding *)
  | E_ec_point_format of list ECGroup.point_format
  | E_unknown_extension of (lbytes 2 * bytes) (* un-{implemented,known} extensions. *)


(* string_of_ *)
let string_of_extension = function
  | E_server_name _ -> "SNI" 
  | E_supported_groups _ -> "groups" 
  | E_signature_algorithms _ -> "sigAlgs"
  | E_key_share _ -> "keyShare" 
  | E_pre_shared_key _ -> "PSK"
  | E_early_data _ -> "EDI"
  | E_supported_versions _ -> "versions"
  | E_cookie _ -> "cookie"
  | E_psk_key_exchange_modes _ -> "psk_kex_modes"
  | E_ec_point_format _ -> "ec_point_fmt" 
  | E_unknown_extension (n,_) -> print_bytes n

let rec string_of_extensions = function
  | e0::es -> string_of_extension e0^" "^string_of_extensions es
  | []  -> ""

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
  | E_ec_point_format _, E_ec_point_format _ -> true 
  // same, if the header is the same: mimics the general behaviour
  | E_unknown_extension(h1,_), E_unknown_extension(h2,_) -> equalBytes h1 h2
  | _ -> false

(*************************************************
 extension formatting
 *************************************************)
 
private val extensionHeaderBytes: extension -> Tot bytes
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
  | E_ec_point_format _        -> abyte2 (0x00z, 0x0Bz) // 11 
  | E_unknown_extension(h,b) -> h

private val serverNameBytes: list TI.serverName -> Tot bytes
let serverNameBytes l =
    let rec (aux:list TI.serverName -> Tot bytes) = function
    | [] -> empty_bytes
    | TI.SNI_DNS(x) :: r -> (abyte 0z) @| bytes_of_int 2 (length x) @| x @| aux r
    | TI.SNI_UNKNOWN(t, x) :: r -> (bytes_of_int 1 t) @| bytes_of_int 2 (length x) @| x @| aux r
    in
    (aux l)

private val extension_depth : extension -> Tot nat
let rec extension_depth (ext:extension): Tot nat =
  match ext with
  | E_early_data edt           -> (
      match edt with
      | ServerEarlyDataIndication -> 0
      | ClientEarlyDataIndication edi -> 1 + extensions_depth edi.ped_extensions
      )
  | _ -> 0
and extensions_depth (exts:list extension): Tot nat =
  match exts with
  | [] -> 0
  | hd::tl -> let x = extensions_depth tl in
	     let y = extension_depth hd in
	     if y > x then y else x

val earlyDataIndicationBytes: edi:earlyDataIndication -> Tot bytes
  (decreases (fun edi -> match edi with | ClientEarlyDataIndication edi -> extensions_depth edi.ped_extensions | _ -> 0))
val extensionPayloadBytes: role -> ext:extension -> Tot bytes
  (decreases (extension_depth ext))

let rec (ecpfListBytes_aux:list ECGroup.point_format -> Tot bytes) =
  function
  | [] -> empty_bytes
  | ECGroup.ECP_UNCOMPRESSED :: r -> (abyte 0z) @| ecpfListBytes_aux r
  | ECGroup.ECP_UNKNOWN(t) :: r -> (bytes_of_int 1 t) @| ecpfListBytes_aux r

val ecpfListBytes: l:list ECGroup.point_format{length (ecpfListBytes_aux l) < 256} -> Tot bytes
let ecpfListBytes l =
  let al = ecpfListBytes_aux l in
  lemma_repr_bytes_values (length al);
  let bl:bytes = vlbytes 1 al in
  bl
  
(* API *)
(** Serialize extension. *)
val extensionBytes: role -> ext:extension -> Tot bytes
  (decreases (extension_depth ext))
val extensionsBytes: role -> cl:list extension -> Tot (b:bytes{length b <= 2 + 65535})
  (decreases (extensions_depth cl))

let rec earlyDataIndicationBytes edi =
  match edi with
  | ServerEarlyDataIndication -> empty_bytes
  | ClientEarlyDataIndication edi ->
      let cid_bytes = configurationIdBytes edi.ped_configuration_id in
      let cs_bytes = cipherSuiteBytes edi.ped_cipher_suite in
      let ext_bytes = extensionsBytes Client edi.ped_extensions in
      lemma_repr_bytes_values (length edi.ped_context);
      let context_bytes = vlbytes 1 edi.ped_context in
//      let edt_bytes = earlyDataTypeBytes edi.ped_early_data_type in
      cid_bytes @| cs_bytes @| ext_bytes @| context_bytes //@| edt_bytes
and extensionPayloadBytes role ext =
  match ext with
  | E_server_name(l)           -> 
      if role = Client then vlbytes 2 (serverNameBytes l) 
      else serverNameBytes l
  | E_supported_groups(l)      -> Parse.namedGroupsBytes l  
  | E_signature_algorithms sha -> sigHashAlgsBytes sha
  | E_key_share ks             -> CommonDH.keyShareBytes ks
  | E_pre_shared_key psk -> admit() //PSK.preSharedKeyBytes psk //17-04-21 TODO parse/format the list with ota
  | E_early_data edt           -> earlyDataIndicationBytes edt
  | E_supported_versions vv    -> 
      List.Tot.fold_left (fun acc v -> acc @| TLSConstants.versionBytes v) empty_bytes vv
  | E_cookie c                 -> c // SI: check 
  | E_psk_key_exchange_modes _ -> admit()
  | E_ec_point_format(l)       -> ecpfListBytes l
  | E_unknown_extension(h,b)   -> b
and extensionBytes role ext =
    let head = extensionHeaderBytes ext in
    let payload = extensionPayloadBytes role ext in
    let payload = vlbytes 2 payload in
    head @| payload
and extensionsBytes role exts =
  vlbytes 2 (List.Tot.fold_left (fun l s -> l @| extensionBytes role s) empty_bytes exts)

(* JK: For some reason without that I do not manage to get the
definition of extensionsBytes *)
assume val extensionsBytes_def: r:role -> 
  cl:list extension{repr_bytes (length (List.Tot.fold_left (fun l s -> l @| extensionBytes r s) empty_bytes cl)) <= 2} ->
  Lemma (requires (True))
	(ensures (extensionsBytes r cl = vlbytes 2 (List.Tot.fold_left (fun l s -> l @| extensionBytes r s) empty_bytes cl)))
  [SMTPat (extensionsBytes r cl)]

(* TODO: inversion lemmas
val parseEarlyDataIndication: pinverse_t earlyDataIndicationBytes
val parseExtension: pinverse_t extensionBytes
val parseExtensions: pinverse_t extensionsBytes
*)

(*************************************************
 extension parsing
 *************************************************)

(** local, failed-to-parse exc. *)
private type canFail (a:Type) =
| ExFail of alertDescription * string
| ExOK of list a

private val parseserverName: r:role -> b:bytes -> Tot (result (list TI.serverName))
let parseserverName r b  =
  let rec aux: b:bytes -> Tot (canFail TI.serverName) (decreases (length b)) = fun b ->
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
	    | 0z -> TI.SNI_DNS(cur)
	    | v  -> TI.SNI_UNKNOWN(int_of_bytes ty, cur)
	    end
	  in
	  let snidup: TI.serverName -> Tot bool = fun x ->
	    begin
	    match x,cur with
	    | TI.SNI_DNS _, TI.SNI_DNS _ -> true
	    | TI.SNI_UNKNOWN(a,_), TI.SNI_UNKNOWN(b,_) -> a = b
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

private let err_msg s = "Got inapproprite bytes for " ^ s

private val addOnce: extension -> list extension -> Tot (result (list extension))
let addOnce ext extList =
    if List.Tot.existsb (sameExt ext) extList then
        Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
    else
        let res = FStar.List.Tot.append extList [ext] in
        correct(res)

(* SI: API. Called by HandshakeMessages. *)
(** Parse extension. *)
val parseEarlyDataIndication: r:role -> b:bytes -> Tot (result earlyDataIndication) (decreases (length b))
val parseExtension: r:role -> b:bytes -> Tot (result extension) (decreases (length b))
val parseExtensions: r:role -> b:bytes -> Tot (result (list extension)) (decreases (length b))

val parseEcpfList: bytes -> Tot (result (list ECGroup.point_format))
let parseEcpfList b =
    let rec aux:b:bytes -> Tot (canFail (ECGroup.point_format)) (decreases (length b)) = fun b ->
        if equalBytes b empty_bytes then ExOK([])
        else
	  if (0 < length b) then 
	    let (u,v) = split b 1 in
              (match aux v with
              | ExFail(x,y) -> ExFail(x,y)
              | ExOK(l) ->
                  let cur = match cbyte u with
                  | 0z -> ECGroup.ECP_UNCOMPRESSED
                  | _ -> ECGroup.ECP_UNKNOWN(int_of_bytes u)
                  in ExOK(cur :: l))
	  else ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Malformed curve list")
    in match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK(l) -> 
      if (List.Tot.mem ECGroup.ECP_UNCOMPRESSED l) then
	correct l
      else
        Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Uncompressed point format not supported")

(* ToDo: what about duplicates? *)
val parseVersions: bytes -> Tot (result (list TLSConstants.protocolVersion))
let parseVersions b =
    let rec aux:b:bytes -> Tot (canFail (TLSConstants.protocolVersion)) (decreases (length b)) = fun b ->
        if equalBytes b empty_bytes then ExOK([])
        else
	  if (0 < length b) then 
	    let (u,v) = split b 2 in (* ToDo: check 2 bytes? *)
            (match aux v with
            | ExFail(x,y) -> ExFail(x,y)
            | ExOK(l) ->
		match TLSConstants.parseVersion u with 
		| Correct(v) -> ExOK(v :: l)
                | Error(e,msg) -> ExFail(e,msg))
	  else ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Malformed versions")
    in match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK(l) -> correct l
	
let rec parseExtension role b =
  if length b >= 4 then
    let (head, payload) = split b 2 in
    match vlparse 2 payload with
    | Correct (data) ->
	(match cbyte2 head with
(*
        | (0xffz, 0x02z) -> // TLS 1.3 draft version
          if length data = 2 then Correct (E_draftVersion data)
          else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "draft 1.3 version"))

*)	
	| (0x00z, 0x00z) -> // sni
	  (match parseserverName role data with
	  | Correct(snis) -> Correct (E_server_name snis)
	  | Error(z) -> Error(z))	  
	| (0x00z, 0x0Az) -> // supported groups
	  if length data >= 2 && length data < 65538 then
	  (match Parse.parseNamedGroups (data) with
	  | Correct(groups) -> Correct (E_supported_groups(groups))
	  | Error(z) -> Error(z))
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "SNI"))
	| (0x00z, 0x0Dz) -> // sigAlgs
	  if length data >= 2 && length data < 65538 then (
	  (match TLSConstants.parseSigHashAlgs (data) with
	  | Correct(algs) -> Correct (E_signature_algorithms algs)
	  | Error(z) -> Error(z))
	  ) else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "sigAlgs"))
	| (0x00z, 0x28z) -> // keyShare
	  (let is_client = (match role with | Client -> true | Server -> false) in
	  match CommonDH.parseKeyShare is_client data with
	  | Correct (ks) -> Correct (E_key_share(ks))
	  | Error(z) -> Error(z))
	| (0x00z, 0x29z) -> // head TBD, PSK
	  if length data >= 2 then
	  (match admit() (* 17-04-21 TODO PSK.parsePreSharedKey data *) with
	  | Correct(psk) -> Correct (E_pre_shared_key psk)
	  | Error(z) -> Error(z))
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "PSK"))

	| (0x00z, 0x2az) -> // EDI
	  (match parseEarlyDataIndication role data with
	  | Correct (edi) -> Correct (E_early_data(edi))
	  | Error(z) -> Error(z))
        | (0xffz, 0x2bz) -> // versions
	  if length data >= 2 && length data < 254 then (
	  (match parseVersions data with 
	  | Correct(v) -> Correct (E_supported_versions v)
	  | Error(z) -> Error(z))
	  ) else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "versions"))
        | (0xffz, 0x2cz) -> // cookie
	  if length data >= 1 && length data <= ((pow2 16) - 1) then 
	    Correct (E_cookie data)
	  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "cookie"))
        (* ToDo: | E_psk_key_exchange_modes _ *)
(*
        | (0xffz, 0x02z) -> // TLS 1.3 draft version
          if length data = 2 then Correct (E_draftVersion data)
          else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate draft 1.3 version")
	| (0xFFz, 0x01z) -> // renego (* OLD *)
	  (match parseRenegotiationInfo data with
	  | Correct(ri) -> Correct (E_renegotiation_info(ri))
	  | Error(z) -> Error(z)
*)	 
	| (0x00z, 0x0Bz) -> // ec point format
	  if length data < 256 && length data >= 1 then
	  (lemma_repr_bytes_values (length data);
	  match vlparse 1 data with
	  | Error(z) -> Error(z)
	  | Correct(data) ->
	  match parseEcpfList data with
	  | Correct(ecpfs) -> Correct (E_ec_point_format(ecpfs))
	  | Error(z) -> Error(z))
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ (err_msg "ec_point_fmt"))
(*
	| (0x00z, 0x17z) -> // extended ms
	  if length data = 0 then Correct (E_extended_ms)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for extended MS extension")
	| (0xBBz, 0x8Fz) -> // extended padding
	  if length data = 0 then Correct (E_extended_padding)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for extended padding extension")
 *)
	| _ -> // Unknown extension
	  Correct(E_unknown_extension(head,data)))
    | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extension length 1")
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Extension bytes are too short to store even the extension type")
and parseEarlyDataIndication role b =
  if length b >= 2 then
    match vlsplit 2 b with
    | Correct(config_id, data) ->
      if length config_id > 2 then (
      lemma_repr_bytes_values (length config_id);
      match parseConfigurationId (vlbytes 2 config_id) with
      | Correct(cid) -> (
	if length data >= 2 then
	  let (cs, data) = split data 2 in
	  match parseCipherSuite cs with
	  | Correct(cs) ->
	    if length data >= 2 then (
	    match vlsplit 2 data with
	    | Correct(exts, data) -> (
	      match parseExtensions role (vlbytes 2 exts) with
	      | Correct(exts) ->
		if length data >= 1 then (
		match vlparse 1 data with
		| Correct(ctx) ->
		    Correct (ClientEarlyDataIndication ({ ped_configuration_id = cid;
							  ped_cipher_suite = cs;
							  ped_extensions = exts;
							  ped_context = ctx; }))
		| Error(z) -> Error(z) )
		else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Not enough bytes to parse cipher suite in early data indication")
	      | Error(z) -> Error(z) )
	    | Error(z) -> Error(z) )
	    else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Not enough bytes to parse cipher suite in early data indication")
	  | Error(z) -> Error(z)
	else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Not enough bytes to parse cipher suite in early data indication") )
      | Error(z) -> Error(z) )
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for configuration id")
    | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse early data indication length")
  else Correct (ServerEarlyDataIndication)
and parseExtensions role b =
  let rec (aux:bytes -> list extension -> Tot (result (list extension))) = fun b exts ->
    if length b >= 4 then
      let ht, b = split b 2 in
      match vlsplit 2 b with
      | Correct(ext, bytes) -> (
	(* assume (Prims.precedes (Prims.LexCons b) (Prims.LexCons (ht @| vlbytes 2 ext))); *)
	match parseExtension role (ht @| vlbytes 2 ext) with
	| Correct(ext) ->
	  (match addOnce ext exts with // fails if the extension already is in the list
	  | Correct(exts) -> aux bytes exts
	  | Error(z) -> Error(z))
	| Error(z) -> Error(z))
      | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extension length 2")
    else Correct(exts) in
  if length b >= 2 then
  match vlparse 2 b with
  | Correct(b) -> aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extensions length")
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extensions length")

(* SI: API. Called by HandshakeMessages. *)
val parseOptExtensions: r:role -> data:bytes -> Tot (result (option (list extension)))
let parseOptExtensions r data =
  if length data = 0 then Correct(None)
  else
  (match parseExtensions r data with
  | Correct(exts) -> Correct(Some exts)
  | Error(z) -> Error(z))


(*************************************************
 Other extension functionality
 *************************************************)

(* JK: Need to get rid of such functions *)
(* API. Called by Negotiation *)
let rec list_valid_cs_is_list_cs (l:valid_cipher_suites): Tot (list cipherSuite) =
  match l with 
  | [] -> [] 
  | hd :: tl -> hd :: list_valid_cs_is_list_cs tl
  
private let rec list_valid_ng_is_list_ng (#p:(namedGroup -> Type)) (l:list (n:namedGroup{p n})): Tot (list namedGroup) = 
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
  list sigHashAlg -> list (x:namedGroup{SEC? x \/ FFDHE? x}) -> 
  option (TI.cVerifyData * TI.sVerifyData) -> 
  option CommonDH.keyShare -> 
  Tot (l:list extension{List.Tot.length l < 256})
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
       | TLS_1p2, TLS_1p3 -> E_supported_versions [TLS_1p2;TLS_1p3] :: res
       // REMARK: This case is not mandatory. E.g. www.google.com chokes on it
       // Commenting this out. This behaviour should be configurable
       // | TLS_1p2, TLS_1p2 -> E_supported_versions [TLS_1p2] :: res
       | _ -> res in
    let res = 
       match pv, ks with
       | TLS_1p3, Some ks -> E_key_share ks::res
       | _,_ -> res in
//    let res = if sres then E_extended_ms :: res else res in
    let res = (E_signature_algorithms sigAlgs) :: res in
    let res =
        if List.Tot.existsb (fun x -> isECDHECipherSuite x) (list_valid_cs_is_list_cs cs) then
          E_ec_point_format([ECGroup.ECP_UNCOMPRESSED]) :: 
	  (E_supported_groups (list_valid_ng_is_list_ng namedGroups)) :: res
        else
          let g = List.Tot.filter (function | FFDHE _ -> true | _ -> false) (list_valid_ng_is_list_ng namedGroups) in
          if g = [] then res
          else (E_supported_groups g) :: res in
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
  option (TI.cVerifyData * TI.sVerifyData) *
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
  | ClientRenegotiationInfo of (TI.cVerifyData)
  | ServerRenegotiationInfo of (TI.cVerifyData * TI.sVerifyData)

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
    | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse renegotiation info length")
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Renegotiation info bytes are too short")
*)

(* TODO: remove *)
private val replace_subtyping: (o:(option (TI.cVerifyData * TI.sVerifyData))) -> Tot (option (bytes*bytes)) 
let replace_subtyping (o:(option (TI.cVerifyData * TI.sVerifyData))) : Tot (option (bytes*bytes)) =
  match o with
  | None -> None
  | Some (a,b) -> Some (a,b)

// TODO
// ADL the negotiation of renegotiation indication is incorrect
// ADL needs to be consistent with clientToNegotiatedExtension
private val serverToNegotiatedExtension: TI.config -> list extension -> cipherSuite -> option (TI.cVerifyData * TI.sVerifyData) -> bool -> result TI.negotiatedExtensions -> extension -> Tot (result (TI.negotiatedExtensions))
let serverToNegotiatedExtension cfg cExtL cs ri (resuming:bool) res sExt : result (TI.negotiatedExtensions)=
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
      | E_ec_point_format(spf) ->
	  if resuming then
            correct l
          else
            correct ({l with TI.ne_supported_point_formats = Some spf})
(* not allowed for server
      | E_signature_algorithms sha ->
          if resuming then correct l
	  else correct ({l with ne_signature_algorithms = Some (sha)})
*)
      | E_key_share (CommonDH.ServerKeyShare sks) ->
        Correct ({l with TI.ne_keyShare = Some sks})
      | E_supported_groups named_group_list ->
        Correct ({l with TI.ne_supported_groups = Some named_group_list})
      | _ -> Error (AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Unexpected pattern in serverToNegotiatedExtension")
     else
       Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an extension not present in client hello")


(* SI: API. Called by Negotiation. *)
val negotiateClientExtensions: protocolVersion -> TI.config -> option (list extension) -> option (list extension) -> cipherSuite -> option (TI.cVerifyData * TI.sVerifyData) -> bool -> Tot (result (TI.negotiatedExtensions))
let negotiateClientExtensions pv cfg cExtL sExtL cs ri (resuming:bool) =
  match pv with
  | SSL_3p0 ->
     begin
     match sExtL with
     | None -> Correct TI.ne_default
     | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Received extensions in SSL 3.0 server hello")
     end
  | _ ->
     begin 
     match cExtL, sExtL with
     | _, None when pv <> TLS_1p3 -> Correct TI.ne_default
     | Some cExtL, Some sExtL -> (
        let nes = TI.ne_default in
        match List.Tot.fold_left (serverToNegotiatedExtension cfg cExtL cs ri resuming) (correct nes) sExtL with
        | Error(x,y) -> Error(x,y)
        | Correct l ->
          if resuming then correct l
          else
	  begin
	    match List.Tot.tryFind E_signature_algorithms? cExtL with
	    | Some (E_signature_algorithms shal) ->
	      correct({l with TI.ne_signature_algorithms = Some shal})
	    | None -> correct l
	    | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Unappropriate sig algs in negotiateClientExtensions")
	  end )
     | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "negoClientExts missing extensions in TLS hello message")
     end 

(* SI: API. Called by Negotiation. *)
val clientToNegotiatedExtension: TI.config -> cipherSuite -> option (TI.cVerifyData * TI.sVerifyData) -> bool -> TI.negotiatedExtensions -> extension -> Tot TI.negotiatedExtensions
let clientToNegotiatedExtension (cfg:TI.config) cs ri resuming neg cExt =
  match cExt with
  | E_supported_groups l ->
      if resuming then neg
      else
	  let isOK g = List.Tot.existsb (fun (x:Parse.namedGroup) -> x = g) (list_valid_ng_is_list_ng cfg.TI.namedGroups) in
	  {neg with TI.ne_supported_groups = Some (List.Tot.filter isOK l)}
  | E_ec_point_format l ->
      if resuming then neg
      else
	  let nl = List.Tot.filter (fun x -> x = ECGroup.ECP_UNCOMPRESSED) l in
	  {neg with TI.ne_supported_point_formats = Some nl}
  | E_server_name l ->
      {neg with TI.ne_server_names = Some l}
  | E_signature_algorithms sha ->
      if resuming then neg
      else {neg with TI.ne_signature_algorithms = Some (sha)}
  | _ -> neg // TODO: handle all remaining cases


private val clientToServerExtension: protocolVersion -> TI.config -> cipherSuite -> option (TI.cVerifyData * TI.sVerifyData) -> option CommonDH.keyShare -> bool -> extension -> option extension
let clientToServerExtension pv cfg cs ri ks resuming cext =
  match cext with
  | E_key_share _ ->
    Option.map E_key_share ks // ks should be in one of client's groups
  | E_server_name server_name_list ->
    begin
    // See https://tools.ietf.org/html/rfc6066
    match pv, List.Tot.tryFind TI.SNI_DNS? server_name_list with
    | TLS_1p3, _   -> None // TODO: SNI goes in EncryptedExtensions in TLS 1.3
    | _, Some name -> Some (E_server_name [])
    end
  | E_ec_point_format ec_point_format_list ->
    if resuming || pv = TLS_1p3 then
      None // No ec_point_format in TLS 1.3
    else
      Some (E_ec_point_format [ECGroup.ECP_UNCOMPRESSED])
  | E_supported_groups named_group_list ->
    Some (E_supported_groups cfg.TI.namedGroups) // Purely informative
  // TODO: handle all remaining cases
  | E_early_data b -> None
  | E_pre_shared_key b -> None
  | _ -> None


(* SI: API. Called by Handshake. *)
val negotiateServerExtensions: protocolVersion -> option (list extension) -> valid_cipher_suites -> TI.config -> cipherSuite -> option (TI.cVerifyData*TI.sVerifyData) -> option CommonDH.keyShare -> bool -> Tot (result (option (list extension)))
let negotiateServerExtensions pv cExtL csl cfg cs ri ks resuming =
   match cExtL with
   | Some cExtL ->
     let sexts = List.Tot.choose (clientToServerExtension pv cfg cs ri ks resuming) cExtL in
     Correct (Some sexts)
   | None ->
       (match pv with
(* SI: deadcode ?
       | SSL_3p0 ->
          let cre =
              if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (list_valid_cs_is_list_cs csl) then
                 Some [E_renegotiation_info (FirstConnection)] //, {ne_default with ne_secure_renegotiation = RI_Valid})
              else None //, ne_default in
          in Correct cre
*)	  
       | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "No extensions in ClientHello"))

private val default_sigHashAlg_fromSig: protocolVersion -> sigAlg -> ML (list sigHashAlg)
let default_sigHashAlg_fromSig pv sigAlg=
  let open CoreCrypto in
  let open Hashing.Spec in
  match sigAlg with
    | RSASIG ->
        (match pv with
        | TLS_1p2 -> [(RSASIG, Hash SHA1)]
        | TLS_1p0 | TLS_1p1 | SSL_3p0 -> [(RSASIG,MD5SHA1)])
        //| SSL_3p0 -> [(RSASIG,NULL)]
    | DSA ->
        [(DSA,Hash SHA1)]
        //match pv with
        //| TLS_1p0| TLS_1p1 | TLS_1p2 -> [(DSA, SHA1)]
        //| SSL_3p0 -> [(DSA,NULL)]
    | _ -> unexpected "[default_sigHashAlg_fromSig] invoked on an invalid signature algorithm"

(* SI: API. Called by HandshakeMessages. *)
val default_sigHashAlg: protocolVersion -> cipherSuite -> ML (l:list sigHashAlg{List.Tot.length l <= 1})
let default_sigHashAlg pv cs =
    default_sigHashAlg_fromSig pv (sigAlg_of_ciphersuite cs)



(*
let rec (compile_curve_list_aux:list ECGroup.ec_all_curve -> Tot bytes) = function
  | [] -> empty_bytes
  | ECGroup.EC_CORE c :: r ->
    let cid = ECGroup.curve_id c in
    cid @| compile_curve_list_aux r
  | ECGroup.EC_EXPLICIT_PRIME :: r -> abyte2 (255z, 01z) @| compile_curve_list_aux r
  | ECGroup.EC_EXPLICIT_BINARY :: r -> abyte2 (255z, 02z) @| compile_curve_list_aux r
  | ECGroup.EC_UNKNOWN(x) :: r -> bytes_of_int 2 x @| compile_curve_list_aux r

private val compile_curve_list: l:list ECGroup.ec_all_curve{length (compile_curve_list_aux l) < 65536} -> Tot bytes
let compile_curve_list l =
  let al = compile_curve_list_aux l in
  lemma_repr_bytes_values (length al);
  let bl: bytes = vlbytes 2 al in
  bl

val parse_curve_list: bytes -> Tot (result (list ECGroup.ec_all_curve))
let parse_curve_list b =
    let rec aux:b:bytes -> Tot (canFail ECGroup.ec_all_curve) (decreases (length b)) = fun b ->
        if equalBytes b empty_bytes then ExOK([])
        else if (length b) % 2 = 1 then ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Bad encoding of curve list")
        else
	  if length b >= 2 then
	    let (u,v) = split b 2 in
            (match aux v with
            | ExFail(x,y) -> ExFail(x,y)
            | ExOK(l) ->
                let cur =
                    (match cbyte2 u with
                    | (0z, 23z) -> ECGroup.EC_CORE CoreCrypto.ECC_P256
                    | (0z, 24z) -> ECGroup.EC_CORE CoreCrypto.ECC_P384
                    | (0z, 25z) -> ECGroup.EC_CORE CoreCrypto.ECC_P521
                    | (255z, 1z) -> ECGroup.EC_EXPLICIT_PRIME
                    | (255z, 2z) -> ECGroup.EC_EXPLICIT_BINARY
                    | _ -> ECGroup.EC_UNKNOWN(int_of_bytes u))
                in
                    if List.Tot.mem cur l then ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Duplicate curve")
                    else ExOK(cur :: l))
	  else ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Malformed curve list")
    in (match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK([]) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Empty supported curve list")
    | ExOK(l) -> correct (l))

(* SI: deadcode

let op_At = FStar.List.Tot.append

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
    | h::t -> (cert_type_to_SigHashAlg h pv) @ (cert_type_list_to_SigHashAlg t pv)

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
*)
// JK : cannot add total effect here because of the exception thrown
(* JK: changed from Tot (list sigHashAlg) to Tot (result (list (sigAlg*hashAlg))) to match the
   spec to the code *)
(* val default_sigHashAlg_fromSig: protocolVersion -> sigAlg -> Tot (result (list (sigAlg*hashAlg))) *)
(* let default_sigHashAlg_fromSig pv sigAlg= *)
(*     match sigAlg with *)
(*     | RSASIG -> ( *)
(*         match pv with *)
(*         | TLS_1p2 -> Correct [(RSASIG, Hash SHA1)] *)
(*         | TLS_1p0 | TLS_1p1 | SSL_3p0 -> Correct [(RSASIG,MD5SHA1)] *)
(* 	| _ -> Error (AD_internal_error, perror __SOURCE_FILE__ __LINE__ "[default_sigHashAlg_fromSig] invoked on an invalid") *)
(* 	) *)
(*         //| SSL_3p0 -> [(RSASIG,NULL)] *)
(*     | DSA -> *)
(*         Correct [(DSA,Hash SHA1)] *)
(*         //match pv with *)
(*         //| TLS_1p0| TLS_1p1 | TLS_1p2 -> [(DSA, SHA1)] *)
(*         //| SSL_3p0 -> [(DSA,NULL)] *)
(*     | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "[default_sigHashAlg_fromSig] invoked on an invalid signature algorithm") *)

(* val default_sigHashAlg: protocolVersion -> cipherSuite -> (result (l:list sigHashAlg{List.Tot.length l <= 1})) *)
(* let default_sigHashAlg pv cs = *)
(*   admit(); *)
(*   match default_sigHashAlg_fromSig pv (sigAlg_of_ciphersuite cs) with *)
(*   | Correct (l) -> Correct(l) *)
(*   | Error(z) -> Error(z) *)

(* val sigHashAlg_contains: list sigHashAlg -> sigHashAlg -> Tot bool *)
(* let sigHashAlg_contains (algList:list sigHashAlg) (alg:sigHashAlg) = *)
(*     List.Tot.mem alg algList *)

(* val sigHashAlg_bySigList: list sigHashAlg -> list sigAlg -> Tot (list sigHashAlg) *)
(* let sigHashAlg_bySigList (algList:list sigHashAlg) (sigAlgList:list sigAlg) = *)
(*     List.Tot.choose (fun alg -> let (sigA,_) = alg in if (List.Tot.existsb (fun a -> a = sigA) sigAlgList) then Some(alg) else None) algList *)

(* val cert_type_to_SigHashAlg: certType -> protocolVersion -> list sigHashAlg *)
(* let cert_type_to_SigHashAlg ct pv = *)
(*     match ct with *)
(*     | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> default_sigHashAlg_fromSig pv DSA *)
(*     | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> default_sigHashAlg_fromSig pv RSASIG *)

(* val cert_type_list_to_SigHashAlg: list certType -> protocolVersion -> list sigHashAlg *)
(* let rec cert_type_list_to_SigHashAlg ctl pv = *)
(*     // FIXME: Generates a list with duplicates! *)
(*     match ctl with *)
(*     | [] -> [] *)
(*     | h::t -> (cert_type_to_SigHashAlg h pv) @ (cert_type_list_to_SigHashAlg t pv) *)

(* val cert_type_to_SigAlg: certType -> Tot sigAlg *)
(* let cert_type_to_SigAlg ct = *)
(*     match ct with *)
(*     | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> DSA *)
(*     | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> RSASIG *)

(* val cert_type_list_to_SigAlg: list certType -> list sigAlg *)
(* let rec cert_type_list_to_SigAlg ctl = *)
(*     // FIXME: Generates a list with duplicates! *)
(*     match ctl with *)
(*     | [] -> [] *)
(*     | h::t -> (cert_type_to_SigAlg h) :: (cert_type_list_to_SigAlg t) *)
