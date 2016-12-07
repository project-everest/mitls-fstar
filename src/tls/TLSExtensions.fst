(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module TLSExtensions

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSFormats
open TLSInfo
open CoreCrypto

let op_At = FStar.List.Tot.append

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

(* TODO: inversion lemmas *)
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
// JK : can I merge client extensions and server extensions ?
and extension = 
  // TLS 1.3 extension types
  | E_earlyData of earlyDataIndication 
  | E_preSharedKey of preSharedKey 
  | E_keyShare of keyShare 
  | E_draftVersion of bytes
  // Common extension types
  | E_signatureAlgorithms of (list sigScheme) 
  // Previous extension types
  | E_renegotiation_info of renegotiationInfo
  | E_server_name of list serverName
  | E_extended_ms 
  | E_extended_padding 
  | E_ec_point_format of list ECGroup.point_format
  | E_supported_groups of list namedGroup
  | E_unknown_extension of (lbytes 2 * bytes) // Still store unknown extension to get parsing injectivity

let sameExt a b =
  match a, b with
  | E_draftVersion _, E_draftVersion _ -> true
  | E_earlyData _, E_earlyData _ -> true
  | E_preSharedKey _, E_preSharedKey _ -> true
  | E_keyShare _, E_keyShare _ -> true
  | E_signatureAlgorithms _, E_signatureAlgorithms _ -> true
  | E_renegotiation_info _, E_renegotiation_info _ -> true 
  | E_server_name _, E_server_name _ -> true
  | E_extended_ms, E_extended_ms -> true 
  | E_extended_padding, E_extended_padding -> true 
  | E_ec_point_format _, E_ec_point_format _ -> true
  | E_supported_groups _, E_supported_groups _ -> true
  // For unknown extensions return true if the header is the same to mimic the general behaviour
  | E_unknown_extension(h1,_), E_unknown_extension(h2,_) -> equalBytes h1 h2
  | _ -> false

val extensionHeaderBytes: extension -> Tot bytes
let extensionHeaderBytes ext =
  match ext with
  | E_draftVersion _        -> abyte2 (0xFFz, 0x02z)
  | E_keyShare _            -> abyte2 (0x00z, 0x28z) // KB: used Ekr's values
  | E_preSharedKey _        -> abyte2 (0x00z, 0x29z) // KB: used Ekr's values
  | E_earlyData _           -> abyte2 (0x00z, 0x2az) // KB: used Ekr's values
  | E_signatureAlgorithms _ -> abyte2 (0x00z, 0x0Dz)
  | E_renegotiation_info(_) -> abyte2 (0xFFz, 0x01z)
  | E_server_name (_)       -> abyte2 (0x00z, 0x00z)
  | E_extended_ms           -> abyte2 (0x00z, 0x17z)
  | E_extended_padding      -> abyte2 (0xBBz, 0x8Fz)
  | E_ec_point_format _     -> abyte2 (0x00z, 0x0Bz)
  | E_supported_groups _    -> abyte2 (0x00z, 0x0Az)
  | E_unknown_extension(h,b)-> h

type canFail (a:Type) =
| ExFail of alertDescription * string
| ExOK of list a

val compile_sni_list: list serverName -> Tot bytes
let compile_sni_list l =
    let rec (aux:list serverName -> Tot bytes) = function
    | [] -> empty_bytes
    | SNI_DNS(x) :: r -> (abyte 0z) @| bytes_of_int 2 (length x) @| x @| aux r
    | SNI_UNKNOWN(t, x) :: r -> (bytes_of_int 1 t) @| bytes_of_int 2 (length x) @| x @| aux r
    in 
    (aux l)

val parse_sni_list: r:role -> b:bytes -> Tot (result (list serverName))
let parse_sni_list r b  =
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
	Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse SNI list: should be empty in ServerHello, has size " ^ string_of_int (length b))
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

let rec (compile_curve_list_aux:list ECGroup.ec_all_curve -> Tot bytes) = function
  | [] -> empty_bytes
  | ECGroup.EC_CORE c :: r ->
    let cid = curve_id (ECGroup.params_of_group c) in
    cid @| compile_curve_list_aux r
  | ECGroup.EC_EXPLICIT_PRIME :: r -> abyte2 (255z, 01z) @| compile_curve_list_aux r
  | ECGroup.EC_EXPLICIT_BINARY :: r -> abyte2 (255z, 02z) @| compile_curve_list_aux r
  | ECGroup.EC_UNKNOWN(x) :: r -> bytes_of_int 2 x @| compile_curve_list_aux r

val compile_curve_list: l:list ECGroup.ec_all_curve{length (compile_curve_list_aux l) < 65536} -> Tot bytes
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

val parse_ecpf_list: bytes -> Tot (result (list ECGroup.point_format))
let parse_ecpf_list b =
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

let rec (compile_ecpf_list_aux:list ECGroup.point_format -> Tot bytes) =
  function
  | [] -> empty_bytes
  | ECGroup.ECP_UNCOMPRESSED :: r -> (abyte 0z) @| compile_ecpf_list_aux r
  | ECGroup.ECP_UNKNOWN(t) :: r -> (bytes_of_int 1 t) @| compile_ecpf_list_aux r

val compile_ecpf_list: l:list ECGroup.point_format{length (compile_ecpf_list_aux l) < 256} -> Tot bytes
let compile_ecpf_list l =
  let al = compile_ecpf_list_aux l in
  lemma_repr_bytes_values (length al);
  let bl:bytes = vlbytes 1 al in
  bl

val addOnce: extension -> list extension -> Tot (result (list extension))
let addOnce ext extList =
    if List.Tot.existsb (sameExt ext) extList then
        Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
    else
        let res = FStar.List.Tot.append extList [ext] in
        correct(res)

let rec extension_depth (ext:extension): Tot nat =
  match ext with
  | E_earlyData edt           -> (
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

(* TODO *)
#set-options "--lax"

val earlyDataIndicationBytes: edi:earlyDataIndication -> Tot bytes 
  (decreases (fun edi -> match edi with | ClientEarlyDataIndication edi -> extensions_depth edi.ped_extensions | _ -> 0))
val extensionPayloadBytes: role -> ext:extension -> Tot bytes
  (decreases (extension_depth ext))
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
  | E_draftVersion b          -> b
  | E_earlyData edt           -> earlyDataIndicationBytes edt
  | E_preSharedKey psk        -> preSharedKeyBytes psk
  | E_keyShare ks             -> keyShareBytes ks
  | E_signatureAlgorithms sha -> sigSchemesBytes sha
  | E_renegotiation_info(ri)  -> renegotiationInfoBytes ri
  | E_server_name(l)          -> if role = Client then vlbytes 2 (compile_sni_list l) else compile_sni_list l
  | E_extended_ms             -> empty_bytes
  | E_extended_padding        -> empty_bytes
  | E_supported_groups(l)     -> namedGroupsBytes l
  | E_ec_point_format(l)      -> compile_ecpf_list l
  | E_unknown_extension(h,b)  -> b
and extensionBytes role ext =
    let head = extensionHeaderBytes ext in
    let payload = extensionPayloadBytes role ext in
    let payload = vlbytes 2 payload in
    head @| payload
and extensionsBytes role exts = 
  vlbytes 2 (List.Tot.fold_left (fun l s -> l @| extensionBytes role s) empty_bytes exts)

#reset-options 

(* JK: For some reason without that I do not manage to get the definition of extensionsBytes *)
assume val extensionsBytes_def: r:role -> cl:list extension{repr_bytes (length (List.Tot.fold_left (fun l s -> l @| extensionBytes r s) empty_bytes cl)) <= 2} -> 
  Lemma (requires (True))
	(ensures (extensionsBytes r cl = vlbytes 2 (List.Tot.fold_left (fun l s -> l @| extensionBytes r s) empty_bytes cl)))
  [SMTPat (extensionsBytes r cl)]

(* TODO: inversion lemmas 
val parseEarlyDataIndication: pinverse_t earlyDataIndicationBytes
val parseExtension: pinverse_t extensionBytes
val parseExtensions: pinverse_t extensionsBytes
*)

(* TODO *)
#set-options "--lax"

val parseEarlyDataIndication: r:role -> b:bytes -> Tot (result earlyDataIndication) (decreases (length b))
val parseExtension: r:role -> b:bytes -> Tot (result extension) (decreases (length b))
val parseExtensions: r:role -> b:bytes -> Tot (result (list extension)) (decreases (length b))
let rec parseExtension role b =
  if length b >= 4 then
    let (head, payload) = split b 2 in
    match vlparse 2 payload with
    | Correct (data) ->
	(match cbyte2 head with
        | (0xffz, 0x02z) -> // TLS 1.3 draft version
          if length data = 2 then Correct (E_draftVersion data)
          else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate draft 1.3 version")
	| (0x00z, 0x0Dz) -> // sigalgs
	  if length data >= 2 && length data < 65538 then (
	  (match parseSigSchemes (data) with
	  | Correct(algs) -> Correct (E_signatureAlgorithms algs)
	  | Error(z) -> Error(z))
	  ) else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for signature & hash algorithms")
	| (0x00z, 0x00z) -> // sni
	  (match parse_sni_list role data with
	  | Correct(snis) -> Correct (E_server_name snis)
	  | Error(z) -> Error(z))
	| (0xFFz, 0x01z) -> // renego
	  (match parseRenegotiationInfo data with
	  | Correct(ri) -> Correct (E_renegotiation_info(ri))
	  | Error(z) -> Error(z))
	| (0x00z, 0x0Az) -> // supported groups
	  if length data >= 2 && length data < 65538 then
	  (match parseNamedGroups (data) with
	  | Correct(groups) -> Correct (E_supported_groups(groups))
	  | Error(z) -> Error(z))
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes named groups")
	| (0x00z, 0x0Bz) -> // ec point format
	  if length data < 256 && length data >= 1 then
	  (lemma_repr_bytes_values (length data);
	  match vlparse 1 data with
	  | Error(z) -> Error(z)
	  | Correct(data) ->
	  match parse_ecpf_list data with
	  | Correct(ecpfs) -> Correct (E_ec_point_format(ecpfs))
	  | Error(z) -> Error(z))
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for ecpf list")
	| (0x00z, 0x17z) -> // extended ms
	  if length data = 0 then Correct (E_extended_ms)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for extended MS extension")
	| (0xBBz, 0x8Fz) -> // extended padding
	  if length data = 0 then Correct (E_extended_padding)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for extended padding extension")
	| (0x00z, 0x2az) -> // head TBD, early data
	  (match parseEarlyDataIndication role data with
	  | Correct (edi) -> Correct (E_earlyData(edi))
	  | Error(z) -> Error(z))
	| (0x00z, 0x29z) -> // head TBD, pre shared key
	  if length data >= 2 then
	  (match parsePreSharedKey data with
	  | Correct(psk) -> Correct (E_preSharedKey(psk))
	  | Error(z) -> Error(z))
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for pre shared key")
	| (0x00z, 0x28z) -> // head TBD, key share
	  (let is_client = (match role with | Client -> true | Server -> false) in
	  match parseKeyShare is_client data with	    
	  | Correct (ks) -> Correct (E_keyShare(ks))
	  | Error(z) -> Error(z))
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

#reset-options

val parseOptExtensions: r:role -> data:bytes -> Tot (result (option (list extension)))
let parseOptExtensions r data =
  if length data = 0 then Correct(None)
  else 
  (match parseExtensions r data with
  | Correct(exts) -> Correct(Some exts)
  | Error(z) -> Error(z))

(* JK: Need to get rid of such functions *)
let rec list_valid_cs_is_list_cs (l:valid_cipher_suites): Tot (list cipherSuite) = 
  match l with | [] -> [] | hd :: tl -> hd :: list_valid_cs_is_list_cs tl
let rec list_valid_ng_is_list_ng (#p:(namedGroup -> Type)) (l:list (n:namedGroup{p n})): Tot (list namedGroup) = match l with | [] -> [] | hd :: tl -> hd :: list_valid_ng_is_list_ng tl

// The extensions sent by the client
// (for the server we negotiate the client extensions)
val prepareExtensions: protocolVersion -> (k:valid_cipher_suites{List.Tot.length k < 256}) -> bool -> bool -> list sigScheme -> list (x:namedGroup{SEC? x \/ FFDHE? x}) -> option (cVerifyData * sVerifyData) -> (option keyShare) -> Tot (l:list extension{List.Tot.length l < 256})
let prepareExtensions pv cs sres sren sigAlgs namedGroups ri ks =
    (* Always send supported extensions. The configuration options will influence how strict the tests will be *)
    let cri =
       match ri with
       | None -> FirstConnection
       | Some (cvd, svd) -> ClientRenegotiationInfo cvd in
    let res = [E_renegotiation_info(cri)] in
    let res = [E_draftVersion (abyte2 (0z, 13z))] in
    let res = 
       match pv, ks with
       | TLS_1p3,Some ks -> (E_keyShare ks)::res
       | _,_ -> res in
    let res = if sres then E_extended_ms :: res else res in
//No extended padding for now
//    let res = E_extended_padding :: res in
    let res = (E_signatureAlgorithms sigAlgs) :: res in
    let res =
        if List.Tot.existsb (fun x -> isECDHECipherSuite x) (list_valid_cs_is_list_cs cs) then
          E_ec_point_format([ECGroup.ECP_UNCOMPRESSED]) :: (E_supported_groups (list_valid_ng_is_list_ng namedGroups)) :: res
        else
          let g = List.Tot.filter (function | FFDHE _ -> true | _ -> false) (list_valid_ng_is_list_ng namedGroups) in
          if g = [] then res
          else (E_supported_groups g) :: res in
    assume (List.Tot.length res < 256);  // JK: Specs in type config in TLSInfo unsufficient
    res

(* TODO: remove *)
let replace_subtyping (o:(option (cVerifyData * sVerifyData))) : Tot (option (bytes*bytes)) = 
  match o with
  | None -> None
  | Some (a,b) -> Some (a,b)
  
// TODO
// ADL the negotiation of renegotiation indication is incorrect
// ADL needs to be consistent with clientToNegotiatedExtension
val serverToNegotiatedExtension: config -> list extension -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> result negotiatedExtensions -> extension -> Tot (result (negotiatedExtensions))
let serverToNegotiatedExtension cfg cExtL cs ri (resuming:bool) res sExt : result (negotiatedExtensions)=
    match res with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
      if List.Tot.existsb (sameExt sExt) cExtL then 
            match sExt with
            | E_renegotiation_info (sri) ->
              (match sri, replace_subtyping ri with
              | FirstConnection, None -> correct ({l with ne_secure_renegotiation = RI_Valid})
              | ServerRenegotiationInfo(cvds,svds), Some(cvdc, svdc) ->
                 if equalBytes cvdc cvds && equalBytes svdc svds then
                    correct ({l with ne_secure_renegotiation = RI_Valid})
                 else
                    Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Mismatch in contents of renegotiation indication")
              | _ -> Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Detected a renegotiation attack"))
            | E_server_name _ ->
                if List.Tot.existsb (fun x->match x with |E_server_name _ -> true | _ -> false) cExtL then correct(l)
                else Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an SNI acknowledgement without an SNI provided")
            | E_ec_point_format(spf) ->
                if resuming then
                    correct l
                else
                    correct ({l with ne_supported_point_formats = Some spf})
(* not allowed for server
            | E_signatureAlgorithms sha ->
                if resuming then correct l
                else correct ({l with ne_signature_algorithms = Some (sha)})
*)
            | E_extended_ms ->
                if resuming then
                    correct(l)
                else
                    correct({l with ne_extended_ms = true})
            | E_extended_padding ->
                if resuming then
                    Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided extended padding in a resuming handshake")
                else
                    if isOnlyMACCipherSuite cs then
                        Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided extended padding for a MAC only ciphersuite")
                    else
                        correct({l with ne_extended_padding = true})
	    | E_keyShare (ServerKeyShare sks) -> correct({l with ne_keyShare = Some sks})
	    | _ -> Error (AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Unexpected pattern in serverToNegotiatedExtension")
        else 
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an extension not present in client hello") 

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
     | Some cExtL, Some sExtL ->
	begin
        let nes = ne_default in
        match List.Tot.fold_left (serverToNegotiatedExtension cfg cExtL cs ri resuming) (correct nes) sExtL with
        | Error(x,y) -> Error(x,y)
        | Correct l ->
          if resuming then correct l
          else
	  begin
	    match List.Tot.tryFind E_signatureAlgorithms? cExtL with
	    | Some (E_signatureAlgorithms shal) ->
	      correct({l with ne_signature_algorithms = Some shal})
	    | None -> correct l
	    | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Unappropriate sig algs in negotiateClientExtensions")
	  end
	end
     | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Missing extensions in TLS hello message")
     end

val clientToServerExtension: protocolVersion -> config -> cipherSuite -> option (cVerifyData * sVerifyData) -> option keyShare -> bool -> extension -> Tot (option extension)
let clientToServerExtension pv (cfg:config) (cs:cipherSuite) ri ks (resuming:bool) (cExt:extension) : (option (extension)) =
    match cExt with
    | E_earlyData b -> None    // JK : TODO
    | E_preSharedKey b -> None // JK : TODO
    | E_keyShare b ->
        (match ks with
 	| Some k -> Some (E_keyShare k)     
	| None -> None)
    | E_renegotiation_info (_) ->
        let ric =
           match ri with
           | Some t -> ServerRenegotiationInfo t
           | None -> FirstConnection in
        (match pv with
        | TLS_1p3 -> None
        | _ -> Some (E_renegotiation_info ric))
    | E_server_name l -> 
        (match List.Tot.tryFind (fun x->match x with | SNI_DNS _ -> true | _ -> false) l with
        | Some _ -> 
	  if pv <> TLS_1p3
	  then Some(E_server_name []) // TODO EncryptedExtensions
	  else None
        | _ -> None)
    | E_ec_point_format(l) ->
        if resuming || pv = TLS_1p3 then None
        else Some(E_ec_point_format [ECGroup.ECP_UNCOMPRESSED])
    | E_supported_groups(l) -> None
    | E_extended_ms -> 
        if pv <> TLS_1p3 && cfg.safe_resumption then Some(E_extended_ms)
        else None
    | E_extended_padding ->
        if resuming then
            None
        else
            if isOnlyMACCipherSuite cs then
                None
            else
                Some(E_extended_padding)
    | _ -> None    

val clientToNegotiatedExtension: config -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> negotiatedExtensions -> extension -> Tot negotiatedExtensions
let clientToNegotiatedExtension (cfg:config) cs ri resuming neg cExt =
  match cExt with
    | E_renegotiation_info (cri) ->
        let rs = 
           match cri, ri with
           | FirstConnection, None -> RI_Valid
           | ClientRenegotiationInfo(cvdc), Some (cvds, svds) ->
               if equalBytes cvdc cvds then RI_Valid else RI_Invalid
           | _ -> RI_Invalid in 
        {neg with ne_secure_renegotiation = rs}
    | E_supported_groups l ->
        if resuming then neg
        else
            let isOK g = List.Tot.existsb (fun (x:namedGroup) -> x = g) (list_valid_ng_is_list_ng cfg.namedGroups) in
            {neg with ne_supported_groups = Some (List.Tot.filter isOK l)}
    | E_ec_point_format l ->
        if resuming then neg
        else
            let nl = List.Tot.filter (fun x -> x = ECGroup.ECP_UNCOMPRESSED) l in
            {neg with ne_supported_point_formats = Some nl}
    | E_server_name l ->
        {neg with ne_server_names = Some l}
    | E_extended_ms ->
        if resuming then
            neg
        else
            // If EMS is disabled in config, don't negotiate it
            {neg with ne_extended_ms = cfg.safe_resumption}
    | E_extended_padding ->
        if resuming then
            neg
        else
            if isOnlyMACCipherSuite cs then
                neg
            else
                {neg with ne_extended_padding = true}
    | E_signatureAlgorithms sha ->
        if resuming then neg
        else {neg with ne_signature_algorithms = Some (sha)}
    | _ -> neg // JK : handle remaining cases

val negotiateServerExtensions: protocolVersion -> option (list extension) -> valid_cipher_suites -> config -> cipherSuite -> option (cVerifyData*sVerifyData) -> option keyShare -> bool -> Tot (result (option (list extension)))
let negotiateServerExtensions pv cExtL csl cfg cs ri ks resuming =
   match cExtL with
   | Some cExtL ->
      let server = List.Tot.choose (clientToServerExtension pv cfg cs ri ks resuming) cExtL in
      Correct (Some server)
//      let negi = ne_default in
//      let nego = List.Tot.fold_left (clientToNegotiatedExtension cfg cs ri resuming) negi cExtL in
//      Correct (Some server, nego)
   | None -> 
       (match pv with
       | SSL_3p0 ->
          let cre =
              if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (list_valid_cs_is_list_cs csl) then
                 Some [E_renegotiation_info (FirstConnection)] //, {ne_default with ne_secure_renegotiation = RI_Valid})
              else None //, ne_default in
          in Correct cre
       | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Missing extensions in TLS client hello"))

val isClientRenegotiationInfo: extension -> Tot (option cVerifyData)
let isClientRenegotiationInfo e =
    match e with
    | E_renegotiation_info(ClientRenegotiationInfo(cvd)) -> Some(cvd)
    | _ -> None

val checkClientRenegotiationInfoExtension: config -> list extension -> cVerifyData -> Tot bool
let checkClientRenegotiationInfoExtension config (cExtL: list extension) cVerifyData =
    match List.Tot.tryPick isClientRenegotiationInfo cExtL with
    | None -> not (config.safe_renegotiation)
    | Some(payload) -> equalBytes payload cVerifyData

val isServerRenegotiationInfo: extension -> Tot (option (cVerifyData * sVerifyData))
let isServerRenegotiationInfo e =
    match e with
    | E_renegotiation_info (ServerRenegotiationInfo(cvd,svd)) -> Some((cvd,svd))
    | _ -> None

val checkServerRenegotiationInfoExtension: config -> list extension -> cVerifyData -> sVerifyData -> Tot bool
let checkServerRenegotiationInfoExtension config (sExtL: list extension) cVerifyData sVerifyData =
    match List.Tot.tryPick isServerRenegotiationInfo sExtL with
    | None -> not (config.safe_renegotiation)
    | Some(x) ->
        let (cvd,svd) = x in
        equalBytes (cvd @| svd) (cVerifyData @| sVerifyData)

val hasExtendedMS: negotiatedExtensions -> Tot bool
let hasExtendedMS extL = extL.ne_extended_ms = true

// JK : cannot add total effect here because of the exception thrown
(* TODO *)
#set-options "--lax"

val default_sigHashAlg_fromSig: protocolVersion -> sigAlg -> (list sigHashAlg)
let default_sigHashAlg_fromSig pv sigAlg=
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

val default_sigHashAlg: protocolVersion -> cipherSuite -> l:list sigHashAlg{List.Tot.length l <= 1}
let default_sigHashAlg pv cs =
    default_sigHashAlg_fromSig pv (sigAlg_of_ciphersuite cs)

val sigHashAlg_contains: list sigHashAlg -> sigHashAlg -> Tot bool
let sigHashAlg_contains (algList:list sigHashAlg) (alg:sigHashAlg) =
    List.Tot.mem alg algList

val sigHashAlg_bySigList: list sigHashAlg -> list sigAlg -> Tot (list sigHashAlg)
let sigHashAlg_bySigList (algList:list sigHashAlg) (sigAlgList:list sigAlg) =
    List.Tot.choose (fun alg -> let (sigA,_) = alg in if (List.Tot.existsb (fun a -> a = sigA) sigAlgList) then Some(alg) else None) algList

val cert_type_to_SigHashAlg: certType -> protocolVersion -> list sigHashAlg
let cert_type_to_SigHashAlg ct pv =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> default_sigHashAlg_fromSig pv DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> default_sigHashAlg_fromSig pv RSASIG

val cert_type_list_to_SigHashAlg: list certType -> protocolVersion -> list sigHashAlg
let rec cert_type_list_to_SigHashAlg ctl pv =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> (cert_type_to_SigHashAlg h pv) @ (cert_type_list_to_SigHashAlg t pv)

val cert_type_to_SigAlg: certType -> Tot sigAlg
let cert_type_to_SigAlg ct =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> RSASIG

val cert_type_list_to_SigAlg: list certType -> list sigAlg
let rec cert_type_list_to_SigAlg ctl =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> (cert_type_to_SigAlg h) :: (cert_type_list_to_SigAlg t)
    
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
