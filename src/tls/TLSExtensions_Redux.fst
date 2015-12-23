(*--build-config
  options:--codegen-lib CoreCrypto --codegen-lib Platform --codegen-lib Classical --codegen-lib SeqProperties --codegen-lib HyperHeap  --admit_fsi FStar.Char --admit_fsi FStar.HyperHeap --admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.Seq --admit_fsi SessionDB --admit_fsi UntrustedCert --admit_fsi DHDB --admit_fsi CoreCrypto --admit_fsi Cert --admit_fsi Handshake --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 5 --lax;
  other-files:ext.fst classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi listTot.fst hyperHeap.fsi stHyperHeap.fst allHyperHeap.fst char.fsi string.fst list.fst listproperties.fst seq.fsi seqproperties.fst /home/jkz/dev/FStar/contrib/Platform/fst/Bytes.fst /home/jkz/dev/FStar/contrib/Platform/fst/Date.fst /home/jkz/dev/FStar/contrib/Platform/fst/Error.fst /home/jkz/dev/FStar/contrib/Platform/fst/Tcp.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/CoreCrypto.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/DHDB.fst TLSError.fst TLSConstants-redux.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst;
  --*)

(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLSExtensions

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo
open CoreCrypto

type renegotiationInfo =
  | FirstConnection
  | ClientRenegotiationInfo of (cVerifyData)
  | ServerRenegotiationInfo of (cVerifyData * sVerifyData)

val renegotiationInfoBytes: renegotiationInfo -> Tot bytes
let renegotiationInfoBytes ri = 
  match ri with
  | FirstConnection -> vlbytes 1 empty_bytes
  | ClientRenegotiationInfo(cvd) -> vlbytes 1 cvd
  | ServerRenegotiationInfo(cvd, svd) -> vlbytes 1 (cvd @| svd)

val parseRenegotiationInfo: pinverse Seq.Eq renegotiationInfoBytes
let parseRenegotiationInfo b =
  if length b >= 1 then
    match vlparse 1 b with
    | Correct(_) ->
	let (len, payload) = split b 1 in
	(match cbyte len with
	| 0uy -> Correct (FirstConnection)
	| 12uy | 36uy -> Correct (ClientRenegotiationInfo payload) // TLS 1.2 / SSLv3 client verify data sizes
	| 24uy -> // TLS 1.2 case
	    let cvd, svd = split payload 12 in
	    Correct (ServerRenegotiationInfo (cvd, svd))
	| 72uy -> // SSLv3
	    let cvd, svd = split payload 36 in
	    Correct (ServerRenegotiationInfo (cvd, svd))
	| _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Inappropriate length for renegotiation info data (expected 12/24 for client/server in TLS1.x, 36/72 for SSL3"))
    | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse renegotiation info length")
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Renegotiation info bytes are too short")

type preEarlyDataIndication =
  { ped_configuration_id: configurationId;
    ped_cipher_suite:cipherSuite;
    ped_extensions:list extension;
    ped_context:bytes;
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
  // Common extension types
  | E_signatureAlgorithms of (list sigHashAlg) 
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
  | E_earlyData _           -> abyte2 (0x00uy, 0x02uy) // JK : TODO, TBD
  | E_preSharedKey _        -> abyte2 (0x00uy, 0x03uy) // JK : TODO, TBD
  | E_keyShare _            -> abyte2 (0x00uy, 0x04uy) // JK : TODO, TBD
  | E_signatureAlgorithms _ -> abyte2 (0x00uy, 0x0Duy)
  | E_renegotiation_info(_) -> abyte2 (0xFFuy, 0x01uy)
  | E_server_name (_)       -> abyte2 (0x00uy, 0x00uy)
  | E_extended_ms           -> abyte2 (0x00uy, 0x17uy)
  | E_extended_padding      -> abyte2 (0xBBuy, 0x8Fuy)
  | E_ec_point_format _     -> abyte2 (0x00uy, 0x0Buy)
  | E_supported_groups _    -> abyte2 (0x00uy, 0x0Auy)
  | E_unknown_extension(h,b)-> h

type CanFail (a:Type) =
| ExFail of alertDescription * string
| ExOK of list a

val compile_sni_list: list serverName -> Tot bytes
let compile_sni_list l =
    let rec (aux:list serverName -> Tot bytes) = function
    | [] -> empty_bytes
    | SNI_DNS(x) :: r -> (abyte 0uy) @| bytes_of_int 2 (length x) @| x @| aux r
    | SNI_UNKNOWN(t, x) :: r -> (bytes_of_int 1 t) @| bytes_of_int 2 (length x) @| x @| aux r
    in aux l

val parse_sni_list: b:bytes -> Tot (Result (list serverName))
let parse_sni_list b  =
    let rec (aux:bytes -> Tot (CanFail (serverName))) = fun b ->
        if equalBytes b empty_bytes then ExOK([])
        else
            let (ty,v) = split b 1 in
            (match vlsplit 2 v with
            | Error(x,y) -> ExFail(x,"Failed to parse sni length")
            | Correct(cur, next) ->
                (match aux next with
                | ExFail(x,y) -> ExFail(x,y)
                | ExOK(l) ->
		    admit();
                    let cur =
                        (match cbyte ty with
                        | 0uy -> SNI_DNS(cur)
                        | v -> SNI_UNKNOWN(int_of_bytes ty, cur))
                    in let (snidup:serverName -> Tot bool) = fun x ->
                        (match (x,cur) with
                        | SNI_DNS _, SNI_DNS _ -> true
                        | SNI_UNKNOWN(a,_), SNI_UNKNOWN(b, _) when (a=b) -> true
                        | _ -> false)
		       in if List.existsb snidup l then ExFail(AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Duplicate SNI type")
                    else ExOK(cur :: l)))
    in (match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK([]) -> Error(AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Empty SNI extension")
    | ExOK(l) -> correct (l))

val compile_curve_list: list ECGroup.ec_all_curve -> Tot bytes
let compile_curve_list l =
    let rec (aux:list ECGroup.ec_all_curve -> Tot bytes) =
        function
        | [] -> empty_bytes
        | ECGroup.EC_CORE c :: r ->
            let cid = ECGroup.curve_id (ECGroup.getParams c) in
            cid @| aux r
        | ECGroup.EC_EXPLICIT_PRIME :: r -> abyte2 (255uy, 01uy) @| aux r
        | ECGroup.EC_EXPLICIT_BINARY :: r -> abyte2 (255uy, 02uy) @| aux r
        | ECGroup.EC_UNKNOWN(x) :: r -> bytes_of_int 2 x @| aux r
    in
    let al = aux l in
    let bl: bytes = vlbytes 2 al in
    bl

val parse_curve_list: bytes -> Tot (Result (list ECGroup.ec_all_curve))
let parse_curve_list b =
    let rec (aux:bytes -> Tot (CanFail ECGroup.ec_all_curve)) = fun b ->
        if equalBytes b empty_bytes then ExOK([])
        else if (length b) % 2 = 1 then ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Bad encoding of curve list")
        else let (u,v) = split b 2 in
            (match aux v with
            | ExFail(x,y) -> ExFail(x,y)
            | ExOK(l) ->
                let cur =
                    (match cbyte2 u with
                    | (0uy, 23uy) -> ECGroup.EC_CORE CoreCrypto.ECC_P256
                    | (0uy, 24uy) -> ECGroup.EC_CORE CoreCrypto.ECC_P384
                    | (0uy, 25uy) -> ECGroup.EC_CORE CoreCrypto.ECC_P521
                    | (255uy, 1uy) -> ECGroup.EC_EXPLICIT_PRIME
                    | (255uy, 2uy) -> ECGroup.EC_EXPLICIT_BINARY
                    | _ -> ECGroup.EC_UNKNOWN(int_of_bytes u))
                in
                    if List.mem cur l then ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Duplicate curve")
                    else ExOK(cur :: l))
    in (match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK([]) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Empty supported curve list")
    | ExOK(l) -> correct (l))

val parse_ecpf_list: bytes -> Tot (Result (list ECGroup.point_format))
let parse_ecpf_list b =
    let rec (aux:bytes -> Tot (CanFail (ECGroup.point_format))) = fun b ->
        if equalBytes b empty_bytes then ExOK([])
        else let (u,v) = split b 1 in
            (match aux v with
            | ExFail(x,y) -> ExFail(x,y)
            | ExOK(l) ->
                let cur = match cbyte u with
                | 0uy -> ECGroup.ECP_UNCOMPRESSED
                | _ -> ECGroup.ECP_UNKNOWN(int_of_bytes u)
                in ExOK(cur :: l))
    in (match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK(l) when not (List.mem ECGroup.ECP_UNCOMPRESSED l) ->
        Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Uncompressed point format not supported")
    | ExOK(l) -> correct (l))

val compile_ecpf_list: list ECGroup.point_format -> Tot bytes
let compile_ecpf_list l =
    let rec (aux:list ECGroup.point_format -> Tot bytes) =
        function
        | [] -> empty_bytes
        | ECGroup.ECP_UNCOMPRESSED :: r -> (abyte 0uy) @| aux r
        | ECGroup.ECP_UNKNOWN(t) :: r -> (bytes_of_int 1 t) @| aux r
    in
    let al = aux l in
    let bl:bytes = vlbytes 1 al in
    bl

val addOnce: extension -> list extension -> Tot (Result (list extension))
let addOnce ext extList =
    if List.existsb (sameExt ext) extList then
        Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
    else
        let res = ext::extList in
        correct(res)

val parseSCSVs: known_cipher_suites -> list extension -> Tot (Result (list extension))
let rec parseSCSVs ch_ciphers extL =
    if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV ch_ciphers then
        addOnce (E_renegotiation_info(FirstConnection)) extL
    else
        correct(extL)

val earlyDataIndicationBytes: earlyDataIndication -> Tot bytes
val extensionPayloadBytes: extension -> Tot bytes
val extensionBytes: extension -> Tot bytes
val extensionsBytes: cl:list extension -> Tot bytes
let rec earlyDataIndicationBytes edi =
  match edi with
  | ServerEarlyDataIndication -> empty_bytes
  | ClientEarlyDataIndication edi ->
      let cid_bytes = configurationIdBytes edi.ped_configuration_id in
      let cs_bytes = cipherSuiteBytes edi.ped_cipher_suite in
      let ext_bytes = extensionsBytes edi.ped_extensions in
      let context_bytes = vlbytes 1 edi.ped_context in
//      let edt_bytes = earlyDataTypeBytes edi.ped_early_data_type in
      cid_bytes @| cs_bytes @| ext_bytes @| context_bytes //@| edt_bytes
and extensionPayloadBytes ext =
  match ext with
  | E_earlyData edt           -> earlyDataIndicationBytes edt
  | E_preSharedKey psk        -> preSharedKeyBytes psk
  | E_keyShare ks             -> keyShareBytes ks
  | E_signatureAlgorithms sha -> sigHashAlgsBytes sha
  | E_renegotiation_info(ri)  -> renegotiationInfoBytes ri
  | E_server_name(l)          -> compile_sni_list l
  | E_extended_ms             -> empty_bytes
  | E_extended_padding        -> empty_bytes
  | E_supported_groups(l)     -> namedGroupsBytes l
  | E_ec_point_format(l)      -> compile_ecpf_list l
  | E_unknown_extension(h,b)  -> b
and extensionBytes ext =
    let head = extensionHeaderBytes ext in
    let payload = extensionPayloadBytes ext in
    let payload = vlbytes 2 payload in
    head @| payload
and extensionsBytes exts =
  vlbytes 2 (List.Tot.fold_left (fun l s -> l @| extensionBytes s) empty_bytes exts)

val parseEarlyDataIndication: pinverse Seq.Eq earlyDataIndicationBytes
val parseExtension: pinverse Seq.Eq extensionBytes
val parseExtensions: pinverse Seq.Eq extensionsBytes
let rec parseExtension b =
  if length b >= 4 then
    let (head, payload) = split b 2 in
    match vlparse 2 payload with
    | Correct (data) ->
	(match cbyte2 head with
	| (0x00uy, 0x0Duy) -> // sigalgs
	  (match parseSigHashAlgs (vlbytes 2 data) with
	  | Correct(algs) -> Correct (E_signatureAlgorithms algs)
	  | Error(z) -> Error(z))
	| (0x00uy, 0x00uy) -> // sni
	  (match parse_sni_list data with
	  | Correct(snis) -> Correct (E_server_name snis)
	  | Error(z) -> Error(z))
	| (0xFFuy, 0x01uy) -> // renego
	  (match parseRenegotiationInfo data with
	  | Correct(ri) -> Correct (E_renegotiation_info(ri))
	  | Error(z) -> Error(z))
	| (0x00uy, 0x0Auy) -> // supported groups
	  (match parseNamedGroups (vlbytes 2 data) with
	  | Correct(groups) -> Correct (E_supported_groups(groups))
	  | Error(z) -> Error(z))
	| (0x00uy, 0x0Buy) -> // ec point format
	  (match parse_ecpf_list data with
	  | Correct(ecpfs) -> Correct (E_ec_point_format(ecpfs))
	  | Error(z) -> Error(z))
	| (0x00uy, 0x17uy) -> // extended ms
	  if length data = 0 then Correct (E_extended_ms)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for extended MS extension")
	| (0xBBuy, 0x8Fuy) -> // extended padding
	  if length data = 0 then Correct (E_extended_padding)
	  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Got inappropriate bytes for extended padding extension")
	| (0x11uy, 0x11uy) -> // head TBD, early data
	  (match parseEarlyDataIndication data with
	  | Correct (edi) -> Correct (E_earlyData(edi))
	  | Error(z) -> Error(z))
	| (0x22uy, 0x22uy) -> // head TBD, pre shared key
	  (match parsePreSharedKey data with
	  | Correct(psk) -> Correct (E_preSharedKey(psk))
	  | Error(z) -> Error(z))
	| (0x33uy, 0x33uy) -> // head TBD, key share
	  (match parseKeyShare data with	    
	  | Correct (ks) -> Correct (E_keyShare(ks))
	  | Error(z) -> Error(z))
	| _ -> // Unknown extension
	  Correct(E_unknown_extension(head,data)))
    | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extension length 1")
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Extension bytes are too short to store even the extension type")
and parseEarlyDataIndication b = 
  if length b > 0 then
    match vlsplit 2 b with
    | Correct(config_id, data) ->
      match parseConfigurationId (vlbytes 2 config_id) with
      | Correct(cid) -> 
	if length data >= 2 then
	  let (cs, data) = split data 2 in
	  match parseCipherSuite cs with
	  | Correct(cs) -> 
	    match vlsplit 2 data with
	    | Correct(exts, data) -> 
	      match parseExtensions (vlbytes 2 exts) with
	      | Correct(exts) -> 
		match vlparse 1 data with
		| Correct(ctx) ->
		    Correct (ClientEarlyDataIndication ({ ped_configuration_id = cid;
							  ped_cipher_suite = cs;
							  ped_extensions = exts;
							  ped_context = ctx; }))
		| Error(z) -> Error(z)
	      | Error(z) -> Error(z)
	    | Error(z) -> Error(z)
	  | Error(z) -> Error(z)
	else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Not enough bytes to parse cipher suite in early data indication")
      | Error(z) -> Error(z)
    | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse early data indication length")
  else Correct (ServerEarlyDataIndication)
and parseExtensions b =
  let rec (aux:bytes -> list extension -> Tot (Result (list extension))) = fun b exts ->
    if length b >= 4 then
      let ht, b = split b 2 in
      match vlsplit 2 b with
      | Correct(ext, bytes) ->
	(match parseExtension (ht @| vlbytes 2 ext) with
	| Correct(ext) -> 
	  (match addOnce ext exts with // fails if the extension already is in the list
	  | Correct(exts) -> aux bytes exts
	  | Error(z) -> Error(z))
	| Error(z) -> Error(z))
      | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extension length 2")
    else Correct(exts) in
  match vlparse 2 b with
  | Correct(b) -> aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse extensions length")

val parseExtensionsWithCS: data:bytes -> known_cipher_suites -> Result (list extension)
let parseExtensionsWithCS data ch_ciphers =
  match parseExtensions data with
  | Correct(exts) -> parseSCSVs ch_ciphers exts
  | Error(z) -> Error(z)
  
// JK : Only client side ? 
val prepareExtensions: config -> ConnectionInfo -> cVerifyData -> l:list extension{List.length l < 256}
let prepareExtensions (cfg:config) (conn:ConnectionInfo) renegoCVD =
    (* Always send supported extensions. The configuration options will influence how strict the tests will be *)
    let res = [E_renegotiation_info(ClientRenegotiationInfo renegoCVD)] in
#if TLSExt_sessionHash
    let res = E_extended_ms :: res in
#endif
#if TLSExt_extendedPadding
    let res = E_extended_padding :: res in
#endif
    let res =
        let curves = List.map (fun x -> ECGroup.EC_CORE x) cfg.ecdhGroups in
        if curves <> [] && List.existsb (fun x -> isECDHECipherSuite x) cfg.ciphersuites then
	  let curves = List.map (fun x -> SEC x) cfg.ecdhGroups in
          E_ec_point_format([ECGroup.ECP_UNCOMPRESSED]) :: E_supported_groups(curves) :: res
        else res in
    res

// TODO : check function
val serverToNegotiatedExtension: list extension -> bool -> cipherSuite -> Result negotiatedExtensions -> extension -> Tot (Result (negotiatedExtensions))
let serverToNegotiatedExtension cExtL (resuming:bool) cs res sExt : Result (negotiatedExtensions)=
    match res with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
        if List.existsb (sameExt sExt) cExtL then
            match sExt with
            | E_renegotiation_info (ri) -> 
	      (match ri with
	      | ServerRenegotiationInfo(cvd,svd) -> correct ({l with ne_renegotiation_info=Some(cvd,svd)})
	      | _ -> Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent renegotiation info without server verified data"))
            | E_server_name _ ->
                if List.existsb (fun x->match x with E_server_name _ -> true | _ -> false) cExtL then correct(l)
                else Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an SNI acknowledgement without an SNI provided")
            | E_ec_point_format(spf) ->
                if resuming then
                    correct l
                else
                    correct ({l with ne_supported_point_formats = Some spf})
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
        else
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided an extension not given by the client")

val negotiateClientExtensions: list extension -> list extension -> bool -> cipherSuite -> Tot (Result (negotiatedExtensions))
let negotiateClientExtensions (cExtL:list extension) (sExtL:list extension) (resuming:bool) cs =
    let nes = ne_default in
    match List.Tot.fold_left (serverToNegotiatedExtension cExtL resuming cs) (correct nes) sExtL with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
        // Client-side specific extension negotiation
        // Nothing for now
        correct(l)

val clientToServerExtension: config -> cipherSuite -> (cVerifyData * sVerifyData) -> bool -> extension -> Tot (option extension)
let clientToServerExtension (cfg:config) (cs:cipherSuite) ((renegoCVD:cVerifyData),(renegoSVD:sVerifyData)) (resuming:bool) (cExt:extension) : (option (extension)) =
    match cExt with
    | E_earlyData b -> None    // JK : TODO
    | E_preSharedKey b -> None // JK : TODO
    | E_keyShare b -> None     // JK : TODO
    | E_renegotiation_info (_) -> Some (E_renegotiation_info (ServerRenegotiationInfo(renegoCVD,renegoSVD)))
    | E_server_name l ->
        (match List.Tot.tryFind (fun x->match x with SNI_DNS _ -> true | _ -> false) l with
        | Some _ -> Some(E_server_name l)
        | _ -> None)
    | E_ec_point_format(l) ->
        if resuming then None
        else Some(E_ec_point_format [ECGroup.ECP_UNCOMPRESSED])
    | E_supported_groups(l) -> None
    | E_extended_ms -> Some(E_extended_ms)
    | E_extended_padding ->
        if resuming then
            None
        else
            if isOnlyMACCipherSuite cs then
                None
            else
                Some(E_extended_padding)
    | E_unknown_extension b -> None    

val clientToNegotiatedExtension: config -> cipherSuite -> (cVerifyData * sVerifyData) -> bool -> negotiatedExtensions -> extension -> Tot negotiatedExtensions
let clientToNegotiatedExtension (cfg:config) cs ((cvd:cVerifyData),(svd:sVerifyData)) (resuming:bool)  neg cExt =
    match cExt with
    | E_renegotiation_info (_) -> {neg with ne_renegotiation_info=Some(cvd,svd)}
    | E_supported_groups l ->
        if resuming then neg
        else
            let rec (okcurves:list namedGroup -> Tot (list ec_curve)) = function
            | SEC(x) :: r ->
                let rl = okcurves r in
                if List.existsb (fun x -> x = x) cfg.ecdhGroups then x::rl else rl
            | x :: r -> okcurves r
            | [] -> [] in
            {neg with ne_supported_curves = Some (okcurves l)}
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
            {neg with ne_extended_ms = true}
    | E_extended_padding ->
        if resuming then
            neg
        else
            if isOnlyMACCipherSuite cs then
                neg
            else
                {neg with ne_extended_padding = true}
    | _ -> neg // JK : handle remaining cases

val negotiateServerExtensions: list extension -> config -> cipherSuite -> (cVerifyData*sVerifyData) -> bool -> Tot (list extension * negotiatedExtensions)
let negotiateServerExtensions cExtL cfg cs (cvd,svd) resuming  :  (list extension * negotiatedExtensions) =
    let server = List.Tot.choose (clientToServerExtension cfg cs (cvd,svd) resuming) cExtL in
    let negi = ne_default in
    let nego = List.Tot.fold_left (clientToNegotiatedExtension cfg cs (cvd,svd) resuming) negi cExtL in
    (server,nego)

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

val hasExtendedPadding: id -> Tot bool
let hasExtendedPadding id = id.ext.ne_extended_padding = true

// JK : cannot add total effect here because of the exception thrown
val default_sigHashAlg_fromSig: ProtocolVersion -> sigAlg -> (list sigHashAlg)
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

val default_sigHashAlg: ProtocolVersion -> cipherSuite -> l:list Sig.alg{List.length l <= 1}
let default_sigHashAlg pv cs =
    default_sigHashAlg_fromSig pv (sigAlg_of_ciphersuite cs)

val sigHashAlg_contains: list Sig.alg -> Sig.alg -> Tot bool
let sigHashAlg_contains (algList:list Sig.alg) (alg:Sig.alg) =
    List.existsb (fun a -> a = alg) algList

val sigHashAlg_bySigList: list Sig.alg -> list sigAlg -> Tot (list Sig.alg)
let sigHashAlg_bySigList (algList:list Sig.alg) (sigAlgList:list sigAlg):list Sig.alg =
    List.Tot.choose (fun alg -> let (sigA,_) = alg in if (List.existsb (fun a -> a = sigA) sigAlgList) then Some(alg) else None) algList

val cert_type_to_SigHashAlg: certType -> ProtocolVersion -> list sigHashAlg
let cert_type_to_SigHashAlg ct pv =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> default_sigHashAlg_fromSig pv DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> default_sigHashAlg_fromSig pv RSASIG

val cert_type_list_to_SigHashAlg: list certType -> ProtocolVersion -> list sigHashAlg
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
