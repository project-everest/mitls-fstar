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

type preEarlyDataIndication =
  { ped_configuration_id: configuration_id;
    ped_cipher_suite:cipherSuite;
    ped_extensions:list extension;
    ped_content:bytes;
    ped_early_data_type:earlyDataType; }
and earlyDataIndication = 
  | ClientEarlyDataIndication of preEarlyDataIndication 
  | ServerEarlyDataIndication
// JK : can I merge client extensions and server extensions ?
and extension = 
  // TLS 1.3 extension types
  | E_earlyData of earlyDataIndication // JK : TODO : put appropriate type
  | E_preSharedKey of preSharedKey // JK : TODO : put appropriate type
  | E_keyShare of keyShare // JK : TODO : put appropriate type
  // Common extension types
  | E_signatureAlgorithms of (list sigHashAlg) // JK : TODO : put appropriate type, did it previously appear ?
  // Previous extension types
  | E_renegotiation_info of (cVerifyData * option sVerifyData) // JK : option is some if server side
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
            | Error(x,y) -> ExFail(x,y)
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

val parse_ecpf_list: bytes -> (Result (list ECGroup.point_format))
let parse_ecpf_list b =
    let rec aux b =
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


val earlyDataIndicationBytes: earlyDataIndication -> Tot bytes
val extensionPayloadBytes: extension -> Tot bytes
val extensionBytes: extension -> Tot bytes
val extensionsBytes: cl:list extension -> Tot (b:bytes{length b < ((List.length cl) * 65539)})
let rec earlyDataIndicationBytes edi =
  match edi with
  | ServerEarlyDataIndication -> empty_bytes
  | ClientEarlyDataIndication edi ->
      let cid_bytes = configurationIdBytes edi.ped_configuration_id in
      let cs_bytes = cipherSuiteBytes edi.ped_cipher_suite in
      let ext_bytes = extensionsBytes edi.ped_extensions in
      let content_bytes = vlbytes 1 edi.ped_content in
      let edt_bytes = earlyDataTypeBytes edi.ped_early_data_type in
      cid_bytes @| cs_bytes @| ext_bytes @| content_bytes @| edt_bytes
and extensionPayloadBytes ext =
  match ext with
  | E_earlyData edt           -> earlyDataIndicationBytes edt
  | E_preSharedKey psk        -> preSharedKeyBytes psk
  | E_keyShare ks             -> keyShareBytes ks
  | E_signatureAlgorithms sha -> sigHashAlgsBytes sha
  | E_renegotiation_info(cvd, svd) -> 
    (match svd with | None -> vlbytes 1 cvd | Some svd' -> let p = cvd @| svd' in vlbytes 1 p)
  | E_server_name(l) -> compile_sni_list l
  | E_extended_ms -> empty_bytes
  | E_extended_padding -> empty_bytes
  | E_supported_groups(l) -> namedGroupsBytes l
  | E_ec_point_format(l) -> compile_ecpf_list l
  | E_unknown_extension(h,b) -> b
and extensionBytes ext =
    let head = extensionHeaderBytes ext in
    let payload = extensionPayloadBytes ext in
    let payload = vlbytes 2 payload in
    head @| payload
and extensionsBytes exts =
  List.fold_leftT (fun l s -> l @| extensionBytes s) empty_bytes exts

(*
let parseExtension head payload role =
    match cbyte2 head with
    | (0uy, 0uy) -> // Server name indication
        (match vlparse 2 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(sni) ->
            (match parse_sni_list sni with
            | Error (x,y) -> Some(Error(x,y))
            | Correct(l) -> Some(correct (E_server_name(l)))))
    | (0xFFuy, 0x01uy) -> // renegotiation info
        (match vlparse 1 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(vd) ->
	  (match role with 
	   | Client ->
            (let res = E_renegotiation_info (vd,None) in
            let res = correct res in
            Some(res))
	   | Server -> 
	    (let vdL = length vd in
	    let (cvd, svd) = split vd (vdL/2) in
	    let res = E_renegotiation_info(cvd,Some svd) in
	    let res = correct res in
	    Some res)))
    | (0x00uy, 0x0Auy) -> // Supported EC curves
        (match vlparse 2 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(ecl) ->
            (match parse_curve_list ecl with
            | Error (x,y) -> Some(Error(x,y))
            | Correct(l) -> Some(correct (E_supported_groups(l)))))
    | (0x00uy, 0x0Buy) -> // Supported EC point formats
        (match vlparse 1 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(ecpf) ->
            (match parse_ecpf_list ecpf with
            | Error (x,y) -> Some(Error(x,y))
            | Correct(l) -> Some(correct (E_ec_point_format(l)))))
#if TLSExt_sessionHash
    | (0x00uy, 0x17uy) -> // extended_ms
        if equalBytes payload empty_bytes then
            Some(correct (E_extended_ms))
        else
            Some(Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invalid data for extended master secret extension"))
#endif
#if TLSExt_extendedPadding
    | (0xBBuy, 0x8Fuy) -> // extended_padding
        if equalBytes payload empty_bytes then
            Some(correct (E_extended_padding))
        else
            Some(Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invalid data for extended padding extension"))
#endif
    // JK : used to be skipped, now stored as "unknown extension"
    | (_,_) -> Some (correct (E_unknown_extension (head @| payload)))

let addOnce ext extList =
    if List.existsb (sameExt ext) extList then
        Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
    else
        let res = ext::extList in
        correct(res)

let rec parseExtensionList ext extList role =
    match length ext with
    | 0 -> correct (extList)
    | x when (x < 4) ->
        (* This is a parsing error, or a malformed extension *)
        Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | _ ->
        let (extTypeBytes,rem) = Platform.Bytes.split ext 2 in
        match vlsplit 2 rem with
            | Error(x,y) -> Error (x,y) (* Parsing error *)
            | Correct (res) ->
                let (payload,rem) = res in
                match parseExtension extTypeBytes payload role with
                | None ->
		    // JK : this case does not happen anymore
                    (* Unknown extension, skip it *)
                    parseExtensionList rem extList role		    
                | Some(res) ->
                    match res with
                    | Error(x,y) -> Error(x,y)
                    | Correct(ce) ->
                        match addOnce ce extList with
                        | Error(x,y) -> Error(x,y)
                        | Correct(extList) -> parseExtensionList rem extList role

let rec parseSCSVs ch_ciphers extL =
    if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV ch_ciphers then
        addOnce (E_renegotiation_info(empty_bytes, None)) extL
    else
        correct(extL)

val parseExtensions: data:bytes -> known_cipher_suites -> role -> Result (list extension)
let parseExtensions data ch_ciphers role =
    match length data with
    | 0 -> parseSCSVs ch_ciphers []
    | 1 -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | _ ->
        match vlparse 2 data with
        | Error(x,y)    -> Error(x,y)
        | Correct(exts) ->
            match parseExtensionList exts [] role with
            | Error(x,y) -> Error(x,y)
            | Correct(extL) -> parseSCSVs ch_ciphers extL

// JK : Only client side ? 
val prepareExtensions: config -> ConnectionInfo -> cVerifyData -> l:list extension{List.length l < 256}
let prepareExtensions (cfg:config) (conn:ConnectionInfo) renegoCVD =
    (* Always send supported extensions. The configuration options will influence how strict the tests will be *)
    let res = [E_renegotiation_info(renegoCVD, None)] in
#if TLSExt_sessionHash
    let res = E_extended_ms :: res in
#endif
#if TLSExt_extendedPadding
    let res = E_extended_padding :: res in
#endif
    let res =
        let curves = List.map (fun x -> ECGroup.EC_CORE x) cfg.ecdhGroups in
        if curves <> [] && List.existsb (fun x -> isECDHECipherSuite x) cfg.ciphersuites then
            E_ec_point_format([ECGroup.ECP_UNCOMPRESSED]) :: E_supported_groups(curves) :: res
        else res in
    res

let serverToNegotiatedExtension cExtL (resuming:bool) cs res sExt : Result (negotiatedExtensions)=
    match res with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
        if List.existsb (sameExt sExt) cExtL then
            match sExt with
            | E_renegotiation_info (cvd,svd) -> 
	      (match svd with
	      | Some svd' -> correct ({l with ne_renegotiation_info=Some(cvd,svd')})
	      | None -> Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent renegotiation info without server verified data"))
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

let negotiateClientExtensions (cExtL:list extension) (sExtL:list extension) (resuming:bool) cs =
    let nes = ne_default in
    match List.fold_left (serverToNegotiatedExtension cExtL resuming cs) (correct nes) sExtL with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
        // Client-side specific extension negotiation
        // Nothing for now
        correct(l)

let clientToServerExtension (cfg:config) (cs:cipherSuite) ((renegoCVD:cVerifyData),(renegoSVD:sVerifyData)) (resuming:bool) (cExt:extension) : (option (extension)) =
    match cExt with
    | E_earlyData b -> None    // JK : how to handle these here ?
    | E_preSharedKey b -> None // JK : how to handle these here ?
    | E_keyShare b -> None     // JK : how to handle these here ?
    | E_renegotiation_info (_) -> Some (E_renegotiation_info (renegoCVD,renegoSVD))
    | E_server_name l ->
        (match List.tryFind (fun x->match x with SNI_DNS _ -> true | _ -> false) l with
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
    

let clientToNegotiatedExtension (cfg:config) cs ((cvd:cVerifyData),(svd:sVerifyData)) (resuming:bool)  neg cExt =
    match cExt with
    | E_renegotiation_info (_) -> {neg with ne_renegotiation_info=Some(cvd,svd)}
    | E_supported_groups l ->
        if resuming then neg
        else
            let rec okcurves = function
            | ECGroup.EC_CORE(x) :: r ->
                let rl = okcurves r in
                if List.existsb (fun x -> x = x) cfg.ecdhGroups then x::rl else rl
            | x :: r -> okcurves r
            | [] -> [] in
            {neg with ne_supported_curves = Some (okcurves l)}
    | E_ec_point_format l ->
        if resuming then neg
        else
            let nl = List.filter (fun x -> x = ECGroup.ECP_UNCOMPRESSED) l in
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

let negotiateServerExtensions cExtL cfg cs (cvd,svd) resuming  :  (list extension * negotiatedExtensions) =
    let server = List.choose (clientToServerExtension cfg cs (cvd,svd) resuming) cExtL in
    let negi = ne_default in
    let nego = List.fold_left (clientToNegotiatedExtension cfg cs (cvd,Some.v svd) resuming) negi cExtL in
    (server,nego)

let isClientRenegotiationInfo e =
    match e with
    | E_renegotiation_info(cvd, None) -> Some(cvd)
    | _ -> None

let checkClientRenegotiationInfoExtension config (cExtL: list extension) cVerifyData =
    match List.tryPick isClientRenegotiationInfo cExtL with
    | None -> not (config.safe_renegotiation)
    | Some(payload) -> equalBytes payload cVerifyData

let isServerRenegotiationInfo e =
    match e with
    | E_renegotiation_info (cvd,Some svd) -> Some((cvd,svd))
    | _ -> None

let checkServerRenegotiationInfoExtension config (sExtL: list extension) cVerifyData sVerifyData =
    match List.tryPick isServerRenegotiationInfo sExtL with
    | None -> not (config.safe_renegotiation)
    | Some(x) ->
        let (cvd,svd) = x in
        equalBytes (cvd @| svd) (cVerifyData @| sVerifyData)

let hasExtendedMS extL = extL.ne_extended_ms = true

let hasExtendedPadding id = id.ext.ne_extended_padding = true

(* sigHashAlg parsing functions *)
let sigHashAlgBytes alg =
    // pre: we're in TLS 1.2
    let (sign,hash) = alg in
    let signB = sigAlgBytes sign in
    let hashB = hashAlgBytes hash in
    hashB @| signB

let parseSigHashAlg b =
    let (hashB,signB) = Platform.Bytes.split b 1 in
    match parseSigAlg signB with
    | Error(x,y) -> Error(x,y)
    | Correct(sign) ->
        match parseHashAlg hashB with
        | Error(x,y) -> Error(x,y)
        | Correct(hash) -> correct(sign,hash)

assume val sigHashAlgListBytes: sal:list Sig.alg -> Tot (lbytes (2* List.length sal))
(*
let rec sigHashAlgListBytes algL =
    match algL with
    | [] -> empty_bytes
    | h::t ->
        let oneItem = sigHashAlgBytes h in
        oneItem @| sigHashAlgListBytes t
*)
let rec parseSigHashAlgList b : (Result (list Sig.alg))=
    if length b = 0 then correct([])
    else if length b = 1 then Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else
        let (thisB,remB) = Platform.Bytes.split b 2 in
        match parseSigHashAlgList remB with
        | Error(x,y) -> Error(x,y)
        | Correct(rem) ->
            match parseSigHashAlg thisB with
            | Error(x,y) -> // skip this one
                correct(rem)
            | Correct(this) ->
                correct(this :: rem)

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

let sigHashAlg_contains (algList:list Sig.alg) (alg:Sig.alg) =
    List.existsb (fun a -> a = alg) algList

let sigHashAlg_bySigList (algList:list Sig.alg) (sigAlgList:list sigAlg):list Sig.alg =
    List.choose (fun alg -> let (sigA,_) = alg in if (List.existsb (fun a -> a = sigA) sigAlgList) then Some(alg) else None) algList

let cert_type_to_SigHashAlg ct pv =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> default_sigHashAlg_fromSig pv DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> default_sigHashAlg_fromSig pv RSASIG

let rec cert_type_list_to_SigHashAlg ctl pv =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> (cert_type_to_SigHashAlg h pv) @ (cert_type_list_to_SigHashAlg t pv)

let cert_type_to_SigAlg ct =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> RSASIG

let rec cert_type_list_to_SigAlg ctl =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> (cert_type_to_SigAlg h) :: (cert_type_list_to_SigAlg t)
