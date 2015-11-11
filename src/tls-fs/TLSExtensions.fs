(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLSExtensions

open Bytes
open Error
open TLSError
open TLSConstants
open TLSInfo

type clientExtension =
    | CE_renegotiation_info of cVerifyData
    | CE_server_name of list<serverName>
    | CE_extended_ms
    | CE_extended_padding
    | CE_ec_point_format of list<ECGroup.point_format>
    | CE_ec_curves of list<ECGroup.ec_all_curve>

let sameClientExt a b =
    match a,b with
    | CE_renegotiation_info (_), CE_renegotiation_info (_) -> true
    | CE_server_name _, CE_server_name _ -> true
    | CE_extended_ms, CE_extended_ms -> true
    | CE_extended_padding, CE_extended_padding -> true
    | CE_ec_curves _, CE_ec_curves _ -> true
    | CE_ec_point_format _, CE_ec_point_format _ -> true
    | _,_ -> false

type serverExtension =
    | SE_renegotiation_info of cVerifyData * sVerifyData
    | SE_server_name
    | SE_extended_ms
    | SE_extended_padding
    | SE_ec_point_format of list<ECGroup.point_format>

let sameServerExt a b =
    match a,b with
    | SE_renegotiation_info (_,_), SE_renegotiation_info (_,_) -> true
    | SE_server_name, SE_server_name -> true
    | SE_extended_ms, SE_extended_ms -> true
    | SE_extended_padding, SE_extended_padding -> true
    | SE_ec_point_format _, SE_ec_point_format _ -> true
    | _,_ -> false

let sameServerClientExt a b =
    match a,b with
    | SE_renegotiation_info (_,_), CE_renegotiation_info (_) -> true
    | SE_server_name, CE_server_name _ -> true
    | SE_extended_ms, CE_extended_ms -> true
    | SE_extended_padding, CE_extended_padding -> true
    | SE_ec_point_format _, CE_ec_point_format _ -> true
    | _,_ -> false

let clientExtensionHeaderBytes ext =
    match ext with
    | CE_renegotiation_info(_) -> abyte2 (0xFFuy, 0x01uy)
    | CE_server_name (_)       -> abyte2 (0x00uy, 0x00uy)
    | CE_extended_ms           -> abyte2 (0x00uy, 0x17uy)
    | CE_extended_padding      -> abyte2 (0xBBuy, 0x8Fuy)
    | CE_ec_point_format _     -> abyte2 (0x00uy, 0x0Buy)
    | CE_ec_curves _           -> abyte2 (0x00uy, 0x0Auy)

type 'a CanFail =
| ExFail of alertDescription * string
| ExOK of 'a list

let compile_sni_list l =
    let rec aux = function
    | [] -> empty_bytes
    | SNI_DNS(x) :: r -> (abyte 0uy) @| bytes_of_int 2 (length x) @| x @| aux r
    | SNI_UNKNOWN(t, x) :: r -> (bytes_of_int 1 t) @| bytes_of_int 2 (length x) @| x @| aux r
    in aux l

let parse_sni_list b : Result<serverName list> =
    let rec aux b =
        if equalBytes b empty_bytes then ExOK([])
        else
            let (ty,v) = split b 1 in
            (match vlsplit 2 v with
            | Error(x,y) -> ExFail(x,y)
            | Correct(cur, next) -> 
                (match aux next with
                | ExFail(x,y) -> ExFail(x,y)
                | ExOK(l) ->
                    let cur =
                        (match cbyte ty with
                        | 0uy -> SNI_DNS(cur)
                        | v -> SNI_UNKNOWN(int_of_bytes ty, cur))
                    in let snidup x =
                        (match (x,cur) with
                        | SNI_DNS _, SNI_DNS _ -> true 
                        | SNI_UNKNOWN(a,_), SNI_UNKNOWN(b, _) when a=b -> true
                        | _ -> false)
                    in if List.exists snidup l then ExFail(AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Duplicate SNI type")
                    else ExOK(cur :: l)))
    in (match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK([]) -> Error(AD_unrecognized_name, perror __SOURCE_FILE__ __LINE__ "Empty SNI extension")
    | ExOK(l) -> correct (l))

let compile_curve_list l =
    let rec aux =
        function
        | [] -> empty_bytes
        | ECGroup.EC_CORE c :: r ->
            let cid = ECGroup.curve_id (ECGroup.getParams c) in
            cid @| aux r
        | ECGroup.EC_EXPLICIT_PRIME :: r -> abyte2 (255uy, 01uy) @| aux r
        | ECGroup.EC_EXPLICIT_BINARY :: r -> abyte2 (255uy, 02uy) @| aux r
        | ECGroup.EC_UNKNOWN(x) :: r -> bytes_of_int 2 x @| aux r
    in vlbytes 2 (aux l)

let parse_curve_list b : Result<list<ECGroup.ec_all_curve>> =   
    let rec aux b =
        if equalBytes b empty_bytes then ExOK([])
        elif (length b) % 2 = 1 then ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Bad encoding of curve list")
        else let (u,v) = split b 2 in
            (match aux v with
            | ExFail(x,y) -> ExFail(x,y)
            | ExOK(l) ->
                let cur =
                    (match cbyte2 u with
                    | (0uy, 23uy) -> ECGroup.EC_CORE ECGroup.ECC_P256
                    | (0uy, 24uy) -> ECGroup.EC_CORE ECGroup.ECC_P384
                    | (0uy, 25uy) -> ECGroup.EC_CORE ECGroup.ECC_P521
                    | (255uy, 1uy) -> ECGroup.EC_EXPLICIT_PRIME
                    | (255uy, 2uy) -> ECGroup.EC_EXPLICIT_BINARY
                    | _ -> ECGroup.EC_UNKNOWN(int_of_bytes u))
                in
                    if List.exists ((=)cur) l then ExFail(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Duplicate curve")
                    else ExOK(cur :: l))
    in (match aux b with
    | ExFail(x,y) -> Error(x,y)
    | ExOK([]) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Empty supported curve list")
    | ExOK(l) -> correct (l))

let parse_ecpf_list b : Result<list<ECGroup.point_format>> =
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
    | ExOK(l) when not (List.exists ((=)ECGroup.ECP_UNCOMPRESSED) l) ->
        Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Uncompressed point format not supported")
    | ExOK(l) -> correct (l))

let compile_ecpf_list l =
    let rec aux =
        function
        | [] -> empty_bytes
        | ECGroup.ECP_UNCOMPRESSED :: r -> (abyte 0uy) @| aux r
        | ECGroup.ECP_UNKNOWN(t) :: r -> (bytes_of_int 1 t) @| aux r 
    in vlbytes 1 (aux l)

let clientExtensionPayloadBytes ext =
    match ext with
    | CE_renegotiation_info(cvd) -> vlbytes 1 cvd
    | CE_server_name(l) -> compile_sni_list l
    | CE_extended_ms -> empty_bytes
    | CE_extended_padding -> empty_bytes
    | CE_ec_curves(l) -> compile_curve_list l
    | CE_ec_point_format(l) -> compile_ecpf_list l

let clientExtensionBytes ext =
    let head = clientExtensionHeaderBytes ext in
    let payload = clientExtensionPayloadBytes ext in
    let payload = vlbytes 2 payload in
    head @| payload

let clientExtensionsBytes extL =
    let extBL = List.map (fun e -> clientExtensionBytes e) extL in
    let extB = List.fold (fun s l -> s @| l) empty_bytes extBL in
    if equalBytes extB empty_bytes then
        empty_bytes
    else
        vlbytes 2 extB

let parseClientExtension head payload =
    match cbyte2 head with
    | (0uy, 0uy) -> // Server name indication
        (match vlparse 2 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(sni) ->
            (match parse_sni_list sni with
            | Error (x,y) -> Some(Error(x,y))
            | Correct(l) -> Some(correct (CE_server_name(l)))))
    | (0xFFuy, 0x01uy) -> // renegotiation info
        (match vlparse 1 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(cvd) ->
            let res = CE_renegotiation_info (cvd) in
            let res = correct res in
            Some(res))
    | (0x00uy, 0x0Auy) -> // Supported EC curves
        (match vlparse 2 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(ecl) ->
            (match parse_curve_list ecl with
            | Error (x,y) -> Some(Error(x,y))
            | Correct(l) -> Some(correct (CE_ec_curves(l)))))
    | (0x00uy, 0x0Buy) -> // Supported EC point formats
        (match vlparse 1 payload with
        | Error (x,y) -> Some(Error(x,y))
        | Correct(ecpf) ->
            (match parse_ecpf_list ecpf with
            | Error (x,y) -> Some(Error(x,y))
            | Correct(l) -> Some(correct (CE_ec_point_format(l)))))
#if TLSExt_sessionHash
    | (0x00uy, 0x17uy) -> // extended_ms
        if equalBytes payload empty_bytes then
            Some(correct (CE_extended_ms))
        else
            Some(Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invalid data for extended master secret extension"))
#endif
#if TLSExt_extendedPadding
    | (0xBBuy, 0x8Fuy) -> // extended_padding
        if equalBytes payload empty_bytes then
            Some(correct (CE_extended_padding))
        else
            Some(Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invalid data for extended padding extension"))
#endif
    | (_,_) -> None

let addOnceClient ext extList =
    if List.exists (sameClientExt ext) extList then
        Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
    else
        let res = ext::extList in
        correct(res)

let rec parseClientExtensionList ext extList =
    match length ext with
    | 0 -> correct (extList)
    | x when x < 4 ->
        (* This is a parsing error, or a malformed extension *)
        Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | _ ->
        let (extTypeBytes,rem) = Bytes.split ext 2 in
        match vlsplit 2 rem with
            | Error(x,y) -> Error (x,y) (* Parsing error *)
            | Correct (res) ->
                let (payload,rem) = res in
                match parseClientExtension extTypeBytes payload with
                | None ->
                    (* Unknown extension, skip it *)
                    parseClientExtensionList rem extList
                | Some(res) ->
                    match res with
                    | Error(x,y) -> Error(x,y)
                    | Correct(ce) ->
                        match addOnceClient ce extList with
                        | Error(x,y) -> Error(x,y)
                        | Correct(extList) -> parseClientExtensionList rem extList

let rec parseClientSCSVs ch_ciphers extL =
    if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV ch_ciphers then
        addOnceClient (CE_renegotiation_info(empty_bytes)) extL
    else
        correct(extL)

let parseClientExtensions data ch_ciphers =
    match length data with
    | 0 -> parseClientSCSVs ch_ciphers []
    | 1 -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | _ ->
        match vlparse 2 data with
        | Error(x,y)    -> Error(x,y)
        | Correct(exts) ->
            match parseClientExtensionList exts [] with
            | Error(x,y) -> Error(x,y)
            | Correct(extL) -> parseClientSCSVs ch_ciphers extL

let prepareClientExtensions (cfg:config) (conn:ConnectionInfo) renegoCVD =
    (* Always send supported extensions. The configuration options will influence how strict the tests will be *)
    let res = [CE_renegotiation_info(renegoCVD)] in
#if TLSExt_sessionHash
    let res = CE_extended_ms :: res in
#endif
#if TLSExt_extendedPadding
    let res = CE_extended_padding :: res in
#endif
    let res = 
        let curves = List.map (fun x -> ECGroup.EC_CORE x) cfg.ecdhGroups in
        if curves <> [] && List.exists (fun x -> isECDHECipherSuite x) cfg.ciphersuites then
            CE_ec_point_format([ECGroup.ECP_UNCOMPRESSED]) :: CE_ec_curves(curves) :: res
        else res in
    res

let serverToNegotiatedExtension cExtL (resuming:bool) cs res sExt : Result<negotiatedExtensions>=
    match res with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
        if List.exists (sameServerClientExt sExt) cExtL then
            match sExt with
            | SE_renegotiation_info (cvd,svd) -> correct ({l with ne_renegotiation_info=Some(cvd,svd)})
            | SE_server_name ->
                if List.exists (fun x->match x with CE_server_name _ -> true | _ -> false) cExtL then correct(l)
                else Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an SNI acknowledgement without an SNI provided")
            | SE_ec_point_format(spf) ->
                if resuming then
                    correct l
                else
                    correct {l with ne_supported_point_formats = Some spf}
            | SE_extended_ms ->
                if resuming then
                    correct(l)
                else
                    correct({l with ne_extended_ms = true})
            | SE_extended_padding ->
                if resuming then
                    Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided extended padding in a resuming handshake")
                else
                    if isOnlyMACCipherSuite cs then
                        Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided extended padding for a MAC only ciphersuite")
                    else
                        correct({l with ne_extended_padding = true})
        else
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided an extension not given by the client")

let negotiateClientExtensions (cExtL:list<clientExtension>) (sExtL:list<serverExtension>) (resuming:bool) cs =
    let nes = ne_default in
    match Collections.List.fold (serverToNegotiatedExtension cExtL resuming cs) (correct nes) sExtL with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
        // Client-side specific extension negotiation
        // Nothing for now
        correct(l)

let serverExtensionHeaderBytes ext =
    match ext with
    | SE_renegotiation_info (_,_) -> abyte2 (0xFFuy, 0x01uy)
    | SE_server_name (_)          -> abyte2 (0x00uy, 0x00uy)
    | SE_extended_ms              -> abyte2 (0x00uy, 0x17uy)
    | SE_extended_padding         -> abyte2 (0xBBuy, 0x8Fuy)
    | SE_ec_point_format _        -> abyte2 (0x00uy, 0x0Buy)

let serverExtensionPayloadBytes ext =
    match ext with
    | SE_renegotiation_info (cvd,svd) ->
        let p = cvd @| svd in
        vlbytes 1 p
    | SE_ec_point_format(l) -> compile_ecpf_list l
    | SE_server_name -> empty_bytes
    | SE_extended_ms -> empty_bytes
    | SE_extended_padding -> empty_bytes

let serverExtensionBytes ext =
    let head = serverExtensionHeaderBytes ext in
    let payload = serverExtensionPayloadBytes ext in
    let payload = vlbytes 2 payload in
    head @| payload

let serverExtensionsBytes extL =
    let extBL = List.map (fun e -> serverExtensionBytes e) extL in
    let extB = List.fold (fun s l -> s @| l) empty_bytes extBL in
    if equalBytes extB empty_bytes then
        empty_bytes
    else
        vlbytes 2 extB

let parseServerExtension head payload =
    match cbyte2 head with
    | (0xFFuy, 0x01uy) -> // renegotiation info
        (match vlparse 1 payload with
        | Error (x,y) -> Error(x,y)
        | Correct(vd) ->
            let vdL = length vd in
            let (cvd,svd) = split vd (vdL/2) in
            let res = SE_renegotiation_info (cvd,svd) in
            correct(res))
    | (0x00uy, 0x17uy) -> // extended master secret
        if equalBytes payload empty_bytes then
            correct(SE_extended_ms)
        else
            Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invalid data for extended master secret extension")
    | (0xBBuy, 0x8Fuy) -> // extended padding
        if equalBytes payload empty_bytes then
            correct(SE_extended_padding)
        else
            Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invalid data for extended padding extension")
    | (0uy, 0x0Buy) -> // Supported EC point format
        (match vlparse 1 payload with
        | Error (x,y) -> Error(x,y)
        | Correct(ecpf) ->
            (match parse_ecpf_list ecpf with
            | Error (x,y) -> Error(x,y)
            | Correct(l) -> correct (SE_ec_point_format(l))))
        | (_,_) ->
        // A server can never send an extension the client doesn't support
        Error(AD_unsupported_extension, perror __SOURCE_FILE__ __LINE__ "Server provided an unsupported extension")

let addOnceServer ext extList =
    if List.exists (sameServerExt ext) extList then
        Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Same extension received more than once")
    else
        let res = ext::extList in
        correct(res)

let rec parseServerExtensionList ext extList =
    match length ext with
    | 0 -> correct (extList)
    | x when x < 4 ->
        (* This is a parsing error, or a malformed extension *)
        Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | _ ->
        let (extTypeBytes,rem) = Bytes.split ext 2 in
        match vlsplit 2 rem with
            | Error(x,y) -> Error (x,y) (* Parsing error *)
            | Correct (res) ->
                let (payload,rem) = res in
                match parseServerExtension extTypeBytes payload with
                | Error(x,y) -> Error(x,y)
                | Correct(ce) ->
                    match addOnceServer ce extList with
                    | Error(x,y) -> Error(x,y)
                    | Correct(extList) -> parseServerExtensionList rem extList

let parseServerExtensions data =
    match length data with
    | 0 -> let el = [] in correct (el)
    | 1 -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | _ ->
        match vlparse 2 data with
        | Error(x,y)    -> Error(x,y)
        | Correct(exts) -> parseServerExtensionList exts []

let ClientToServerExtension (cfg:config) cs ((renegoCVD:cVerifyData),(renegoSVD:sVerifyData)) (resuming:bool) cExt : option<serverExtension>=
    match cExt with
    | CE_renegotiation_info (_) -> Some (SE_renegotiation_info (renegoCVD,renegoSVD))
    | CE_server_name l ->
        (match List.tryFind (fun x->match x with SNI_DNS _ -> true | _ -> false) l with
        | Some _ -> Some(SE_server_name)
        | _ -> None)
    | CE_ec_point_format(l) ->
        if resuming then None
        else Some(SE_ec_point_format [ECGroup.ECP_UNCOMPRESSED])
    | CE_ec_curves(l) -> None
    | CE_extended_ms -> Some(SE_extended_ms)
    | CE_extended_padding ->
        if resuming then
            None
        else
            if isOnlyMACCipherSuite cs then
                None
            else
                Some(SE_extended_padding)

let clientToNegotiatedExtension (cfg:config) cs ((cvd:cVerifyData),(svd:sVerifyData)) (resuming:bool)  neg cExt =
    match cExt with
    | CE_renegotiation_info (_) -> {neg with ne_renegotiation_info=Some(cvd,svd)}
    | CE_ec_curves l ->
        if resuming then neg
        else
            let rec okcurves = function
            | ECGroup.EC_CORE(x) :: r ->
                let rl = okcurves r in
                if List.exists ((=)x) cfg.ecdhGroups then x::rl else rl
            | x :: r -> okcurves r
            | [] -> [] in
            {neg with ne_supported_curves = Some (okcurves l)}
    | CE_ec_point_format l ->
        if resuming then neg
        else
            let nl = List.filter (fun x -> x = ECGroup.ECP_UNCOMPRESSED) l in
            {neg with ne_supported_point_formats = Some nl}
    | CE_server_name l ->
        {neg with ne_server_names = Some l}
    | CE_extended_ms ->
        if resuming then
            neg
        else
            {neg with ne_extended_ms = true}
    | CE_extended_padding ->
        if resuming then
            neg
        else
            if isOnlyMACCipherSuite cs then
                neg
            else
                {neg with ne_extended_padding = true}

let negotiateServerExtensions cExtL cfg cs (cvd,svd) resuming  : serverExtension list  * negotiatedExtensions =
    let server = List.choose (ClientToServerExtension cfg cs (cvd,svd) resuming) cExtL in
    let negi = ne_default in
    let nego = Collections.List.fold (clientToNegotiatedExtension cfg cs (cvd,svd) resuming) negi cExtL in
    (server,nego)

let isClientRenegotiationInfo e =
    match e with
    | CE_renegotiation_info(cvd) -> Some(cvd)
    | _ -> None

let checkClientRenegotiationInfoExtension config (cExtL: list<clientExtension>) cVerifyData =
    match List.tryPick isClientRenegotiationInfo cExtL with
    | None -> not (config.safe_renegotiation)
    | Some(payload) -> equalBytes payload cVerifyData

let isServerRenegotiationInfo e =
    match e with
    | SE_renegotiation_info (cvd,svd) -> Some((cvd,svd))
    | _ -> None

let checkServerRenegotiationInfoExtension config (sExtL: list<serverExtension>) cVerifyData sVerifyData =
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
    let (hashB,signB) = Bytes.split b 1 in
    match parseSigAlg signB with
    | Error(x,y) -> Error(x,y)
    | Correct(sign) ->
        match parseHashAlg hashB with
        | Error(x,y) -> Error(x,y)
        | Correct(hash) -> correct(sign,hash)

let rec sigHashAlgListBytes algL =
    match algL with
    | [] -> empty_bytes
    | h::t ->
        let oneItem = sigHashAlgBytes h in
        oneItem @| sigHashAlgListBytes t

let rec parseSigHashAlgList b : (Result<list<Sig.alg>>)=
    if length b = 0 then correct([])
    elif length b = 1 then Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else
        let (thisB,remB) = Bytes.split b 2 in
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
    | SA_RSA ->
        (match pv with
        | TLS_1p2 -> [(SA_RSA, SHA)]
        | TLS_1p0 | TLS_1p1 | SSL_3p0 -> [(SA_RSA,MD5SHA1)])
        //| SSL_3p0 -> [(SA_RSA,NULL)]
    | SA_DSA ->
        [(SA_DSA,SHA)]
        //match pv with
        //| TLS_1p0| TLS_1p1 | TLS_1p2 -> [(SA_DSA, SHA)]
        //| SSL_3p0 -> [(SA_DSA,NULL)]
    | _ -> unexpected "[default_sigHashAlg_fromSig] invoked on an invalid signature algorithm"

let default_sigHashAlg pv cs =
    default_sigHashAlg_fromSig pv (sigAlg_of_ciphersuite cs)

let sigHashAlg_contains (algList:list<Sig.alg>) (alg:Sig.alg) =
    List.exists (fun a -> a = alg) algList

let sigHashAlg_bySigList (algList:list<Sig.alg>) (sigAlgList:list<sigAlg>):list<Sig.alg> =
    List.choose (fun alg -> let (sigA,_) = alg in if (List.exists (fun a -> a = sigA) sigAlgList) then Some(alg) else None) algList

let cert_type_to_SigHashAlg ct pv =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> default_sigHashAlg_fromSig pv SA_DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> default_sigHashAlg_fromSig pv SA_RSA

let rec cert_type_list_to_SigHashAlg ctl pv =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> (cert_type_to_SigHashAlg h pv) @ (cert_type_list_to_SigHashAlg t pv)

let cert_type_to_SigAlg ct =
    match ct with
    | TLSConstants.DSA_fixed_dh | TLSConstants.DSA_sign -> SA_DSA
    | TLSConstants.RSA_fixed_dh | TLSConstants.RSA_sign -> SA_RSA

let rec cert_type_list_to_SigAlg ctl =
    // FIXME: Generates a list with duplicates!
    match ctl with
    | [] -> []
    | h::t -> (cert_type_to_SigAlg h) :: (cert_type_list_to_SigAlg t)
