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
// Extensions may appear in the following messages
// The concrete message syntax
 type ext_msg =
   | EM_ClientHello
   | EM_ServerHello
   | EM_EncryptedExtensions
   | EM_Certificate
   | EM_NewSessionTicket
   | EM_HelloRetryRequest

(* As a static invariant, we record that any intermediate, parsed
extension and extension lists can be formatted into bytes without
overflowing 2^16. This create dependencies on the formatting
functions, at odd with recursive extensions. *)

let error s = Error (AD_decode_error, ("Extensions parsing: "^s))

//17-05-01 deprecated---use TLSError.result instead?
// SI: seems to be only used internally by parseServerName. Remove.
(** local, failed-to-parse exc. *)
private type canFail (a:Type) =
| ExFail of alertDescription * string
| ExOK of list a

(* PRE-SHARED KEYS AND KEY EXCHANGES *)
type pskIdentity = PSK.psk_identifier * PSK.obfuscated_ticket_age

val pskiBytes: PSK.psk_identifier * PSK.obfuscated_ticket_age -> bytes
let pskiBytes (i,ot) =
  lemma_repr_bytes_values (UInt32.v ot);
  (vlbytes2 i @| bytes_of_int 4 (UInt32.v ot))

val pskiListBytes: list pskIdentity -> bytes
let pskiListBytes ids =
  List.Tot.fold_left (fun acc pski -> acc @| pskiBytes pski) empty_bytes ids

noeq type psk =
  // this is the truncated PSK extension, without the list of binder tags.
  | ClientPSK:
    identities:list pskIdentity{
      let n = length (pskiListBytes identities) in 6 < n /\ n < 65536} ->
    binders_len:nat{binders_len <= 65535} ->
    psk
  // this is just an index in the client offer's PSK extension
  | ServerPSK: UInt16.t -> psk

// PSK binders, actually the truncated suffix of TLS 1.3 ClientHello
// We statically enforce length requirements to ensure that formatting is total.
type binder = b:bytes {32 <= length b /\ length b <= 255}

(** REMARK: this is more restrictive than in the RFC, which allows up to 2047 binders *)
type binders =
  bs:list binder {1 <= List.Tot.length bs /\ List.Tot.length bs < 255}

val binderListBytes: binders -> Pure (b:bytes)
  (requires True)
  (ensures fun b -> length b >= 33 /\ length b <= 65535)
let binderListBytes bs =
  let rec aux (bl:list binder) : Tot (b:bytes{length b <= op_Multiply (List.Tot.length bl) 256}) =
    match bl with
    | [] -> empty_bytes
    | b::t ->
      let bt = aux t in
      assert(length bt <= op_Multiply (List.Tot.length bl - 1) 256);
      let b0 = Parse.vlbytes1 b in
      assert(length b0 <= 256);
      b0 @| (aux t) in
  match bs with
  | h::t ->
    let b = aux t in
    let b0 = Parse.vlbytes1 h in
    assert(length b0 >= 33);
    b0 @| b

let bindersBytes (bs:binders): b:bytes{length b >= 35 /\ length b <= 65537} =
  let b = binderListBytes bs in
  Parse.vlbytes2 b

let parseBinderList (b:bytes{2 <= length b}) : result binders =
  let rec (aux: b:bytes -> list binder -> Tot (result (list binder)) (decreases (length b))) =
   fun b binders ->
    if length b > 0 then
      if length b >= 5 then
        match vlsplit 1 b with
        | Error z -> error "parseBinderList failed to parse a binder"
        | Correct (binder, bytes) ->
          if length binder < 32 then error "parseBinderList: binder too short"
          else (assume (length bytes < length b); aux bytes (binders @ [binder]))
      else error "parseBinderList: too few bytes"
    else Correct binders in
  if length b < 2 then
    error "pskBinderList not enough bytes to read length header"
  else
    match vlparse 2 b with
    | Correct b ->
      begin
      match aux b [] with
      | Correct bs ->
        let len = List.Tot.length bs in
        if 0 < len && len < 255 then
          Correct bs
        else
          error "none or too many binders"
      | Error z -> Error z
      end
    | Error z -> error "parseBinderList"

(** REMARK: we don't serialize the binders length; we do it when serializing Binders *)
val pskBytes: psk -> bytes
let pskBytes = function
  | ClientPSK ids len ->
    vlbytes2 (pskiListBytes ids)
  | ServerPSK sid ->
    lemma_repr_bytes_values (UInt16.v sid);
    bytes_of_int 2 (UInt16.v sid)

val parsePskIdentity: b:bytes -> result pskIdentity
let parsePskIdentity b =
  if length b < 2 then
    error "not enough bytes to parse the length of the identity field of PskIdentity"
  else
    match vlsplit 2 b with
    | Error z -> error "malformed PskIdentity"
    | Correct (id, ota) ->
      if length ota = 4 then
        let ota = uint32_of_bytes ota in
        lemma_repr_bytes_values (length id);
        Correct (id, ota)
      else error "malformed PskIdentity"

val parsePskIdentities: b:bytes{length b >= 2} -> result (list pskIdentity)
let parsePskIdentities b =
  let rec (aux: b:bytes -> list pskIdentity -> Tot (result (list pskIdentity)) (decreases (length b))) = fun b psks ->
    if length b > 0 then
      if length b >= 2 then
        match vlsplit 2 b with
        | Error z -> error "parsePskIdentities failed to parse id"
        | Correct (id,bytes) ->
          lemma_repr_bytes_values (length id);
          if length bytes >= 4 then
            let ot, bytes = split bytes 4 in
            match parsePskIdentity (vlbytes2 id @| ot) with
            | Correct pski -> aux bytes (psks @ [pski])
            | Error z -> Error z
          else error "parsePSKIdentities too few bytes"
      else error "parsePSKIdentities too few bytes"
    else Correct psks in
  match vlparse 2 b with
  | Correct b ->
    if length b >= 7 then aux b []
    else error "parsePskIdentities: too short"
  | Error z -> error "parsePskIdentities: failed to parse"

#set-options "--lax"
val client_psk_parse : bytes -> result (psk * option binders)
let client_psk_parse b =
  match vlsplit 2 b with
  | Error z -> error "client_psk_parse failed to parse"
  | Correct(ids,binders_bytes) -> (
    // SI: add ids header back.
    match parsePskIdentities (vlbytes2 ids) with
    | Correct ids -> (
    	match parseBinderList binders_bytes with
    	| Correct bl -> Correct (ClientPSK ids (length binders_bytes), Some bl)
    	| Error z -> error "client_psk_parse_binders")
    | Error z -> error "client_psk_parse_ids")

val server_psk_parse : bytes -> psk
let server_psk_parse b = ServerPSK (UInt16.uint_to_t (int_of_bytes b))

val parse_psk: ext_msg -> bytes -> result (psk * option binders)
let parse_psk mt b =
  match mt with
  | EM_ClientHello -> client_psk_parse b
  | EM_ServerHello -> Correct (server_psk_parse b, None)
  | _ -> error "PSK extension cannot appear in this message type"
#reset-options

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

#set-options "--lax"
let parse_client_psk_kexes: pinverse_t client_psk_kexes_bytes = fun b ->
  if equalBytes b (client_psk_kexes_bytes [PSK_KE]) then Correct [PSK_KE] else
  if equalBytes b (client_psk_kexes_bytes [PSK_DHE_KE]) then Correct [PSK_DHE_KE] else
  if equalBytes b (client_psk_kexes_bytes [PSK_KE; PSK_DHE_KE]) then Correct [PSK_KE; PSK_DHE_KE]  else
  if equalBytes b (client_psk_kexes_bytes [PSK_DHE_KE; PSK_KE]) then Correct [PSK_DHE_KE; PSK_KE]
  else error "PSK KEX payload"
  // redundants lists yield an immediate decoding error.
#reset-options

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

let rec ecpfListBytes_aux: list point_format -> bytes = function
  | [] -> empty_bytes
  | ECP_UNCOMPRESSED :: r -> abyte 0z @| ecpfListBytes_aux r
  | ECP_UNKNOWN t :: r -> bytes_of_int 1 t @| ecpfListBytes_aux r

val ecpfListBytes: l:list point_format{length (ecpfListBytes_aux l) < 256} -> Tot bytes
let ecpfListBytes l =
  let al = ecpfListBytes_aux l in
  lemma_repr_bytes_values (length al);
  let bl:bytes = vlbytes 1 al in
  bl

(* ALPN *)

let rec alpnBytes_aux: l:alpn -> Tot (b:bytes{length b <= op_Multiply 256 (List.Tot.length l)})
  = function
  | [] -> empty_bytes
  | protocol :: r ->
    lemma_repr_bytes_values (length protocol);
    vlbytes 1 protocol @| alpnBytes_aux r

let alpnBytes (a:alpn) : b:bytes{length b < 65536} =
  let r = alpnBytes_aux a in
  lemma_repr_bytes_values (length r);
  vlbytes 2 r

let rec parseAlpn_aux (al:alpn) (b:bytes) : Tot (result alpn) (decreases (length b)) =
  if length b = 0 then Correct(al)
  else
    if List.Tot.length al < 255 then
      match vlsplit 1 b with
      | Correct(cur, r) ->
        if length cur > 0 then
          begin
          List.Tot.append_length al [cur];
          parseAlpn_aux (al @ [cur]) r
          end
        else
          error "illegal empty protocol name in ALPN extension"
      | Error z -> Error z
    else error "too many entries in protocol_name_list in ALPN extension"

let parseAlpn : pinverse_t alpnBytes = fun b ->
  if length b >= 2 then
    match vlparse 2 b with
    | Correct l -> parseAlpn_aux [] l
    | Error(z) -> Error z
  else error "parseAlpn: extension is too short"

(* QUIC parameters *)

let quicVersionBytes (v:quicVersion) : Tot (lbytes 4) =
  bytes_of_uint32 (match v with
    | QuicVersion1 -> 1ul
    | QuicCustomVersion n -> n)

let rec quicVersionsBytes (vl:list quicVersion)
  : Tot (b:bytes{length b <= op_Multiply 4 (List.Tot.length vl)})
  (decreases (List.Tot.length vl))
  = match vl with
  | [] -> empty_bytes
  | h::t -> quicVersionBytes h @| (quicVersionsBytes t)

let quicParameterBytes : quicParameter -> b:bytes{length b < 256} = function
  | Quic_initial_max_stream_data n ->
    abyte2 (0z, 0z) @| vlbytes2 (bytes_of_uint32 n)
  | Quic_initial_max_data n ->
    abyte2 (0z, 1z) @| vlbytes2 (bytes_of_uint32 n)
  | Quic_initial_max_stream_id n ->
    abyte2 (0z, 2z) @| vlbytes2 (bytes_of_uint32 n)
  | Quic_idle_timeout n ->
    abyte2 (0z, 3z) @| vlbytes2 (bytes_of_uint16 n)
  | Quic_truncate_connection_id ->
    abyte2 (0z, 4z) @| vlbytes2 empty_bytes
  | Quic_max_packet_size n ->
    abyte2 (0z, 5z) @| vlbytes2 (bytes_of_uint16 n)
  | Quic_custom_parameter (n,b) ->
    bytes_of_uint16 n @| vlbytes2 b

let rec quicParametersBytes_aux (pl:list quicParameter)
  : Tot (b:bytes{length b <= op_Multiply (List.Tot.length pl) 256})
  (decreases (List.Tot.length pl))
  = match pl with
  | [] -> empty_bytes
  | p :: t -> quicParameterBytes p @| (quicParametersBytes_aux t)

let quicParametersBytes = function
  | QuicParametersClient nv iv p ->
    quicVersionBytes nv @| quicVersionBytes iv @|
    vlbytes2 (quicParametersBytes_aux p)
  | QuicParametersServer sv p ->
    vlbytes1 (quicVersionsBytes sv) @|
    vlbytes2 (quicParametersBytes_aux p)

let parseQuicVersion: pinverse_t quicVersionBytes = fun b ->
  if length b = 4 then
    let n = uint32_of_bytes b in
    if n = 1ul then Correct QuicVersion1
    else Correct (QuicCustomVersion n)
  else error "invalid QUIC version"

let parse_uint16 (b:bytes) : result UInt16.t =
  if length b = 2 then
    Correct (uint16_of_bytes b)
  else error "invalid uint16 encoding"

let parse_uint32 (b:bytes) : result UInt32.t =
  if length b = 4 then Correct (uint32_of_bytes b)
  else error "invalid uint32 encoding"

let rec parseQuicParameters_aux (b:bytes)
  : Tot (result (list quicParameter)) (decreases (length b))
  =
  if length b = 0 then Correct ([])
  else if length b < 4 then error "parseQuicParameters_aux: no headers"
  else
    let (pt, pv) = split b 2 in
    match vlsplit 2 pv with
    | Error z -> error "parseQuicParameters_aux: bad variable length encoding"
    | Correct (pv, rest) ->
      let param =
        match cbyte2 pt with
        | (0z, 0z) ->
          (match parse_uint32 pv with
          | Correct n -> Correct (Quic_initial_max_stream_data n)
          | _ -> error "bad initial_max_stream_data")
        | (0z, 1z) ->
          (match parse_uint32 pv with
          | Correct n -> Correct (Quic_initial_max_data n)
          | _ -> error "bad initial_max_data")
        | (0z, 2z) ->
          (match parse_uint32 pv with
          | Correct n -> Correct (Quic_initial_max_stream_id n)
          | _ -> error "initial_max_stream_id")
        | (0z, 3z) ->
          (match parse_uint16 pv with
          | Correct n -> Correct (Quic_idle_timeout n)
          | _ -> error "bad idle_timeout")
        | (0z, 4z) -> Correct Quic_truncate_connection_id
        | (0z, 5z) ->
          (match parse_uint16 pv with
          | Correct n -> Correct (Quic_max_packet_size n)
          | _ -> error "bad max_packet_size")
        | _ ->
          let pt = uint16_of_bytes pt in
          if length pv < 252 && UInt16.v pt > 5 then
            Correct (Quic_custom_parameter (pt, pv))
          else error "invalid unrecognized QUIC transport parameter"
        in
      // TODO tail recursive
      (match param, parseQuicParameters_aux rest with
      | Correct p, Correct tl -> Correct(p :: tl)
      | Error z, _
      | _, Error z -> Error z)

let rec parseQuicVersions (b:bytes)
  : Tot (result (list quicVersion)) (decreases (length b))
  =
  if length b = 0 then Correct []
  else if length b < 4 then error "bad version list"
  else
    let v, b = split b 4 in
    match parseQuicVersion v, parseQuicVersions b with
    | Error z, _ | _, Error z -> Error z
    | Correct v, Correct t -> Correct (v :: t)

let parseQuicParameters_valid (b:bytes) : Tot (result valid_quicParameters) =
  match parseQuicParameters_aux b with
  | Error z -> Error z
  | Correct qpl ->
    if not (List.Tot.existsb Quic_initial_max_stream_data? qpl) then
      error "parseQuicParameters: missing initial_max_stream_data"
    else if not (List.Tot.existsb Quic_initial_max_data? qpl) then
      error "parseQuicParameters: missing initial_max_data"
    else if not (List.Tot.existsb Quic_initial_max_stream_id? qpl) then
      error "parseQuicParameters: missing initial_max_stream_id"
    else if not (List.Tot.existsb Quic_idle_timeout? qpl) then
      error "parseQuicParameters: missing idle_timeout"
    else if List.Tot.length qpl >= 256 then // ADL FIXME: this should be ruled out statically
      error "parseQuicParameters: too many parameters"
    else Correct(qpl)

let parseQuicParameters (mt:ext_msg) (b:bytes) =
  match mt with
  | EM_ClientHello ->
    if length b < 38 then error "parseQuicParameters: too short"
    else
     begin
      let nv, b = split b 4 in
      let iv, b = split b 4 in
      match parseQuicVersion nv, parseQuicVersion iv with
      | Error z, _ | _, Error z -> Error z
      | Correct nv, Correct iv ->
        match vlparse 2 b with
        | Error z -> error "parseQuicParameters: bad client parameters"
        | Correct pb ->
          match parseQuicParameters_valid pb with
          | Error z -> Error z
          | Correct qpl -> Correct(QuicParametersClient nv iv qpl)
     end
  | EM_EncryptedExtensions ->
   begin
    if length b < 32 then error "parseQuicParameters: too short" else
    match vlsplit 1 b with
    | Error z -> error "parseQuicParameters: bad supported version list"
    | Correct(vlb, b) ->
      match parseQuicVersions vlb with
      | Error z -> Error z
      | Correct vl ->
        if vl = [] || List.Tot.length vl >= 64 then
          error "parseQuicParameters: bad supported version list"
        else if length b < 32 then
          error "parseQuicParameters: parameters too short"
        else match vlparse 2 b with
        | Error z -> error "parseQuicParameters: bad server parameters"
        | Correct pb ->
          match parseQuicParameters_valid pb with
          | Error z -> Error z
          | Correct qpl -> Correct(QuicParametersServer vl qpl)
   end
  | _ -> error "parseQuicParameters: extension appears in the wrong message type"

(* PROTOCOL VERSIONS *)

// The length exactly reflects the RFC format constraint <2..254>
type protocol_versions =
  l:list protocolVersion {0 < List.Tot.length l /\ List.Tot.length l < 128}

#set-options "--lax"
// SI: dead code?
val protocol_versions_bytes: protocol_versions -> b:bytes {length b <= 255}
let protocol_versions_bytes vs =
  vlbytes 1 (List.Tot.fold_left (fun acc v -> acc @| TLSConstants.versionBytes v) empty_bytes vs)
  // todo length bound; do we need an ad hoc variant of fold?
#reset-options

//17-05-01 added a refinement to control the list length; this function verifies.
//17-05-01 should we use generic code to parse such bounded lists?
//REMARK: This is not tail recursive, contrary to most of our parsing functions
val parseVersions:
  b:bytes ->
  Tot (result (l:list TLSConstants.protocolVersion {FStar.Mul.( length b == 2 * List.Tot.length l)})) (decreases (length b))
let rec parseVersions b =
  match length b with
  | 0 -> let r = [] in assert_norm (List.Tot.length r == 0); Correct r
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
          assert_norm (List.Tot.length (v::vs) == 1 + List.Tot.length vs);
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

private val parseServerName: r:ext_msg -> b:bytes -> Tot (result (list serverName))
let parseServerName mt b  =
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
    match mt with
    | EM_EncryptedExtensions
    | EM_ServerHello ->
      if length b = 0 then correct []
      else
      	let msg = "Failed to parse SNI list: should be empty in ServerHello, has size " ^ string_of_int (length b) in
      	Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ msg)
    | EM_ClientHello ->
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
    | _ -> error "SNI extension cannot appear in this message type"

// ExtensionType and Extension Table in https://tlswg.github.io/tls13-spec/#rfc.section.4.2.
// M=Mandatory, AF=mandatory for Application Features in https://tlswg.github.io/tls13-spec/#rfc.section.8.2.
noeq type extension' (p: (lbytes 2 -> GTot Type0)) =
  | E_server_name of list serverName (* M, AF *) (* RFC 6066 *)
  | E_supported_groups of list namedGroup (* M, AF *) (* RFC 7919 *)
  | E_signature_algorithms of signatureSchemeList (* M, AF *) (* RFC 5246 *)
  | E_key_share of CommonDH.keyShare (* M, AF *)
  | E_pre_shared_key of psk (* M, AF *)
  | E_session_ticket of bytes
  | E_early_data of earlyDataIndication
  | E_supported_versions of protocol_versions   (* M, AF *)
  | E_cookie of b:bytes {0 < length b /\ length b < 65536}  (* M *)
  | E_psk_key_exchange_modes of client_psk_kexes (* client-only; mandatory when proposing PSKs *)
  | E_extended_ms
  | E_ec_point_format of list point_format
  | E_alpn of alpn
  | E_quic_parameters of quicParameters
  | E_unknown_extension of ((x: lbytes 2 {p x}) * bytes) (* header, payload *)
(*
We do not yet support the extensions below (authenticated but ignored)
  | E_max_fragment_length
  | E_status_request
  | E_use_srtp
  | E_heartbeat
  | E_signed_certifcate_timestamp
  | E_client_certificate_type
  | E_server_certificate_type
  | E_certificate_authorities
  | E_oid_filters
  | E_post_handshake_auth
  | E_renegotiation_info of renegotiationInfo
*)

let bindersLen (#p: (lbytes 2 -> GTot Type0)) (el: list (extension' p)) : nat =
  match List.Tot.find E_pre_shared_key? el with
  | Some (Extensions.E_pre_shared_key (ClientPSK _ len)) -> 2 + len
  | _ -> 0

let string_of_extension (#p: (lbytes 2 -> GTot Type0)) (e: extension' p) = match e with
  | E_server_name _ -> "server_name"
  | E_supported_groups _ -> "supported_groups"
  | E_signature_algorithms _ -> "signature_algorithms"
  | E_key_share _ -> "key_share"
  | E_pre_shared_key _ -> "pre_shared_key"
  | E_session_ticket _ -> "session_ticket"
  | E_early_data _ -> "early_data"
  | E_supported_versions _ -> "supported_versions"
  | E_cookie _ -> "cookie"
  | E_psk_key_exchange_modes _ -> "psk_key_exchange_modes"
  | E_extended_ms -> "extended_master_secret"
  | E_ec_point_format _ -> "ec_point_formats"
  | E_alpn _ -> "alpn"
  | E_quic_parameters _ -> "quic_transport_parameters"
  | E_unknown_extension (n,_) -> print_bytes n

let rec string_of_extensions (#p: (lbytes 2 -> GTot Type0)) (l: list (extension' p)) = match l with
  | e0 :: es -> string_of_extension e0 ^ " " ^ string_of_extensions es
  | [] -> ""

(** shallow equality *)
let sameExt (#p: (lbytes 2 -> GTot Type0)) (e1: extension' p) (e2: extension' p) =
  let q : extension' p * extension' p = e1, e2 in
  match q with
  | E_server_name _, E_server_name _ -> true
  | E_supported_groups _, E_supported_groups _ -> true
  | E_signature_algorithms _, E_signature_algorithms _ -> true
  | E_key_share _, E_key_share _ -> true
  | E_pre_shared_key _, E_pre_shared_key _ -> true
  | E_session_ticket _, E_session_ticket _ -> true
  | E_early_data _, E_early_data _ -> true
  | E_supported_versions _, E_supported_versions _ -> true
  | E_cookie _, E_cookie _ -> true
  | E_psk_key_exchange_modes _, E_psk_key_exchange_modes _ -> true
  | E_extended_ms, E_extended_ms -> true
  | E_ec_point_format _, E_ec_point_format _ -> true
  | E_alpn _, E_alpn _ -> true
  | E_quic_parameters _, E_quic_parameters _ -> true
  // same, if the header is the same: mimics the general behaviour
  | E_unknown_extension(h1,_), E_unknown_extension(h2,_) -> equalBytes h1 h2
  | _ -> false

(*************************************************
 extension formatting
 *************************************************)

//17-05-05 no good reason to pattern match twice when formatting? follow the same structure as for parsing?
val extensionHeaderBytes: (#p: (lbytes 2 -> GTot Type0)) -> extension' p -> lbytes 2
let extensionHeaderBytes #p ext =
  match ext with             // 4.2 ExtensionType enum value
  | E_server_name _            -> abyte2 (0x00z, 0x00z)
  | E_supported_groups _       -> abyte2 (0x00z, 0x0Az) // 10
  | E_signature_algorithms _   -> abyte2 (0x00z, 0x0Dz) // 13
  | E_quic_parameters _        -> abyte2 (0x00z, 0x1Az) // 26
  | E_session_ticket _         -> abyte2 (0x00z, 0x23z) // 35
  | E_key_share _              -> abyte2 (0x00z, 0x28z) // 40
  | E_pre_shared_key _         -> abyte2 (0x00z, 0x29z) // 41
  | E_early_data _             -> abyte2 (0x00z, 0x2az) // 42
  | E_supported_versions _     -> abyte2 (0x00z, 0x2bz) // 43
  | E_cookie _                 -> abyte2 (0x00z, 0x2cz) // 44
  | E_psk_key_exchange_modes _ -> abyte2 (0x00z, 0x2dz) // 45
  | E_extended_ms              -> abyte2 (0x00z, 0x17z) // 45
  | E_ec_point_format _        -> abyte2 (0x00z, 0x0Bz) // 11
  | E_alpn _                   -> abyte2 (0x00z, 0x10z) // 16
  | E_unknown_extension (h,b)  -> h

// 17-05-19: We constrain unknown extensions to have headers different from known extensions.
let unknown_extensions_unknown
  (h: lbytes 2)
: GTot Type0
= forall (p: (lbytes 2 -> GTot Type0)) (e' : extension' p { equalBytes h (extensionHeaderBytes e') = true } ) . E_unknown_extension? e'

type extension = extension' unknown_extensions_unknown

val encryptedExtension: extension -> bool
let encryptedExtension ext =
  match ext with
  | E_server_name _
  | E_supported_groups _
  | E_alpn _
  | E_quic_parameters _
  | E_early_data _ -> true
  | _ -> false

private
let equal_extensionHeaderBytes_sameExt
  (e1 e2: extension)
: Lemma
  (requires (equalBytes (extensionHeaderBytes e1) (extensionHeaderBytes e2) = true))
  (ensures (sameExt e1 e2))
= assert (extensionHeaderBytes e1 == extensionHeaderBytes e2);
  match e1 with
  | E_unknown_extension _ -> assert (E_unknown_extension? e2)
  | _ -> ()

private
let sameExt_equal_extensionHeaderBytes
  (e1 e2: extension)
: Lemma
  (requires (sameExt e1 e2))
  (ensures (equalBytes (extensionHeaderBytes e1) (extensionHeaderBytes e2) = true))
= ()

(* API *)

// Missing refinements in `extension` type constructors to be able to prove the length bound
#set-options "--lax"
(** Serializes an extension payload *)
val extensionPayloadBytes: extension -> b:bytes { length b < 65536 - 4 }
let rec extensionPayloadBytes = function
  | E_server_name []           -> vlbytes 2 empty_bytes // ServerHello, EncryptedExtensions
  | E_server_name l            -> vlbytes 2 (vlbytes 2 (serverNameBytes l)) // ClientHello
  | E_supported_groups l       -> vlbytes 2 (namedGroupsBytes l)
  | E_signature_algorithms sha -> vlbytes 2 (signatureSchemeListBytes sha)
  | E_session_ticket b         -> vlbytes 2 b
  | E_key_share ks             -> vlbytes 2 (CommonDH.keyShareBytes ks)
  | E_pre_shared_key psk       ->
    (match psk with
    | ClientPSK ids len -> vlbytes_trunc 2 (pskBytes psk) (2 + len)
    | _ -> vlbytes 2 (pskBytes psk))
  | E_early_data edi           -> vlbytes 2 (earlyDataIndicationBytes edi)
  | E_supported_versions vv    ->
    // Sending TLS 1.3 draft versions, as other implementations are doing
    vlbytes 2
      (vlbytes 1
        (List.Tot.fold_left (fun acc v -> acc @| versionBytes_draft v) empty_bytes vv))
  | E_cookie c                 -> (lemma_repr_bytes_values (length c); vlbytes 2 (vlbytes 2 c))
  | E_psk_key_exchange_modes kex -> vlbytes 2 (client_psk_kexes_bytes kex)
  | E_extended_ms              -> vlbytes 2 empty_bytes
  | E_ec_point_format l        -> vlbytes 2 (ecpfListBytes l)
  | E_alpn l                   -> vlbytes 2 (alpnBytes l)
  | E_quic_parameters qp       -> vlbytes 2 (quicParametersBytes qp)
  | E_unknown_extension (_,b)  -> vlbytes 2 b
#reset-options

(** Serializes an extension *)
val extensionBytes: ext:extension -> b:bytes { 2 <= length b /\ length b < 65536 }
let rec extensionBytes ext =
  let head = extensionHeaderBytes ext in
  let payload = extensionPayloadBytes ext in
  lemma_repr_bytes_values (length payload);
  //let payload = vlbytes 2 payload in
  head @| payload

let extensionBytes_is_injective
  (ext1: extension)
  (s1: bytes)
  (ext2: extension)
  (s2: bytes)
: Lemma
  (requires (Seq.equal (extensionBytes ext1 @| s1) (extensionBytes ext2 @| s2)))
  (ensures (ext1 == ext2 /\ s1 == s2))
= let head1 = extensionHeaderBytes ext1 in
  let payload1 = extensionPayloadBytes ext1 in
  let head2 = extensionHeaderBytes ext2 in
  let payload2 = extensionPayloadBytes ext2 in
  append_assoc head1 payload1 s1;
  append_assoc head2 payload2 s2;
  lemma_append_inj head1 (payload1 @| s1) head2 (payload2 @| s2);
  equal_extensionHeaderBytes_sameExt ext1 ext2;
  match ext1 with
  | E_supported_groups l1 ->
    let (E_supported_groups l2) = ext2 in
    assume (List.Tot.length l1 < 65536/2 );
    let n1 = namedGroupsBytes l1 in
    assume (List.Tot.length l2 < 65536/2 );
    let n2 = namedGroupsBytes l2 in
    assume (repr_bytes (length n1) <= 2);
    assume (repr_bytes (length n2) <= 2);
    lemma_vlbytes_inj_strong 2 n1 s1 n2 s2;
    namedGroupsBytes_is_injective l1 empty_bytes l2 empty_bytes
  | E_signature_algorithms sha1 ->
    let (E_signature_algorithms sha2) = ext2 in
    let sg1 = signatureSchemeListBytes sha1 in
    let sg2 = signatureSchemeListBytes sha2 in
    assume (repr_bytes (length sg1) <= 2);
    assume (repr_bytes (length sg2) <= 2);
    lemma_vlbytes_inj_strong 2 sg1 s1 sg2 s2;
    signatureSchemeListBytes_is_injective sha1 empty_bytes sha2 empty_bytes
  | E_extended_ms ->
    lemma_repr_bytes_values (length empty_bytes);
    lemma_vlbytes_inj_strong 2 empty_bytes s1 empty_bytes s2
  | E_unknown_extension (h1, b1) ->
    let (E_unknown_extension (h2, b2)) = ext2 in
    assume (repr_bytes (length b1) <= 2);
    assume (repr_bytes (length b2) <= 2);
    lemma_vlbytes_inj_strong 2 b1 s1 b2 s2
  | _ ->
    assume (ext1 == ext2 /\ s1 == s2)

val extensionListBytes: exts: list extension -> bytes
let extensionListBytes exts =
  List.Tot.fold_left (fun l s -> l @| extensionBytes s) empty_bytes exts

private let rec extensionListBytes_eq exts accu :
  Lemma (List.Tot.fold_left (fun l s -> l @| extensionBytes s) accu exts ==
  accu @| extensionListBytes exts)
= match exts with
  | [] -> append_empty_bytes_r accu
  | s :: q ->
    let e = extensionBytes s in
    append_empty_bytes_l e;
    extensionListBytes_eq q (accu @| e);
    extensionListBytes_eq q e;
    append_assoc accu e (extensionListBytes q)

let extensionListBytes_cons
  (e: extension)
  (es: list extension)
: Lemma
  (extensionListBytes (e :: es) == extensionBytes e @| extensionListBytes es)
= let l = extensionBytes e in
  append_empty_bytes_l l;
  extensionListBytes_eq es l

let rec extensionListBytes_append
  (e1 e2: list extension)
: Lemma
  (extensionListBytes (e1 @ e2) == extensionListBytes e1 @| extensionListBytes e2)
= match e1 with
  | [] ->
    append_empty_bytes_l (extensionListBytes e2)
  | e :: q ->
    extensionListBytes_cons e (q @ e2);
    extensionListBytes_append q e2;
    append_assoc (extensionBytes e) (extensionListBytes q) (extensionListBytes e2);
    extensionListBytes_cons e q

let rec extensionListBytes_is_injective_same_length_in
  (exts1: list extension)
  (s1: bytes)
  (exts2: list extension)
  (s2: bytes)
: Lemma
  (requires (Seq.equal (extensionListBytes exts1 @| s1) (extensionListBytes exts2 @| s2) /\ List.Tot.length exts1 == List.Tot.length exts2))
  (ensures (exts1 == exts2 /\ s1 == s2))
= match exts1, exts2 with
  | [], [] ->
    lemma_append_inj empty_bytes s1 empty_bytes s2
  | ext1::q1, ext2::q2 ->
    let e1 = extensionBytes ext1 in
    let l1 = extensionListBytes q1 in
    extensionListBytes_cons ext1 q1;
    append_assoc e1 l1 s1;
    let e2 = extensionBytes ext2 in
    let l2 = extensionListBytes q2 in
    extensionListBytes_cons ext2 q2;
    append_assoc e2 l2 s2;
    extensionBytes_is_injective ext1 (l1 @| s1) ext2 (l2 @| s2);
    extensionListBytes_is_injective_same_length_in q1 s1 q2 s2

let rec extensionListBytes_is_injective_same_length_out
  (exts1: list extension)
  (s1: bytes)
  (exts2: list extension)
  (s2: bytes)
: Lemma
  (requires (
    let l1 = extensionListBytes exts1 in
    let l2 = extensionListBytes exts2 in (
    Seq.equal (l1 @| s1) (l2 @| s2) /\ length l1 == length l2
  )))
  (ensures (exts1 == exts2 /\ s1 == s2))
= match exts1 with
  | [] ->
    begin match exts2 with
    | [] -> lemma_append_inj empty_bytes s1 empty_bytes s2
    | e :: q -> extensionListBytes_cons e q
    end
  | ext1::q1 ->
    extensionListBytes_cons ext1 q1;
    let (ext2::q2) = exts2 in
    let e1 = extensionBytes ext1 in
    let l1 = extensionListBytes q1 in
    append_assoc e1 l1 s1;
    let e2 = extensionBytes ext2 in
    let l2 = extensionListBytes q2 in
    extensionListBytes_cons ext2 q2;
    append_assoc e2 l2 s2;
    extensionBytes_is_injective ext1 (l1 @| s1) ext2 (l2 @| s2);
    extensionListBytes_is_injective_same_length_out q1 s1 q2 s2

let rec extensionListBytes_is_injective
  (exts1: list extension)
  (exts2: list extension)
: Lemma
  (requires (Seq.equal (extensionListBytes exts1) (extensionListBytes exts2)))
  (ensures (exts1 == exts2))
= extensionListBytes_is_injective_same_length_out exts1 empty_bytes exts2 empty_bytes

let rec extensionListBytes_same_bindersLen
  (exts1: list extension)
  (s1: bytes)
  (exts2: list extension)
  (s2: bytes)
: Lemma
  (requires (
    let e1 = extensionListBytes exts1 in
    let e2 = extensionListBytes exts2 in (
    Seq.equal (e1 @| s1) (e2 @| s2) /\ length e1 + bindersLen exts1 == length e2 + bindersLen exts2
  )))
  (ensures (bindersLen exts1 == bindersLen exts2))
= match exts1, exts2 with
  | x1::q1, x2::q2 ->
    extensionListBytes_cons x1 q1;
    let ex1 = extensionBytes x1 in
    let eq1 = extensionListBytes q1 in
    append_assoc ex1 eq1 s1;
    extensionListBytes_cons x2 q2;
    let ex2 = extensionBytes x2 in
    let eq2 = extensionListBytes q2 in
    append_assoc ex2 eq2 s2;
    extensionBytes_is_injective x1 (eq1 @| s1) x2 (eq2 @| s2);
    if E_pre_shared_key? x1
    then ()
    else begin
      Seq.lemma_len_append ex1 eq1;
      Seq.lemma_len_append ex2 eq2;
      extensionListBytes_same_bindersLen q1 s1 q2 s2
    end
  | _ -> ()

let extensionListBytes_is_injective_strong
  (exts1: list extension)
  (s1: bytes)
  (exts2: list extension)
  (s2: bytes)
: Lemma
  (requires (
    let e1 = extensionListBytes exts1 in
    let e2 = extensionListBytes exts2 in (
    Seq.equal (e1 @| s1) (e2 @| s2) /\ length e1 + bindersLen exts1 == length e2 + bindersLen exts2
  )))
  (ensures (exts1 == exts2 /\ s1 == s2))
= extensionListBytes_same_bindersLen exts1 s1 exts2 s2;
  extensionListBytes_is_injective_same_length_out exts1 s1 exts2 s2

type extensions = exts:list extension {repr_bytes (length (extensionListBytes exts)) <= 2}

val noExtensions: exts:extensions {exts == []}
let noExtensions =
  lemma_repr_bytes_values (length (extensionListBytes []));
  []

(** Serializes a list of extensions.
  If there is a PreSharedKey client extension, then add the length of the PSK binders to
  the total length. Note that the `E_pre_shared_key` argument includes the length of
  binders in this case.
*)
val extensionsBytes:
  exts:extensions {length (extensionListBytes exts) + bindersLen exts < 65536} ->
  b:bytes { 2 <= length b /\ length b < 2 + 65536 }
let extensionsBytes exts =
  let b = extensionListBytes exts in
  let binder_len = bindersLen exts in
  lemma_repr_bytes_values (length b + binder_len);
  vlbytes_trunc 2 b binder_len

let extensionsBytes_is_injective_strong
  (exts1:extensions {length (extensionListBytes exts1) + bindersLen exts1 < 65536})
  (s1: bytes)
  (exts2:extensions {length (extensionListBytes exts2) + bindersLen exts2 < 65536})
  (s2: bytes)
: Lemma
  (requires (Seq.equal (extensionsBytes exts1 @| s1) (extensionsBytes exts2 @| s2)))
  (ensures (exts1 == exts2 /\ s1 == s2))
= let b1 = extensionListBytes exts1 in
  let binder_len1 = bindersLen exts1 in
  lemma_repr_bytes_values (length b1 + binder_len1);
  let b2 = extensionListBytes exts2 in
  let binder_len2 = bindersLen exts2 in
  lemma_repr_bytes_values (length b2 + binder_len2);
  vlbytes_trunc_injective 2 b1 binder_len1 s1 b2 binder_len2 s2;
  extensionListBytes_is_injective_strong exts1 s1 exts2 s2

let extensionsBytes_is_injective
  (ext1: extensions {length (extensionListBytes ext1) + bindersLen ext1 < 65536} )
  (ext2: extensions {length (extensionListBytes ext2) + bindersLen ext2 < 65536} )
: Lemma (requires True)
  (ensures (Seq.equal (extensionsBytes ext1) (extensionsBytes ext2) ==> ext1 == ext2))
= Classical.move_requires (extensionsBytes_is_injective_strong ext1 empty_bytes ext2) empty_bytes

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

val parseEcpfList: bytes -> result (list point_format)
let parseEcpfList b =
    let rec aux: (b:bytes -> Tot (result (list point_format)) (decreases (length b))) = fun b ->
        if equalBytes b empty_bytes then Correct []
        else if length b = 0 then error "malformed curve list"
        else
          let u,v = split b 1 in
          ( match aux v with
            | Error z -> Error z
            | Correct l ->
              let cur =
              match cbyte u with
              | 0z -> ECP_UNCOMPRESSED
              | _ -> ECP_UNKNOWN(int_of_bytes u) in
              Correct (cur :: l))
    in match aux b with
    | Error z -> Error z
    | Correct l ->
      if List.Tot.mem ECP_UNCOMPRESSED l
      then correct l
      else error "uncompressed point format not supported"

let parseKeyShare mt data =
  match mt with
  | EM_ClientHello -> CommonDH.(parseKeyShare KS_ClientHello data)
  | EM_ServerHello -> CommonDH.(parseKeyShare KS_ServerHello data)
  | EM_HelloRetryRequest -> CommonDH.(parseKeyShare KS_HRR data)
  | _ -> error "key_share extension cannot appear in this message type"

(* We don't care about duplicates, not formally excluded. *)
#set-options "--lax"

let normallyNone ctor r =
  (ctor r, None)

val parseExtension: ext_msg -> bytes -> result (extension * option binders)
let parseExtension mt b =
  if length b < 4 then error "extension type: not enough bytes" else
  let head, payload = split b 2 in
  match vlparse 2 payload with
  | Error (_,s) -> error ("extension: "^s)
  | Correct data -> (
    match cbyte2 head with
    | (0x00z, 0x00z) ->
//      mapResult E_server_name (parseServerName mt data)
      mapResult (normallyNone E_server_name) (parseServerName mt data)
    | (0x00z, 0x0Az) -> // supported groups
      if length data < 2 || length data >= 65538 then error "supported groups" else
      mapResult (normallyNone E_supported_groups) (Parse.parseNamedGroups data)

    | (0x00z, 0x0Dz) -> // sigAlgs
      if length data < 2 ||  length data >= 65538 then error "supported signature algorithms" else
      mapResult (normallyNone E_signature_algorithms) (TLSConstants.parseSignatureSchemeList data)

    | (0x00z, 0x10z) -> // application_layer_protocol_negotiation
      if length data < 2 ||  length data >= 65538 then error "application layer protocol negotiation" else
      mapResult (normallyNone E_alpn) (parseAlpn data)

    | (0x00z, 0x1Az) -> // quic_transport_parameters
      if length data < 2 || length data >= 65538 then error "quic transport parameters" else
      mapResult (normallyNone E_quic_parameters) (parseQuicParameters mt data)

    | (0x00z, 0x23z) -> // session_ticket
      Correct (E_session_ticket data, None)

    | (0x00z, 0x28z) ->
      mapResult (normallyNone E_key_share) (parseKeyShare mt data)

    | (0x00z, 0x29z) -> // PSK
      if length data < 2 then error "PSK"
      else (match parse_psk mt data with
      | Error z -> Error z
      | Correct (psk, None) -> Correct (E_pre_shared_key psk, None)
      | Correct (psk, Some binders) -> Correct (E_pre_shared_key psk, Some binders))

    | (0x00z, 0x2az) ->
      if length data <> 0 && length data <> 4 then error "early data indication" else
      mapResult (normallyNone E_early_data) (parseEarlyDataIndication data)

    | (0x00z, 0x2bz) ->
      if length data <= 2 || length data >= 256 then error "supported versions" else
      mapResult (normallyNone E_supported_versions) (parseSupportedVersions data)

    | (0xffz, 0x2cz) -> // cookie
      if length data <= 2 || length data >= 65538 then error "cookie" else
      Correct (E_cookie data,None)

    | (0x00z, 0x2dz) -> // key ex
      if length data < 2 then error "psk_key_exchange_modes" else
      mapResult (normallyNone E_psk_key_exchange_modes) (parse_client_psk_kexes data)

    | (0x00z, 0x17z) -> // extended ms
      if length data > 0 then error "extended master secret" else
      Correct (E_extended_ms,None)

    | (0x00z, 0x0Bz) -> // ec point format
      if length data < 1 || length data >= 256 then error "ec point format" else (
      lemma_repr_bytes_values (length data);
      match vlparse 1 data with
      | Error z -> Error z
      | Correct ecpfs -> mapResult (normallyNone E_ec_point_format) (parseEcpfList ecpfs))

    | _ -> Correct (E_unknown_extension (head,data), None))

//17-05-08 TODO precondition on bytes to prove length subtyping on the result
// SI: simplify binder accumulation code. (Binders should be the last in the list.)
val parseExtensions: ext_msg -> b:bytes -> result (extensions * option binders)
let parseExtensions mt b =
  let rec aux: b:bytes -> list extension * option binders
    -> Tot (result (list extension * option binders))
    (decreases (length b)) =
    fun b (exts, obinders) ->
    if length b >= 4 then
      let ht, b = split b 2 in
      match vlsplit 2 b with
      | Error(z) -> error "extension length"
      | Correct(ext, bytes) ->
      	(* assume (Prims.precedes (Prims.LexCons b) (Prims.LexCons (ht @| vlbytes 2 ext))); *)
      	(match parseExtension mt (ht @| vlbytes 2 ext) with
      	// SI:
      	| Correct (ext, Some binders) ->
      	  (match addOnce ext exts with // fails if the extension already is in the list
      	  | Correct exts -> aux bytes (exts, Some binders) // keep the binder we got
      	  | Error z -> Error z)
      	| Correct (ext, None) ->
      	  (match addOnce ext exts with // fails if the extension already is in the list
      	  | Correct exts -> aux bytes (exts, obinders)  // use binder-so-far.
      	  | Error z -> Error z)
      	| Error z -> Error z)
    else Correct (exts,obinders) in
  if length b < 2 then error "extensions" else
  match vlparse 2 b with
  | Correct b -> aux b ([], None)
  | Error z -> error "extensions"

(* SI: API. Called by HandshakeMessages. *)
// returns either Some,Some or None,
val parseOptExtensions: ext_msg -> data:bytes -> result (option (list extension) * option binders)
let parseOptExtensions mt data =
  if length data = 0
  then Correct (None,None)
  else (
    match parseExtensions mt data with
    | Error z -> Error z
    | Correct (ee,obinders) -> Correct (Some ee, obinders))
#reset-options

(*************************************************
 Other extension functionality
 *************************************************)

(* JK: Need to get rid of such functions *)
private let rec list_valid_cs_is_list_cs (l:valid_cipher_suites): list cipherSuite =
  match l with
  | [] -> []
  | hd :: tl -> hd :: list_valid_cs_is_list_cs tl

#set-options "--lax"
private let rec list_valid_ng_is_list_ng (l:list valid_namedGroup) : list namedGroup =
  match l with
  | [] -> []
  | hd :: tl -> hd :: list_valid_ng_is_list_ng tl
#reset-options

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
#set-options "--lax"
val prepareExtensions:
  protocolVersion ->
  protocolVersion ->
  k:valid_cipher_suites{List.Tot.length k < 256} ->
  option string -> // SNI
  option alpn -> // ALPN
  option quicParameters ->
  bool -> // EMS
  bool ->
  bool -> // EDI (Nego checks that PSK is compatible)
  option bytes -> // session_ticket
  signatureSchemeList ->
  list valid_namedGroup ->
  option (cVerifyData * sVerifyData) ->
  option CommonDH.keyShare ->
  list (PSK.pskid * PSK.pskInfo) ->
  l:list extension{List.Tot.length l < 256}
(* SI: implement this using prep combinators, of type exts->data->exts, per ext group.
   For instance, PSK, HS, etc extensions should all be done in one function each.
   This seems to make this prepareExtensions more modular. *)
let prepareExtensions minpv pv cs host alps qp ems sren edi ticket sigAlgs namedGroups ri ks psks =
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
    let res =
      match host with
      | Some dns -> E_server_name [SNI_DNS (utf8 dns)] :: res
      | None -> res
    in
    let res =
      match alps with
      | Some al -> E_alpn al :: res
      | None -> res
    in
    let res =
      match qp with
      | Some qp -> E_quic_parameters qp :: res
      | None -> res
    in
    let res =
      match ticket with
      | Some t -> E_session_ticket t :: res
      | None -> res
    in
    // Include extended_master_secret when resuming
    let res = if ems then E_extended_ms :: res else res in
    let res = E_signature_algorithms sigAlgs :: res in
    let res =
      if List.Tot.existsb isECDHECipherSuite (list_valid_cs_is_list_cs cs) then
	      E_ec_point_format [ECP_UNCOMPRESSED] :: res
      else res
    in
    let res =
      if List.Tot.existsb (fun cs -> isDHECipherSuite cs || CipherSuite13? cs) (list_valid_cs_is_list_cs cs) then
        E_supported_groups (list_valid_ng_is_list_ng namedGroups) :: res
      else res
    in
    let res =
      let filter = (fun (_,x) -> x.PSK.allow_psk_resumption || x.PSK.allow_dhe_resumption) in
      if pv = TLS_1p3 && List.Tot.filter filter psks <> [] then
        let (pskids, pskinfos) : list PSK.pskid * list PSK.pskInfo = List.Tot.split psks in
        let psk_kex = [] in
        let psk_kex =
          if List.Tot.existsb (fun x -> x.PSK.allow_psk_resumption) pskinfos
          then PSK_KE :: psk_kex else psk_kex in
        let psk_kex =
          if List.Tot.existsb (fun x -> x.PSK.allow_dhe_resumption) pskinfos
          then PSK_DHE_KE :: psk_kex else psk_kex in
        let res = E_psk_key_exchange_modes psk_kex :: res in
        let binder_len = List.Tot.fold_left (fun ctr pski ->
          let h = PSK.pskInfo_hash pski in
          ctr + 1 + Hashing.Spec.tagLen h) 0 pskinfos in
        let pskidentities = List.Tot.map (fun x -> x, PSK.default_obfuscated_age) pskids in
        let res =
          if edi then (E_early_data None) :: res
          else res in
        E_pre_shared_key (ClientPSK pskidentities binder_len) :: res // MUST BE LAST
      else res
    in
    let res = List.Tot.rev res in
    assume (List.Tot.length res < 256);  // JK: Specs in type config in TLSInfo unsufficient
    res
#reset-options

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


(* TODO (adl):
   The negotiation of renegotiation indication is incorrect,
   Needs to be consistent with clientToNegotiatedExtension
*)
#set-options "--lax"
private val serverToNegotiatedExtension:
  config ->
  list extension ->
  cipherSuite ->
  option (cVerifyData * sVerifyData) ->
  bool ->
  result unit ->
  extension ->
  result unit
let serverToNegotiatedExtension cfg cExtL cs ri resuming res sExt =
  match res with
  | Error z -> Error z
  | Correct l ->
    if not (List.Tot.existsb (sameExt sExt) cExtL) then
      Error(AD_unsupported_extension, perror __SOURCE_FILE__ __LINE__ "server sent an unexpected extension")
    else match sExt with
    (*
    | E_renegotiation_info sri ->
      if List.Tot.existsb E_renegotiation_info? cExtL then
      begin
      match sri, replace_subtyping ri with
      | FirstConnection, None -> correct ()
      | ServerRenegotiationInfo(cvds,svds), Some(cvdc, svdc) ->
        if equalBytes cvdc cvds && equalBytes svdc svds then
          correct l
        else
          Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Mismatch in contents of renegotiation indication")
      | _ -> Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Detected a renegotiation attack")
      end
      *)
    | E_server_name _ ->
      // RFC 6066, bottom of page 6
      //When resuming a session, the server MUST NOT include a server_name extension in the server hello
      if resuming then Error(AD_unsupported_extension, perror __SOURCE_FILE__ __LINE__ "server sent SNI acknowledge in resumption")
      else correct ()
    | E_session_ticket _ -> correct ()
    | E_alpn sal -> if List.Tot.length sal = 1 then correct ()
      else Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Multiple ALPN selected by server")
    | E_quic_parameters (QuicParametersServer qvl qp) -> correct ()
    | E_extended_ms -> correct ()
    | E_ec_point_format spf -> correct () // Can be sent in resumption, apparently (RFC 4492, 5.2)
    | E_key_share (CommonDH.ServerKeyShare sks) -> correct ()
    | E_supported_groups named_group_list ->
      if resuming then Error(AD_unsupported_extension, perror __SOURCE_FILE__ __LINE__ "server sent supported groups in resumption")
      else correct ()
    | e ->
      Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ ("unhandled server extension: "^(string_of_extension e)))

val negotiateClientExtensions:
  protocolVersion ->
  config ->
  option (list extension) ->
  option (list extension) ->
  cipherSuite ->
  option (cVerifyData * sVerifyData) ->
  bool ->
  result unit
let negotiateClientExtensions pv cfg cExtL sExtL cs ri resuming =
  match pv, cExtL, sExtL with
  | SSL_3p0, _, None ->
    Correct ()
  | SSL_3p0, _, Some _ ->
    Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Received extensions in SSL 3.0 ServerHello")
  | TLS_1p3, Some cExtL, Some sExtL ->
    (*
    match List.Tot.find E_psk_key_exchange_modes? cExtL,
          List.Tot.find E_pre_shared_key? sExtL
    with
    | None, None -> Correct ()
    | None, Some _ ->
      Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Received pre_shared_key extension but did not offer psk_key_exchange_modes")
    | Some kexs, Some (ServerPSK idx) ->
      match List.Tot.find E_pre_shared_key? cExtL with
      | None ->
        Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Sent psk_key_exchange_modes without pre_shared_key")
      | Some (ClientPSK ids _) ->
        if UInt16.v idx < List.Tot.length ids then Correct ()
        else
        Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Server sent an out of bounds PSK index")
    *)
    Correct ()
  | _, Some cExtL, Some sExtL ->
    begin
    match List.Tot.fold_left (serverToNegotiatedExtension cfg cExtL cs ri resuming) (correct ()) sExtL with
    | Error z -> Error z
    | Correct () -> correct ()
    end
  | _, _, None -> Correct ()
  | _, None, Some sExtL ->
    Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "negotiation failed: missing extensions in TLS ClientHello (shouldn't happen)")
#reset-options

private val clientToServerExtension: protocolVersion
  -> config
  -> cipherSuite
  -> option (cVerifyData * sVerifyData)
  -> option nat // PSK index
  -> option CommonDH.keyShare
  -> bool
  -> extension
  -> option extension
let clientToServerExtension pv cfg cs ri pski ks resuming cext =
  match cext with
  | E_key_share _ ->
    if pv = TLS_1p3 then Option.mapTot E_key_share ks // ks should be in one of client's groups
    else None
  | E_alpn cal ->
    (match cfg.alpn with
    | None -> None
    | Some sal ->
      let common = List.Tot.filter (fun x -> List.Tot.mem x sal) cal in
      match common with
      | a :: _ -> Some (E_alpn [a])
      | _ -> None)
  | E_quic_parameters (QuicParametersClient qv qvi qp) ->
    (match cfg.quic_parameters, pv with
    | Some (sqvl, sqp), TLS_1p3 ->
      // TODO client parameter validation?
      Some (E_quic_parameters (QuicParametersServer sqvl sqp))
    | _ -> None)
  | E_server_name server_name_list ->
    if resuming then None // RFC 6066 page 6
    else
      (match List.Tot.tryFind SNI_DNS? server_name_list with
      | Some name -> Some (E_server_name []) // Acknowledge client's choice
      | _ -> None)
  | E_extended_ms ->
    if pv = TLS_1p3 || not cfg.extended_master_secret then None
    else Some E_extended_ms
  | E_ec_point_format ec_point_format_list -> // REMARK: ignores client's list
    if pv = TLS_1p3 then None // No ec_point_format in TLS 1.3
    else Some (E_ec_point_format [ECP_UNCOMPRESSED])
  | E_pre_shared_key _ ->
    if pski = None || pv <> TLS_1p3 then None
    else
      let x = Some?.v pski in
      begin
        assume (x < 65536);
        Some (E_pre_shared_key (ServerPSK (UInt16.uint_to_t x)))
      end
  | E_supported_groups named_group_list ->
    if pv = TLS_1p3 then
      // REMARK: Purely informative, can only appear in EncryptedExtensions
      Some (E_supported_groups (list_valid_ng_is_list_ng cfg.named_groups))
    else None
  | E_early_data b -> // EE
    if cfg.enable_early_data && pski = Some 0 then Some (E_early_data None) else None
  | E_session_ticket b ->
     if pv = TLS_1p3 || not cfg.enable_tickets then None
     else Some (E_session_ticket empty_bytes) // TODO we may not always want to refresh the ticket
  | _ -> None

(* SI: API. Called by Handshake. *)
val negotiateServerExtensions: protocolVersion
   -> option (list extension)
   -> valid_cipher_suites
   -> config
   -> cipherSuite
   -> option (cVerifyData * sVerifyData)
   -> option nat
   -> option CommonDH.keyShare
   -> bool
   -> result (option (list extension))
let negotiateServerExtensions pv cExtL csl cfg cs ri pski ks resuming =
   match cExtL with
   | Some cExtL ->
     let sexts = List.Tot.choose (clientToServerExtension pv cfg cs ri pski ks resuming) cExtL in
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
