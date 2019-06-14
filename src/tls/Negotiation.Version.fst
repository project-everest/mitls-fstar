module Negotiation.Version

open Parsers.ProtocolVersion
open Parsers.ClientHelloExtension
open TLSConstants // for leqPV and the configuration

open FStar.Error
open TLSError

module HSM = HandshakeMessages
module CFG = Parsers.MiTLSConfig

#reset-options "--query_stats --using_facts_from '* -FStar.Reflection -FStar.Tactics -EverCrypt -Crypto -Spec -Hacl'" 

/// ---- PROTOCOL VERSIONS ----
///
/// The protocol version is negotiated in ClientHello and ServerHello,
/// using two overlapping mechanisms: the supportedVersion extension
/// of TLS 1.3 and the protocolVersion field of earlier versions.

// 19-01-04 possible code improvements: 
// * replace min/max_version in config with the payload of the supported_version extension.
// * refine TLSConstants.protocolVersion with implemented instead of not Unknown (this re-binding is confusing) 

/// We currently implement only TLS 1.2 and 1.3, and the negotiated
/// version can be further constrained in the connection initial
/// configuration.

// see also Negotiation.implemented_version 
let implemented pv = pv = TLS_1p2 || pv = TLS_1p3

let supported_new min_version max_version pv =
  implemented pv &&
  min_version `leqPV` pv && pv `leqPV` max_version

let supported cfg pv = supported_new cfg.min_version cfg.max_version pv

// hoisting negotiation failures; does these help with extraction or verification?
// private let illegal       #a msg: result a = fatal #a Illegal_parameter msg
// private let unsupported   #a msg: result a = fatal #a Unsupported_extension msg
// private let fatal_version #a msg: result a = fatal #a Protocol_version msg

/// (1) Client offers supported versions
///
/// We may provide more flexible configurations by replacing
/// min/max_version with a list of supported versions.

(* 
// an earlier variant, presumaly harder to lower and extract.
let offer_versions cfg: option clientHelloExtension =
  match cfg.min_version, cfg.max_version with
  | TLS_1p3, TLS_1p3 -> Some (CHE_supported_versions [TLS_1p3])
  | TLS_1p2, TLS_1p3 -> Some (CHE_supported_versions [TLS_1p3; TLS_1p2])
  | TLS_1p2, TLS_1p2 -> Some (CHE_supported_versions [TLS_1p2])
  | _                -> None
*)

// an auxiliary function; its first version was simpler, but led to timeouts below.
// let snoc_supportedVersion cfg pv pvs = 
//   if supported cfg pv then pvs @ [pv] else pvs 

// its tedious elaboration--complicating our spec
let snoc_supportedVersion
  min_version max_version
  (pv:Parsers.ProtocolVersion.protocolVersion) 
  (pvs:list Parsers.ProtocolVersion.protocolVersion): 
  (pvs1:list Parsers.ProtocolVersion.protocolVersion {List.length pvs1 <= List.length pvs + 1}) 
= 
  if supported_new min_version max_version pv then (
    List.lemma_snoc_length (pvs,pv);
    pvs @ [pv] ) 
  else pvs 

// 19-01-26 slow TC, due to constructor refinements? 
#push-options "--z3rlimit 100"
let support cfg: result clientHelloExtension =
  let vs = snoc_supportedVersion cfg.min_version cfg.max_version TLS_1p3 [] in 
  let vs = snoc_supportedVersion cfg.min_version cfg.max_version TLS_1p2 vs in 
  if List.isEmpty vs 
  then fatal Internal_error "configuration must include a supported protocol version"
  else Correct (CHE_supported_versions vs)

let support_new (cfg: CFG.miTLSConfig) : result clientHelloExtension =
  let min_version = Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.min_version in
  let max_version = Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.max_version in
  let vs = snoc_supportedVersion min_version max_version TLS_1p3 [] in 
  let vs = snoc_supportedVersion min_version max_version TLS_1p2 vs in
  if List.isEmpty vs 
  then fatal Internal_error "configuration must include a supported protocol version"
  else Correct (CHE_supported_versions vs)
#pop-options 

// sanity check
let mem_support (pv: Parsers.ProtocolVersion.protocolVersion) = function 
  | Correct (CHE_supported_versions xs) -> List.mem pv xs
  | _ -> false 
let supported_lemma cfg pv: Lemma (supported cfg pv <==> mem_support pv (support cfg)) = ()

/// implementation

open FStar.Integers 
open LowParse.Low.Base 
open Mem

// migrate to LowParse? 

let live_slice_pos h0 (#rrel #rel: _) (out: slice rrel rel) p0 = live_slice h0 out /\ p0 <= out.len 
type output = slice (srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _)) (srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _))

val write_supportedVersion 
  (min_version max_version: Parsers.ProtocolVersion.protocolVersion)
  (pv: Parsers.ProtocolVersion.protocolVersion) 
  (out: output)
  (pl p0: UInt32.t)
: Stack UInt32.t
  (requires fun h0 -> 
    valid_list protocolVersion_parser h0 out pl p0 /\
    v p0 + 2 <= v out.len
    //19-01-26 slower & causing a timeout below: [v out.len - v p0 >= 2]
    //19-01-26 much slower: [out.len - p0 >= 2ul]
    )
  (ensures fun h0 p1 h1 -> 
    valid_list protocolVersion_parser h1 out pl p1 /\
    v p0 <= v p1 /\
    v p1 - v p0 <= 2 /\ 
    LowStar.Buffer.modifies (loc_slice_from_to out p0 p1) h0 h1 /\
    contents_list protocolVersion_parser h1 out pl p1 == snoc_supportedVersion min_version max_version pv (contents_list protocolVersion_parser h0 out pl p0))

#push-options "--z3rlimit 100"
let write_supportedVersion min_version max_version pv out pl p0 =
  if supported_new min_version max_version pv then (
    let p1 = protocolVersion_writer pv out p0 in
    let h1 = get () in
    valid_list_snoc protocolVersion_parser h1 out pl p0;
    p1
  ) else p0

val write_supportedVersions
  (cfg:config) 
  (out:output)
  (p0:UInt32.t)
: Stack (result UInt32.t) 
  (requires fun h0 -> live_slice_pos h0 out p0) 
  (ensures fun h0 r h1 -> 
    LowStar.Modifies.(modifies (loc_slice_from out p0) h0 h1) /\ (
    match r with 
    | Error z -> True
    | Correct p1 -> 
      match support cfg with 
      | Error _ -> False 
      | Correct che -> valid_content_pos clientHelloExtension_parser h1 out p0 che p1 ))
#pop-options 

let write_supportedVersions cfg out p0 =
  if out.len - p0 < 10ul then fatal Internal_error "output buffer" else
  let pl_extension = p0 + 2ul in // extension payload, after the extension tag
  let pl_CHE_supported_versions = pl_extension + 2ul in // CHE_supported_versions payload, after the CHE_supported_versions length
  let pl_supported_versions = pl_CHE_supported_versions + 1ul in // supported_versions payload, after the supported_versions list length
  let h = get () in
  valid_list_nil protocolVersion_parser h out pl_supported_versions; 
  let pl = write_supportedVersion cfg.min_version cfg.max_version TLS_1p3 out pl_supported_versions pl_supported_versions in 
  let pl = write_supportedVersion cfg.min_version cfg.max_version TLS_1p2 out pl_supported_versions pl in
  if pl = pl_supported_versions then fatal Internal_error "configuration must include a supported protocol version" else 
    let h = get () in
    valid_list_cons_recip protocolVersion_parser h out pl_supported_versions pl;
    Extensions.finalize_supportedVersions out pl_CHE_supported_versions pl;
    Extensions.clientHelloExtension_CHE_supported_versions_finalize out pl_extension pl;
    Extensions.finalize_clientHelloExtension_supported_versions out p0;
    Correct pl
// this kind of code is hard to get right, as the programmer needs to
// know every detail of the wire format, including its byte offsets
// and explicit proof steps---every error takes 10' 

(* another attempt based on higher-order low-level writing combinators *)

module LPW = LowParse.Low.Writers

(* step 1: produce all elementary combinators for lists, vldata, constructors and so on. Ideally these should be provided by QuackyDucky, but that requires cross-module inlining. *)

module HST = FStar.HyperStack.ST

let omake_supportedVersions
  (l: option (list Parsers.ProtocolVersion.protocolVersion))
: Tot (option Extensions.supportedVersions)
= match l with
  | None -> None
  | Some l ->
    let len = List.Tot.length l in
    if 1 <= len && len <= 127
    then Some l
    else None

inline_for_extraction
noextract
let owrite_supportedVersions
  #h0
  #sout
  #sout_from0
  (w: LPW.olwriter protocolVersion_serializer h0 sout sout_from0)
: Tot (w' : LPW.owriter Extensions.supportedVersions_serializer h0 sout sout_from0 {
    LPW.owvalue w' == omake_supportedVersions (LPW.olwvalue w)
  })
= LPW.OWriter (Ghost.hide (omake_supportedVersions (LPW.olwvalue w))) (fun sout_from ->
    Classical.forall_intro Extensions.supportedVersions_bytesize_eq;
    Classical.forall_intro (LPW.serialized_length_eq Extensions.supportedVersions_serializer);
    Classical.forall_intro (LPW.serialized_list_length_constant_size Extensions.protocolVersion_serializer);
    if 1ul `UInt32.gt` (sout.LPW.len `UInt32.sub` sout_from)
    then begin
      LPW.max_uint32
    end else begin
      let res = LPW.olwrite w (sout_from `UInt32.add` 1ul) in
      if res `UInt32.gte` (LPW.max_uint32 `UInt32.sub` 1ul)
      then begin
        res
      end else begin
        let h = HST.get () in
        LPW.valid_list_serialized_list_length Extensions.protocolVersion_serializer h sout (sout_from `UInt32.add` 1ul) res;
        let len = res `UInt32.sub` (sout_from `UInt32.add` 1ul) in
        if not (2ul `UInt32.lte` len && len `UInt32.lte` 254ul)
        then
          LPW.max_uint32 `UInt32.sub` 1ul
        else begin
          Extensions.finalize_supportedVersions sout sout_from res;
          res
        end
      end
    end
  )

inline_for_extraction
noextract
let owrite_clientHelloExtension_CHE_supported_versions
  #h0
  #sout
  #sout_from0
  (w: LPW.owriter Extensions.supportedVersions_serializer h0 sout sout_from0)
: Tot (w' : LPW.owriter clientHelloExtension_CHE_supported_versions_serializer h0 sout sout_from0 {
    LPW.owvalue w' == LPW.owvalue w
  })
= LPW.OWriter (Ghost.hide (LPW.owvalue w)) (fun sout_from ->
    Classical.forall_intro Extensions.supportedVersions_bytesize_eq;
    Classical.forall_intro (LPW.serialized_length_eq Extensions.supportedVersions_serializer);
    Classical.forall_intro clientHelloExtension_CHE_supported_versions_bytesize_eq;
    Classical.forall_intro (LPW.serialized_length_eq clientHelloExtension_CHE_supported_versions_serializer);
    if 2ul `UInt32.gt` (sout.LPW.len `UInt32.sub` sout_from)
    then LPW.max_uint32
    else
      let res = LPW.owrite w (sout_from `UInt32.add` 2ul) in
      if res `UInt32.gte` (LPW.max_uint32 `UInt32.sub` 1ul)
      then res
      else begin
        clientHelloExtension_CHE_supported_versions_finalize sout sout_from res;
        res
      end
  )

let omake_CHE_supported_versions (x: option clientHelloExtension_CHE_supported_versions) : Tot (option clientHelloExtension) =
  match x with
  | None -> None
  | Some y -> Some (CHE_supported_versions y)

inline_for_extraction
noextract
let owrite_constr_clientHelloExtension_CHE_supported_versions
  #h0
  #sout
  #sout_from0
  (w: LPW.owriter clientHelloExtension_CHE_supported_versions_serializer h0 sout sout_from0)
: Tot (w' : LPW.owriter clientHelloExtension_serializer h0 sout sout_from0 {
    LPW.owvalue w' == omake_CHE_supported_versions (LPW.owvalue w)
  })
= LPW.OWriter (Ghost.hide (omake_CHE_supported_versions (LPW.owvalue w))) (fun sout_from ->
    Classical.forall_intro clientHelloExtension_CHE_supported_versions_bytesize_eq;
    Classical.forall_intro (LPW.serialized_length_eq clientHelloExtension_CHE_supported_versions_serializer);
    Classical.forall_intro clientHelloExtension_bytesize_eq;
    Classical.forall_intro (LPW.serialized_length_eq clientHelloExtension_serializer);
    if 2ul `UInt32.gt` (sout.LPW.len `UInt32.sub` sout_from)
    then LPW.max_uint32
    else
      let res = LPW.owrite w (sout_from `UInt32.add` 2ul) in
      if res `UInt32.gte` (LPW.max_uint32 `UInt32.sub` 1ul)
      then res
      else begin
        finalize_clientHelloExtension_supported_versions sout sout_from;
        res
      end
  )

(* step 2: assemble those combinators to actually implement "support" as a writer *)

inline_for_extraction
noextract
let write_snoc_supportedVersion
  min_version max_version
  #h0
  #sout
  #sout_from0
  (pv: Parsers.ProtocolVersion.protocolVersion)
  (pvs: LPW.lwriter protocolVersion_serializer h0 sout sout_from0)
: Tot (pvs1 : LPW.lwriter protocolVersion_serializer h0 sout sout_from0 {
    LPW.lwvalue pvs1 == snoc_supportedVersion min_version max_version pv (LPW.lwvalue pvs)
  })
= LPW.lwriter_ifthenelse
    (supported_new min_version max_version pv)
    (fun _ -> LPW.lwriter_append pvs (LPW.lwriter_singleton (LPW.write_leaf_cs protocolVersion_writer _ _ _ pv)))
    (fun _ -> pvs)

module HS = FStar.HyperStack
module B = LowStar.Monotonic.Buffer

inline_for_extraction
noextract
let write_supportedVersions_new
  #scfg_rrel #scfg_rel
  (scfg: LPW.slice scfg_rrel scfg_rel)
  (scfg_pos: UInt32.t)
  sout
  sout_from0
  (h0: HS.mem {
    LPW.valid CFG.miTLSConfig_parser h0 scfg scfg_pos /\
    B.loc_disjoint (LPW.loc_slice_from_to scfg scfg_pos (LPW.get_valid_pos CFG.miTLSConfig_parser h0 scfg scfg_pos)) (LPW.loc_slice_from sout sout_from0)    
  })
: Tot (e: LPW.owriter clientHelloExtension_serializer h0 sout sout_from0 {
      LPW.owvalue e == option_of_result (support_new (LPW.contents CFG.miTLSConfig_parser h0 scfg scfg_pos))
  })
= LPW.graccess CFG.accessor_miTLSConfig_min_version scfg scfg_pos _ _ _ `LPW.owbind` (fun pmin ->
  LPW.graccess CFG.accessor_miTLSConfig_max_version scfg scfg_pos _ _ _ `LPW.owbind` (fun pmax ->
  LPW.read_leaf protocolVersion_reader scfg pmin _ _ _ `LPW.owbind` (fun min_version ->
  LPW.read_leaf protocolVersion_reader scfg pmax _ _ _ `LPW.owbind` (fun max_version ->
  owrite_constr_clientHelloExtension_CHE_supported_versions
    (owrite_clientHelloExtension_CHE_supported_versions
      (owrite_supportedVersions
        (LPW.olwriter_of_lwriter
          ([@inline_let]
            let w =
              write_snoc_supportedVersion min_version max_version TLS_1p3 (LPW.lwriter_nil protocolVersion_serializer h0 sout sout_from0)
            in
            write_snoc_supportedVersion min_version max_version TLS_1p2 w
  )))))
  )))

let test_write_supportedVersions_new
  #scfg_rrel #scfg_rel
  (scfg: LPW.slice scfg_rrel scfg_rel)
  (scfg_pos: UInt32.t)
  (sout: LPW.slice (LPW.srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _)) (LPW.srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _)))
  (sout_from: UInt32.t)
: HST.Stack UInt32.t
  (requires (fun _ -> False))
  (ensures (fun _ _ _ -> True))
= let h = HST.get () in
  LPW.owrite (write_supportedVersions_new scfg scfg_pos sout sout_from h) sout_from


/// (2) Server chooses a supported version
///
/// Check that the protocol version in ClientHello is within the
/// range of versions supported by the server configuration and
/// outputs the negotiated version if true

module CH = Parsers.ClientHello

type ch = CH.clientHello
let offered_version o = o.CH.version 
let offered_extensions o = o.CH.extensions 

/// We ignore the "minimal protocol version" signalled in the packet
/// header; this is fine since our server never accepts any proposal
/// below the "maximal protocol version".

// does it help? 
private let correct #a (x:a): result a = Correct x

// used only for tracing
let offered_versions ch = 
  match List.Tot.find CHE_supported_versions? (offered_extensions ch) with
  | None -> [offered_version ch] 
  | Some (CHE_supported_versions vs) -> vs
  

val choose: cfg:config -> ch -> result (pv:protocolVersion{ supported cfg pv })
let choose cfg ch =
  let legacy_max_pv = offered_version ch in 
  if TLS_1p3 `leqPV` legacy_max_pv then
    fatal Protocol_version "Client offered an invalid legacy protocol version "
  else
    match List.Tot.find CHE_supported_versions? (offered_extensions ch) with
    | None ->
      // legacy negotiation: we pick at most TLS 1p2
      if legacy_max_pv = TLS_1p2 && supported cfg TLS_1p2 then
        correct TLS_1p2
      else
        fatal Protocol_version "Client offered an unsupported protocol version"

    | Some (CHE_supported_versions vs) ->
      // new extension-based negotiation: we pick the first client offer supported by the server
      match List.Helpers.find_aux cfg supported vs with
      | Some v -> correct v
      | None -> fatal Protocol_version "Client offered no supported protocol version"

(*
// 19-01-26 TODO lowering this function requires two iterators on the
// received sequence of client-supported extensions. (Not sure how to
// write them parametrically, since they need to be parameterized by
// accessors, readers, and jumpers.) Use supportedVersions_nth instead?  

let rec find_supportedVersions parser jumper reader filter input p pmax =
  if p = pmax then None else 
    let v = reader input p in 
    if filter v then Some v else
      let p = jumper parser input p in 
      find_supportedVersions parser jumper reader filter input p max  

val choose_low:
  cfg:config -> 
  input:slice -> pch:UInt32.t -> Stack (result protocolVersion) 
  (requires fun h0 -> 
    valid Parsers.ClientHello.clientHello_parser h0 input pch) 
  (ensures fun h0 r h1 -> r = 
    let ch = contents Parsers.ClientHello.clientHello_parser h0 input p in 
    LowStar.Modifies.(modifies loc_none h0 h1) /\ 
    r == choose cfg ch)

let choose_low cfg input pch = 
  let ppv = accessor_clientHello_version input pch in 
  let legacy_max_pv = protocolVersion_reader input ppv in 
  if TLS_1p3 `leqPV` legacy_max_pv then
    fatal Protocol_version "protocol version negotiation: bad legacy proposal"
  else
    let pches = accessor_clientHello_extensions input in 
    match LowParse.find_list CHE_supported_versions? input pches with
    | None ->
      // legacy negotiation: we pick at most TLS 1p2
      if legacy_max_pv = TLS_1p2 && supported cfg TLS_1p2 then
        correct TLS_1p2
      else
        fatal Protocol_version "protocol version negotiation: mismatch"

    | Some (p_supported_versions) ->
      // new extension-based negotiation: we pick the first client offer supported by the server
      match LowParse.find_list_aux cfg supported input p_supported_versions with
      | Some v -> correct v
      | None -> fatal Protocol_version "protocol version negotiation: mismatch"  
*)


/// (3) Client validates the server's choice

(**
  Determines if the server random value contains a downgrade flag
  AND if there has been a downgrade
  The downgrade flag is a random value set by RFC (6.3.1.1)
*)
val isSentinelRandomValue:
  Parsers.ProtocolVersion.protocolVersion ->
  Parsers.ProtocolVersion.protocolVersion ->
  TLSInfo.random ->
  bool
let isSentinelRandomValue client_pv server_pv server_random =
  let open FStar.Bytes in
  let down = bytes_of_string "DOWNGRD" in
  assume(length down = 7 /\ length (abyte 1z) = 1 /\ length (abyte 0z) = 1); //18-12-16 TODO how?
  (server_pv `leqPV` TLS_1p2 && TLS_1p3 `leqPV` client_pv && server_random = down @| abyte 1z) ||
  (server_pv `leqPV` TLS_1p1 && TLS_1p2 `leqPV` client_pv && server_random = down @| abyte 0z)
// TODO do we produce them? do we get downgrade resistance from them?

module SH = Parsers.RealServerHello

/// ServerHello sets the protocol version
let chosen sh =
  let pv0 = sh.SH.version in 
  if TLS_1p3 `leqPV` pv0 then
    fatal Illegal_parameter "Server selected an illegal legacy protocol version"
  else
    let open Parsers.ServerHelloExtension in
    match List.Tot.find SHE_supported_versions? sh.SH.extensions with
      | None -> correct pv0 // old style
      | Some (SHE_supported_versions pv1) ->
        if TLS_1p3 `leqPV` pv1 && pv0 <> TLS_1p2 then 
        fatal Illegal_parameter "Extension-based version negotiation requires TLS 1.2 legacy protocol version"
        else correct pv1 

/// The client checks it is compatible with its offer
val accept:
  cfg: config ->
  sh: HSM.sh ->
//pv: protocolVersion ->
//ses: Parsers.ServerHelloExtensions.serverHelloExtensions ->
//sr: TLSInfo.random ->
  result (pv: Parsers.ProtocolVersion.protocolVersion{ chosen sh = Correct pv /\ supported cfg pv })

let accept cfg sh (*pv ses sr*) =
  match chosen sh with
  | Error z -> Error z 
  | Correct pv -> 
    if isSentinelRandomValue cfg.max_version pv sh.SH.random then 
      fatal Illegal_parameter "Protocol-version downgrade attempt detected"
    else 
    if not (supported cfg pv) then 
      fatal Illegal_parameter "Client did not offer the selected protocol version"
    else
      correct pv

//19-04-19 TODO lower reader for accept 

(* experiment beyond version --- to be discarded

/// ----
///
/// server's handling of ClientHello, a rather long stateful function.
/// calling (pure) computeServerMode, then the application callback. 
///
 
let find_client_extension (filter:clientHelloExtension -> bool) o
  : option (e:clientHelloExtension{filter e}) =
  List.Tot.find filter o.Parsers.ClientHello.extensions 

let find_client_key_shares (o:offer): Parsers.KeyShareClientHello.keyShareClientHello =
  match find_client_extension CHE_key_share? o with
  | Some (CHE_key_share x) -> x
  | _ -> assume(Parsers.KeyShareClientHello.keyShareClientHello_list_bytesize [] = 0); []
//TODO 19-01-04 where to get it from? 

let group_of_hrr hrr : option CommonDH.group = None
//19-01-03 TODO where are QD's HRR extensions? 
(*
  match List.Tot.find (Extensions.E_key_share?) hrr.hrr_extensions with
  | Some (Extensions.E_key_share (CommonDH.HRRKeyShare ng)) ->
    CommonDH.group_of_namedGroup ng
  | _ -> None
*)

private
let sameExtensionTag e0 e1 = tag_of_clientHelloExtension e0 = tag_of_clientHelloExtension e1 

private
let retry_extension_ok (o1, hrr) (e:clientHelloExtension) = 
  match e with
// 19-01-04 TODO   
// | Case_key_share shares2 -> (
//     match shares2, group_of_hrr hrr with
//     | [CommonDH.Share g _], Some g' -> g = g'
//     | _, None ->
//         let shares1 = find_client_key_shares o1 in
//         //TODO 19-01-03 easier on the underlying wire representation
//         Parsers.KeyShareClientHello.keyShareClientHello_serializer32 shares1 =
//         Parsers.KeyShareClientHello.keyShareClientHello_serializer32 shares2
//         // CommonDH.clientKeyShareBytes shares1 = CommonDH.clientKeyShareBytes shares2
//     | _ -> false)
  | CHE_early_data _ -> false // Forbidden
  | CHE_cookie c -> true // FIXME we will send cookie
      // If we add cookie support we need to treat this case separately
      // | Extensions.E_cookie c -> c = S_HRR?.cookie ns.state
  | e ->
        (match List.Helpers.find_aux e sameExtensionTag o1 with
        | None -> (IO.debug_print_string "Extra extension\n") && false
        // This allows the client to send less extensions,
        // but the ones that are sent must be exactly the same
        | Some e' ->
          //FIXME: Extensions.E_pre_shared_key "may be updated" 4.1.2
          true) // FIXME
          //(extensionBytes e) = (extensionBytes e'))

// check the second offer is compatible with the first (see RFC)
let retry_offer_ok o1 hrr o2 = 
  let open Parsers.ClientHello in 
  o1.version = o2.version &&
  o1.random = o2.random &&
  o1.session_id = o2.session_id &&
// TODO 19-01-04 
//  o1.session_id = hrr.hrr_sessionID &&
//  List.Tot.mem hrr.hrr_cipher_suite o2.ch_cipher_suites &&
  o1.compression_method = o2.compression_method &&
  List.Helpers.forall_aux (o1.extensions, hrr) retry_extension_ok o2.extensions


(*
// typeckecks but yields unsafe C.
let small (a:option (list bool)) = None? a || List.length (Some?.v a) < 10

// uglier, yields good C, possible recommended style in Low*
let small2 (a:option (list bool)) = 
  if None? a then true else List.length (Some?.v a) < 10

// we miss an early inlining semantics to get both with [let ( || ) = if a then true else b]
*)

(*
open Mem 

val server_ClientHello: // #region:rgn -> t region Server ->
  offer -> // log:HandshakeLog.t ->
  St (result serverMode)
#set-options "--admit_smt_queries true"
let server_ClientHello #region ns offer log =
  trace ("offered client extensions "^string_of_option_extensions offer.ch_extensions);
  trace ("offered cipher suites "^(string_of_ciphersuitenames offer.ch_cipher_suites));
  trace (match (offered_versions TLS_1p0 offer) with
        | Error z -> "Error: "^string_of_error z
        | Correct v -> List.Tot.fold_left accum_string_of_pv "offered versions" v);
  match !ns.state with
  | S_HRR o1 hrr ->
    trace ("Processing second offer based on existing HRR state (stateful HRR).");
    if retry_offer_ok o1 offer
    then
      let sm = computeServerMode ns.cfg offer ns.nonce in
      match sm with
      | Error z ->
        trace ("negotiation failed: "^string_of_error z);
        Error z
      | Correct (ServerHelloRetryRequest hrr _) ->
        fatal Illegal_parameter "client sent the same hello in response to hello retry"
      | Correct (ServerMode m cert _) ->
        trace ("negotiated after HRR "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
        let nego_cb = ns.cfg.nego_callback in
        let exts_bytes = Extensions.app_extensions_bytes offer.ch_extensions in
        trace ("Negotiation callback to handle extra extensions.");
        match nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes (Some empty_bytes) with
        | Nego_accept sexts ->
          let el = Extensions.ext_of_custom sexts in
          ns.state := S_ClientHello m cert;
          Correct (ServerMode m cert el)
        | _ ->
          trace ("Application requested to abort the handshake after internal HRR.");
          fatal Handshake_failure "application aborted the handshake by callback"
    else
      fatal Illegal_parameter "Inconsistant parameters between first and second client hello"

  | S_Init _ ->
    let sm = computeServerMode ns.cfg offer ns.nonce in
    let previous_cookie = // for stateless HRR
      match find_cookie offer with
      | None -> None
      | Some c ->
        match Ticket.check_cookie c with
        | None -> trace ("WARNING: ignorning invalid cookie "^(hex_of_bytes c)); None
        | Some (hrr, digest, extra) ->
          trace ("Loaded stateless retry cookie "^(hex_of_bytes c));
          let hrr = { hrr with hrr_extensions =
            (Extensions.E_cookie c) :: hrr.hrr_extensions; } in
          // Overwrite the current transcript digest with values from cookie
          trace ("Overwriting the transcript digest with CH1 hash "^(hex_of_bytes digest));
          HandshakeLog.load_stateless_cookie log hrr digest;
          Some extra // for the server nego callback
      in
    match sm with
    | Error z ->
      trace ("negotiation failed: "^string_of_error z);
      Error z
    | Correct (ServerHelloRetryRequest hrr cs) ->
      // Internal HRR caused by group negotiation
      // We do not invoke the server nego callback in this case
      // record the initial offer and return the HRR to HS
      let ha = verifyDataHashAlg_of_ciphersuite cs in
      let digest = HandshakeLog.hash_tag #ha log in
      let cookie = Ticket.create_cookie hrr digest empty_bytes in
      let hrr = { hrr with hrr_extensions =
        (Extensions.E_cookie cookie) :: hrr.hrr_extensions; } in
      ns.state := S_HRR offer hrr;
      sm
    | Correct (ServerMode m cert _) ->
      let nego_cb = ns.cfg.nego_callback in
      let exts_bytes = Extensions.app_extensions_bytes offer.ch_extensions in
      trace ("Negotiation callback to handle extra extensions and query for stateless retry.");
      trace ("Application data in cookie: "^(match previous_cookie with | Some c -> hex_of_bytes c | _ -> "none"));
      match nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes previous_cookie with
      | Nego_abort ->
        trace ("Application requested to abort the handshake.");
        fatal Handshake_failure "application aborted the handshake by callback"
      | Nego_retry cextra ->
        let hrr = ({
          hrr_sessionID = offer.ch_sessionID;
          hrr_cipher_suite = name_of_cipherSuite m.n_cipher_suite;
          hrr_extensions = [
            Extensions.E_supported_versions (Extensions.ServerPV TLS_1p3);
          ]}) in
        let ha = verifyDataHashAlg_of_ciphersuite m.n_cipher_suite in
        let digest = HandshakeLog.hash_tag #ha log in
        let cookie = Ticket.create_cookie hrr digest cextra in
        let hrr = { hrr with hrr_extensions =
          (Extensions.E_cookie cookie) :: hrr.hrr_extensions; } in
        ns.state := (S_HRR offer hrr);
        Correct (ServerHelloRetryRequest hrr m.n_cipher_suite)
      | Nego_accept sexts ->
        trace ("negotiated "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
        ns.state := S_ClientHello m cert;
        Correct (ServerMode m cert (Extensions.ext_of_custom sexts))
*)
*)
