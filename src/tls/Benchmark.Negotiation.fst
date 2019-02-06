module Benchmark.Negotiation

open Parsers.ProtocolVersion
open Parsers.SupportedVersions
open Parsers.ClientHelloExtension

open FStar.Integers
open LowParse.Low.Base 
open FStar.Error // TODO: should be included in TLSError?
open TLSError // TODO: should be included in Mem?
open Mem

noeq type config : Type0 = {
    // supported versions, implicitly preferring the latest versions
    min_version: protocolVersion; 
    max_version: protocolVersion;

}

// 19-01-18 where is it defined?
let uint16_min (x y: UInt16.t) = if FStar.UInt16.(x <=^ y) then x else y 

(** Determine the oldest protocol versions for TLS *)
let minPV (a b: Parsers.ProtocolVersion.protocolVersion) =
  match a,b with
  | SSL_3p0, _  | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _  | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _  | _, TLS_1p1 -> TLS_1p1
  | TLS_1p2, _  | _, TLS_1p2 -> TLS_1p2
  | TLS_1p3, _  | _, TLS_1p3 -> TLS_1p3
  | Unknown_protocolVersion x, 
    Unknown_protocolVersion y -> Unknown_protocolVersion (uint16_min x y)

let leqPV a b = (a = minPV a b)


/// We currently implement only TLS 1.2 and 1.3, and the negotiated
/// version can be further constrained in the connection initial
/// configuration.

let implemented pv = pv = TLS_1p2 || pv = TLS_1p3

let supported cfg pv =
  implemented pv &&
  cfg.min_version `leqPV` pv && pv `leqPV` cfg.max_version


/// (1) Client offers supported versions
///
/// Offer only locally-implemented versions, irrespective of the
/// configuration. We may provide more flexible configurations by replacing
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
  (cfg:config) 
  (pv:protocolVersion) 
  (pvs:list protocolVersion): 
  (pvs1:list protocolVersion {List.length pvs1 <= List.length pvs + 1}) 
= 
  if supported cfg pv then (
    List.lemma_snoc_length (pvs,pv);
    pvs @ [pv] ) 
  else pvs 

// 19-01-26 slow TC, due to constructor refinements? 
#push-options "--z3rlimit 100"
let support cfg: result clientHelloExtension =
  let vs = snoc_supportedVersion cfg TLS_1p3 [] in 
  let vs = snoc_supportedVersion cfg TLS_1p2 vs in 
  if List.isEmpty vs 
  then fatal Internal_error "configuration must include a supported protocol version"
  else Correct (CHE_supported_versions vs)
#pop-options 

// migrate to LowParse? 
let live_slice_pos h0 out p0 = live_slice h0 out /\ p0 <= out.len 

#push-options "--z3rlimit 100" 
val write_supportedVersions
  (cfg:config) 
  (out:slice) (p0:UInt32.t) : Stack (result UInt32.t) 
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

val write_supportedVersion 
  (cfg: config) 
  (pv: protocolVersion) 
  (out: slice) (pl p0: UInt32.t) : Stack UInt32.t
  (requires fun h0 -> 
    valid_list protocolVersion_parser h0 out pl p0 /\
    v p0 + 2 <= v out.len
    //19-01-26 slower & causing a timeout below: [v out.len - v p0 >= 2]
    //19-01-26 much slower: [out.len - p0 >= 2ul]
    )
  (ensures fun h0 p1 h1 -> 
    valid_list protocolVersion_parser h1 out pl p1 /\
    v p1 - v p0 <= 2 /\ 
    LowStar.Buffer.modifies (loc_slice_from_to out p0 p1) h0 h1 /\
    contents_list protocolVersion_parser h1 out pl p1 == snoc_supportedVersion cfg pv (contents_list protocolVersion_parser h0 out pl p0))

#push-options "--z3rlimit 100"
let write_supportedVersion cfg pv out pl p0 =
  if supported cfg pv then (
    let p1 = protocolVersion_writer pv out p0 in
    let h1 = get () in
    valid_list_snoc protocolVersion_parser h1 out pl p0;
    p1
  ) else p0

let write_supportedVersions cfg out p0 =
  if out.len - p0 < 10ul then fatal Internal_error "output buffer" else
  let pl_extension = p0 + 2ul in // extension payload, after the extension tag
  let pl_CHE_supported_versions = pl_extension + 2ul in // CHE_supported_versions payload, after the CHE_supported_versions length
  let pl_supported_versions = pl_CHE_supported_versions + 1ul in // supported_versions payload, after the supported_versions list length
  let h = get () in
  valid_list_nil protocolVersion_parser h out pl_supported_versions; 
  let pl = write_supportedVersion cfg TLS_1p3 out pl_supported_versions pl_supported_versions in 
  let pl = write_supportedVersion cfg TLS_1p2 out pl_supported_versions pl in
  if pl = pl_supported_versions then fatal Internal_error "configuration must include a supported protocol version" else 
    let h = get () in
    valid_list_cons_recip protocolVersion_parser h out pl_supported_versions pl;
    finalize_supportedVersions out pl_CHE_supported_versions pl;
    clientHelloExtension_CHE_supported_versions_finalize out pl_extension pl;
    finalize_clientHelloExtension_supported_versions out p0;
    Correct pl
// this kind of code is hard to get right, as the programmer needs to
// know every detail of the wire format, including its byte offsets
// and explicit proof steps---every error takes 10' 
