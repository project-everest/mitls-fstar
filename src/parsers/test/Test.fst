module Test
include Test.FinalExtensions

module LWP = LowParse.Writers.NoHoare.Combinators
module U32 = FStar.UInt32
module B = LowStar.Buffer

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let keyshares1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share inv))
  ()
: LWP.TWrite unit (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul) (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul) inv
=
  let mv = Parsers.MiTLSConfig.lwp_accessor_miTLSConfig_max_version cfg in
  let mv = Parsers.KnownProtocolVersion.lwp_knownProtocolVersion_accessor_tag mv in
  let max_version = LWP.deref Parsers.ProtocolVersion.protocolVersion_reader mv in
  match max_version, ks with
  | Parsers.ProtocolVersion.TLS_1p3, Some ks ->
    LWP.frame (fun _ -> Parsers.ClientHelloExtension.clientHelloExtension_key_share_lwriter (fun _ -> LWP.cat ks));
    LWP.extend_vllist_snoc _ _ _
  | _ -> ()

[@@ noextract_to "Kremlin"] noextract
let keyshares2 = keyshares1

let extract_keyshares
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share inv))
: Tot (LWP.extract_t _ (keyshares2 inv cfg ks))
= LWP.extract _ (keyshares1 _ _ _)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let keyshares
  (#inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share inv))
: LWP.TWrite unit (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul) (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul) inv
= LWP.wrap_extracted_impl _ _ (extract_keyshares inv cfg ks)

#push-options "--z3rlimit 16"
inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let clientHelloExtensions_of_unknown_extensions1
  (inv: LWP.memory_invariant)
  (l: LWP.ptr Parsers.UnknownExtensions.lwp_unknownExtensions inv)
  ()
: LWP.TWrite unit 
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    inv
=
  let l = LWP.cast (Parsers.UnknownExtensions.unknownExtensions_lwp_write_recip ()) l in
  let l = LWP.lptr_of_vllist_ptr _ _ _ l in
  LWP.list_map'
    _ _
    (fun x ->
      let tg = Parsers.TaggedUnknownExtension.lwp_taggedUnknownExtension_accessor_tag x in
      let tg = LWP.deref Parsers.ExtensionType.extensionType_reader tg in
      let tg = Parsers.ExtensionType.Unknown_extensionType?._0 tg in
      Parsers.ClientHelloExtension.clientHelloExtension_lwriter_unknown tg (fun _ ->
        let pl = Parsers.TaggedUnknownExtension.lwp_taggedUnknownExtension_accessor_Unknown x in
        LWP.cat (LWP.cast (Parsers.TaggedUnknownExtension_payload_default.taggedUnknownExtension_payload_default_lwp_rewrite_recip ()) pl)
      )
    )
    _ _
    l
#pop-options

[@@ noextract_to "Kremlin"] noextract
let clientHelloExtensions_of_unknown_extensions2 = clientHelloExtensions_of_unknown_extensions1

let extract_clientHelloExtensions_of_unknown_extensions
  (inv: LWP.memory_invariant)
  (l: LWP.ptr Parsers.UnknownExtensions.lwp_unknownExtensions inv)
: Tot (LWP.extract_t _ (clientHelloExtensions_of_unknown_extensions2 inv l))
= LWP.extract _ (clientHelloExtensions_of_unknown_extensions1 _ _)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let clientHelloExtensions_of_unknown_extensions
  (#inv: LWP.memory_invariant)
  (l: LWP.ptr Parsers.UnknownExtensions.lwp_unknownExtensions inv)
: LWP.TWrite unit (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul) (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul) inv
= LWP.wrap_extracted_impl _ _ (extract_clientHelloExtensions_of_unknown_extensions inv l)

module PV = Parsers.ProtocolVersion
module KPV = Parsers.KnownProtocolVersion

let implemented (pv: PV.protocolVersion) = pv = PV.TLS_1p2 || pv = PV.TLS_1p3

(** Determine the oldest protocol versions for TLS *)
let minPV (a b: Parsers.ProtocolVersion.protocolVersion) =
  let open PV in
  match a,b with
  | SSL_3p0, _  | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _  | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _  | _, TLS_1p1 -> TLS_1p1
  | TLS_1p2, _  | _, TLS_1p2 -> TLS_1p2
  | TLS_1p3, _  | _, TLS_1p3 -> TLS_1p3
  | Unknown_protocolVersion x, 
    Unknown_protocolVersion y -> Unknown_protocolVersion (if x `FStar.UInt16.lt` y then x else y)

let leqPV a b = (a = minPV a b)
let geqPV a b = (b = minPV a b)

let supported (min_version max_version pv: PV.protocolVersion) : Tot bool =
  implemented pv &&
  min_version `leqPV` pv && pv `leqPV` max_version

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let supported_versions1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
=
  let minv = Parsers.MiTLSConfig.lwp_accessor_miTLSConfig_min_version cfg in
  let minv = LWP.deref KPV.knownProtocolVersion_reader minv in
  let minv = KPV.tag_of_knownProtocolVersion minv in
  let maxv = Parsers.MiTLSConfig.lwp_accessor_miTLSConfig_max_version cfg in
  let maxv = LWP.deref KPV.knownProtocolVersion_reader maxv in
  let maxv = KPV.tag_of_knownProtocolVersion maxv in
  Parsers.ClientHelloExtension.clientHelloExtension_supported_versions_lwriter (fun _ ->
    Parsers.ClientHelloExtension_CHE_supported_versions.clientHelloExtension_CHE_supported_versions_lwp_writer (fun _ ->
      LWP.write_vllist_nil _ _;
      LWP.ifthenelse_combinator
        (supported minv maxv PV.TLS_1p3)
        (fun _ -> LWP.extend_vllist_snoc_ho _ _ _ (fun _ -> LWP.start _ PV.protocolVersion_writer PV.TLS_1p2))
        (fun _ -> ());
      LWP.ifthenelse_combinator
        (supported minv maxv PV.TLS_1p3)
        (fun _ -> LWP.extend_vllist_snoc_ho _ _ _ (fun _ -> LWP.start _ PV.protocolVersion_writer PV.TLS_1p2))
        (fun _ -> ());
      Parsers.SupportedVersions.supportedVersions_lwp_write ()
    )
  )

[@@ noextract_to "Kremlin"] noextract
let supported_versions2 = supported_versions1

let extract_supported_versions
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
: Tot (LWP.extract_t _ (supported_versions2 inv cfg))
= LWP.extract _ (supported_versions1 _ _)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let supported_versions
  (#inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
: LWP.TWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
= LWP.wrap_extracted_impl _ _ (extract_supported_versions _ cfg)

(* From: src/tls/Negotiation.fst: prepareClientextensions *)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_extensions1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share inv))
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtensions.lwp_clientHelloExtensions
    inv
=
  LWP.write_vllist_nil _ _;
  let custom_exts = Parsers.MiTLSConfig.lwp_accessor_miTLSConfig_custom_extensions cfg in
  clientHelloExtensions_of_unknown_extensions custom_exts;
  LWP.extend_vllist_snoc_ho _ _ _ (fun _ -> supported_versions cfg);
  keyshares cfg ks;
  write_final_extensions cfg edi lri now;
  Parsers.ClientHelloExtensions.clientHelloExtensions_lwp_write ()

[@@ noextract_to "Kremlin"] noextract
let write_extensions2 = write_extensions1

let write_extensions
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share inv))
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t _ (write_extensions2 inv cfg ks edi lri now))
= LWP.extract _ (write_extensions1 _ _ _ _ _ _)

let main () : Tot C.exit_code = C.EXIT_SUCCESS
