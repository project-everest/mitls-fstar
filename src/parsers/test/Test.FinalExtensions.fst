module Test.FinalExtensions
include Test.BindersAge

module LWP = LowParse.Writers.NoHoare.Combinators
module U32 = FStar.UInt32
module B = LowStar.Buffer

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_psk_key_exchange_modes1
  (inv: LWP.memory_invariant)
  (_: unit)
: LWP.TWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
=
  Parsers.ClientHelloExtension.clientHelloExtension_psk_key_exchange_modes_lwriter (fun _ ->
    Parsers.ClientHelloExtension_CHE_psk_key_exchange_modes.clientHelloExtension_CHE_psk_key_exchange_modes_lwp_writer (fun _ ->
            let open Parsers.PskKeyExchangeMode in
            LWP.write_vllist_nil lwp_pskKeyExchangeMode _;
            LWP.extend_vllist_snoc_ho lwp_pskKeyExchangeMode _ _ (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_ke
            );
            LWP.extend_vllist_snoc_ho lwp_pskKeyExchangeMode _ _ (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_dhe_ke
            );
            Parsers.PskKeyExchangeModes.pskKeyExchangeModes_lwp_write ()
  ))

[@@ noextract_to "Kremlin"] noextract
let write_psk_key_exchange_modes2 = write_psk_key_exchange_modes1

let extract_write_psk_key_exchange_modes
  (inv: LWP.memory_invariant)
: Tot (LWP.extract_t inv (write_psk_key_exchange_modes2 inv))
= LWP.extract _ (write_psk_key_exchange_modes1 inv)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_psk_key_exchange_modes
  (#inv: LWP.memory_invariant)
  (_: unit)
: LWP.TWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
= LWP.wrap_extracted_impl _ _ (extract_write_psk_key_exchange_modes inv)

#restart-solver

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_psk_kex1
  (inv: LWP.memory_invariant)
  (allow_psk_resumption: bool)
  (allow_dhe_resumption: bool)
  ()
: LWP.TWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  Parsers.ClientHelloExtension.clientHelloExtension_psk_key_exchange_modes_lwriter (fun _ ->
    Parsers.ClientHelloExtension_CHE_psk_key_exchange_modes.clientHelloExtension_CHE_psk_key_exchange_modes_lwp_writer (fun _ ->
            LWP.write_vllist_nil _ _;
(* // FIXME: the following does not extract properly, it extracts to ((if allow_psk_resumption then f) buf len) instead of (if allow_psk_resumption then (f buf len))
            if allow_psk_resumption
            then
              LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
                LWP.start _ Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer Parsers.PskKeyExchangeMode.Psk_ke
              );
*)
            LWP.ifthenelse_combinator
              allow_psk_resumption
              (fun _ -> 
                LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
                  LWP.start _ Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer Parsers.PskKeyExchangeMode.Psk_ke
                )
              )
              (fun _ -> ());
(* same here
            if allow_dhe_resumption
            then
              LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
                LWP.start _ Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer Parsers.PskKeyExchangeMode.Psk_dhe_ke
              );
*)
            LWP.ifthenelse_combinator
              allow_dhe_resumption
              (fun _ ->
                LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
                  LWP.start _ Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer Parsers.PskKeyExchangeMode.Psk_dhe_ke
                )
              )
              (fun _ -> ());
            Parsers.PskKeyExchangeModes.pskKeyExchangeModes_lwp_write ()
          )
        )

[@@ noextract_to "Kremlin"] noextract
let write_psk_kex2 = write_psk_kex1

let extract_write_psk_kex
  (inv: LWP.memory_invariant)
  (allow_psk_resumption: bool)
  (allow_dhe_resumption: bool)
: Tot (LWP.extract_t inv (write_psk_kex2 inv allow_psk_resumption allow_dhe_resumption))
= LWP.extract inv (write_psk_kex1 inv allow_psk_resumption allow_dhe_resumption)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_psk_kex
  (#inv: LWP.memory_invariant)
  (allow_psk_resumption: bool)
  (allow_dhe_resumption: bool)
: LWP.TWrite 
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  LWP.wrap_extracted_impl _ _ (extract_write_psk_kex inv allow_psk_resumption allow_dhe_resumption)

#restart-solver

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_binders1
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.OfferedPsks.lwp_offeredPsks_binders inv
=
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          Parsers.PskBinderEntry.lwp_pskBinderEntry
          (fun r -> let tk = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_ticket r in compute_binder_ph tk)
          _ _ (* list bytesize bounds automatically inferred by F* *)
          lri
          ;
        Parsers.OfferedPsks_binders.offeredPsks_binders_lwp_write ()

[@@ noextract_to "Kremlin"] noextract
let write_binders2 = write_binders1

let extract_write_binders
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: Tot (LWP.extract_t inv (write_binders2 inv lri))
= LWP.extract inv (write_binders1 inv lri)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_binders
  (#inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: LWP.TWrite unit LWP.parse_empty Parsers.OfferedPsks.lwp_offeredPsks_binders inv
= LWP.wrap_extracted_impl _ _ (extract_write_binders inv lri)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_pskidentities1
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.OfferedPsks.lwp_offeredPsks_identities inv
=
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          Parsers.PskIdentity.lwp_pskIdentity
          (obfuscate_age now)
          _ _
          lri
          ;
        Parsers.OfferedPsks_identities.offeredPsks_identities_lwp_write ()

[@@ noextract_to "Kremlin"] noextract
let write_pskidentities2 = write_pskidentities1

let extract_write_pskidentities
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t inv (write_pskidentities2 inv lri now))
= LWP.extract inv (write_pskidentities1 inv lri now)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_pskidentities
  (#inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: LWP.TWrite unit LWP.parse_empty Parsers.OfferedPsks.lwp_offeredPsks_identities inv
= LWP.wrap_extracted_impl _ _ (extract_write_pskidentities inv lri now)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_pre_shared_key1
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite 
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  Parsers.ClientHelloExtension.clientHelloExtension_pre_shared_key_lwriter (fun _ ->
    Parsers.ClientHelloExtension_CHE_pre_shared_key.clientHelloExtension_CHE_pre_shared_key_lwp_writer (fun _ ->
    Parsers.OfferedPsks.offeredPsks_lwriter
      (fun _ ->
          write_pskidentities lri now
      )
      (fun _ ->
        write_binders lri
      )
    )
  )

[@@ noextract_to "Kremlin"] noextract
let write_pre_shared_key2 = write_pre_shared_key1

let extract_write_pre_shared_key
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t inv (write_pre_shared_key2 inv lri now))
= LWP.extract inv (write_pre_shared_key1 inv lri now)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_pre_shared_key
  (#inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: LWP.TWrite 
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  LWP.wrap_extracted_impl _ _ (extract_write_pre_shared_key inv lri now)

#restart-solver

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_final_extensions1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite
    unit
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    inv
= let mv = Parsers.MiTLSConfig.lwp_accessor_miTLSConfig_max_version cfg in
  let mv = Parsers.KnownProtocolVersion.lwp_knownProtocolVersion_accessor_tag mv in
  let max_version = LWP.deref Parsers.ProtocolVersion.protocolVersion_reader mv in
  match max_version with
  | Parsers.ProtocolVersion.TLS_1p3 ->
    let allow_psk_resumption = LWP.list_exists (fun _ -> true) lri in
    let allow_dhe_resumption = LWP.list_exists (fun _ -> true) lri in
    if allow_psk_resumption || allow_dhe_resumption
    then begin
      LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
        write_psk_kex allow_psk_resumption allow_dhe_resumption
      );
      if edi
      then
        LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
          Parsers.ClientHelloExtension.clientHelloExtension_early_data_lwriter (fun _ ->
            Parsers.ClientHelloExtension_CHE_early_data.clientHelloExtension_CHE_early_data_lwp_writer (fun _ -> ())
          )
        );
      LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
        write_pre_shared_key lri now
      );
      ()
    end else begin
      LWP.extend_vllist_snoc_ho
        Parsers.ClientHelloExtension.lwp_clientHelloExtension _ _ (fun _ ->
        write_psk_key_exchange_modes ()
      )
    end
  | _ -> ()

[@@ noextract_to "Kremlin"] noextract
let write_final_extensions2 = write_final_extensions1

let extract_write_final_extensions
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t inv (write_final_extensions2 inv cfg edi lri now))
= LWP.extract inv (write_final_extensions1 inv cfg edi lri now)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let write_final_extensions
  (#inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: LWP.TWrite
    unit
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    inv
= LWP.wrap_extracted_impl _ _ (extract_write_final_extensions inv cfg edi lri now)
