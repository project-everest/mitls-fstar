module Test.FinalExtensions

module LWP = LowParse.Writers.NoHoare.Combinators
module U32 = FStar.UInt32
module B = LowStar.Buffer

let hash_len (c: Parsers.CipherSuite13.cipherSuite13) : Tot (u: U32.t { 32 <= U32.v u /\ U32.v u <= 255 }) =
  let open Parsers.CipherSuite13 in
  match c with
  | Constraint_TLS_AES_128_GCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_256_GCM_SHA384 _ -> 48ul
  | Constraint_TLS_CHACHA20_POLY1305_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_8_SHA256 _ -> 32ul

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let compute_binder_ph1
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.PskBinderEntry.lwp_pskBinderEntry inv
=
  let cs = Parsers.TicketContents13.lwp_accessor_ticketContents13_cs tc in
  let c = LWP.deref Parsers.CipherSuite13.cipherSuite13_reader cs in
  let len : U32.t = hash_len c in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  )

 //  ; LWP.valid_rewrite Parsers.PskBinderEntry.pskBinderEntry_lwp_rewrite // automatic thanks to subcomp

[@@ noextract_to "Kremlin"] noextract
let compute_binder_ph2 = compute_binder_ph1 // to avoid inline_for_extraction in effect indices, implicit args, etc.

// this will be extracted as a C function
let extract_compute_binder
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: Tot (LWP.extract_t inv (compute_binder_ph2 inv tc))
= LWP.extract _ (compute_binder_ph1 inv tc)

// this will be inlined as an explicit function call
inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let compute_binder_ph
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: LWP.TWrite unit LWP.parse_empty Parsers.PskBinderEntry.lwp_pskBinderEntry inv
= LWP.wrap_extracted_impl _ _ (extract_compute_binder inv tc)

inline_for_extraction
let encode_age age mask = U32.(age +%^ mask)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let obfuscate_age1
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.PskIdentity.lwp_pskIdentity inv
=
  let id = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_identity ri in
  let tk = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_ticket ri in
  let ct = Parsers.TicketContents13.lwp_accessor_ticketContents13_creation_time tk in
  let creation_time = LWP.deref LowParse.Low.Int.read_u32 ct in
  let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
  let aa = Parsers.TicketContents13.lwp_accessor_ticketContents13_age_add tk in
  let age_add = LWP.deref LowParse.Low.Int.read_u32 aa in
  let obfuscated_age = encode_age age age_add in
  Parsers.PskIdentity.pskIdentity_lwriter
    (fun _ -> LWP.cat id)
    (fun _ -> LWP.start LWP.parse_u32 LowParse.Low.Int.write_u32 obfuscated_age)

[@@ noextract_to "Kremlin"] noextract
let obfuscate_age2 = obfuscate_age1

let extract_obfuscate_age
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: Tot (LWP.extract_t inv (obfuscate_age2 inv now ri))
= LWP.extract inv (obfuscate_age1 inv now ri)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let obfuscate_age
  (#inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: LWP.TWrite unit LWP.parse_empty Parsers.PskIdentity.lwp_pskIdentity inv
= LWP.wrap_extracted_impl _ _ (extract_obfuscate_age inv now ri)


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
