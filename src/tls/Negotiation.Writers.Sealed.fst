module Negotiation.Writers.Sealed

module LWP = LowParseWriters.Sealed
module Aux = Negotiation.Writers.Aux.Sealed
module Aux2 = Negotiation.Writers.Aux2.Sealed

#reset-options "--z3cliopt smt.arith.nl=false"

open TLSConstants
open Extensions
open Negotiation


module U32 = FStar.UInt32
module B = LowStar.Buffer

#push-options "--z3rlimit 16 --query_stats"

inline_for_extraction
noextract
let compute_binder_ph1
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
  ()
: LWP.TWrite unit LWP.emp lwp_pskBinderEntry inv
=
  let c = LWP.deref CipherSuite.cipherSuite13_reader (Parsers.TicketContents13.lwps_accessor_ticketContents13_cs tc) in
  let (CipherSuite13 _ h) = cipherSuite_of_cipherSuite13 c in
  let len : U32.t = Hacl.Hash.Definitions.hash_len h in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  );
  LWP.valid_synth Aux.valid_pskBinderEntry_intro'

noextract
let compute_binder_ph2 = compute_binder_ph1 // to avoid inline_for_extraction in effect indices, implicit args, etc.

// this will be extracted as a C function
let extract_compute_binder
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: Tot (LWP.extract_t inv (compute_binder_ph2 inv tc))
= LWP.extract _ (compute_binder_ph1 inv tc)

// this will be inlined as an explicit function call
inline_for_extraction
noextract
let compute_binder_ph
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: LWP.TWrite unit LWP.emp lwp_pskBinderEntry inv
= LWP.wrap_extracted_impl _ _ (extract_compute_binder inv tc)

inline_for_extraction
noextract
let obfuscate_age1
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.TWrite unit LWP.emp Parsers.PskIdentity.lwp_pskIdentity inv
=
  LWP.cat (Parsers.ResumeInfo13.lwps_accessor_resumeInfo13_identity ri);
  let tk = Parsers.ResumeInfo13.lwps_accessor_resumeInfo13_ticket ri in
  let creation_time = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwps_accessor_ticketContents13_creation_time tk) in
  let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
  let age_add = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwps_accessor_ticketContents13_age_add tk) in
  let obfuscated_age = PSK.encode_age age age_add in
  LWP.append LWP.parse_u32 LowParse.Low.Int.write_u32 obfuscated_age;
  LWP.valid_synth Aux.valid_pskIdentity_intro'

noextract
let obfuscate_age2 = obfuscate_age1

let extract_obfuscate_age
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: Tot (LWP.extract_t inv (obfuscate_age2 inv now ri))
= LWP.extract inv (obfuscate_age1 inv now ri)

inline_for_extraction
noextract
let obfuscate_age
  (#inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: LWP.TWrite unit LWP.emp Parsers.PskIdentity.lwp_pskIdentity inv
= LWP.wrap_extracted_impl _ _ (extract_obfuscate_age inv now ri)


inline_for_extraction
noextract
let write_psk_key_exchange_modes1
  (inv: LWP.memory_invariant)
  (_: unit)
: LWP.TWrite unit LWP.emp Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
=
  Aux2.constr_clientHelloExtension_CHE_psk_key_exchange_modes (fun _ ->
    LWP.parse_vldata_intro_weak_ho' // FIXME: this should be parse_vldata_intro_ho', but I can't reason on reify
            Parsers.PskKeyExchangeModes.lwp_pskKeyExchangeModes 0ul 65535ul (fun _ ->
            let open Parsers.PskKeyExchangeMode in
            LWP.parse_vllist_nil lwp_pskKeyExchangeMode 255ul;
            LWP.parse_vllist_snoc_weak_ho' lwp_pskKeyExchangeMode 0ul 255ul (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_ke
            );
            LWP.parse_vllist_snoc_weak_ho' lwp_pskKeyExchangeMode 0ul 255ul (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_dhe_ke
            );
            LWP.parse_vllist_recast _ _ _ 1ul 255ul;
            LWP.valid_synth
              Aux.valid_synth_pskKeyExchangeModes_intro'
        );
          LWP.valid_synth
            Aux.valid_clientHelloExtension_CHE_psk_key_exchange_modes_intro';
          ()
  )

noextract
let write_psk_key_exchange_modes2 = write_psk_key_exchange_modes1

let extract_write_psk_key_exchange_modes
  (inv: LWP.memory_invariant)
: Tot (LWP.extract_t inv (write_psk_key_exchange_modes2 inv))
= LWP.extract _ (write_psk_key_exchange_modes1 inv)

inline_for_extraction
noextract
let write_psk_key_exchange_modes
  (#inv: LWP.memory_invariant)
  (_: unit)
: LWP.TWrite unit LWP.emp Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
= LWP.wrap_extracted_impl _ _ (extract_write_psk_key_exchange_modes inv)

#restart-solver

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data1
  (inv: LWP.memory_invariant)
  ()
: LWP.TWrite
    unit
    LWP.emp
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  Aux2.constr_clientHelloExtension_CHE_early_data (fun _ ->
    LWP.parse_vldata_intro_weak_ho'
      LWP.emp 0ul 65535ul (fun _ -> ());
    LWP.valid_synth Aux.valid_clientHelloExtension_CHE_early_data_intro'
  )

noextract
let write_clientHelloExtension_CHE_early_data2 = write_clientHelloExtension_CHE_early_data1

let extract_write_clientHelloExtension_CHE_early_data
  (inv: LWP.memory_invariant)
: Tot (LWP.extract_t inv (write_clientHelloExtension_CHE_early_data2 inv))
= LWP.extract inv (write_clientHelloExtension_CHE_early_data1 inv)

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data
  (#inv: LWP.memory_invariant)
  ()
: LWP.TWrite
    unit
    LWP.emp
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
= LWP.wrap_extracted_impl _ _ (extract_write_clientHelloExtension_CHE_early_data inv)

#restart-solver

inline_for_extraction
noextract
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
= let max_version = LWP.deref Parsers.ProtocolVersion.protocolVersion_reader (Parsers.KnownProtocolVersion.lwps_knownProtocolVersion_accessor_tag (Parsers.MiTLSConfig.lwps_accessor_miTLSConfig_max_version cfg)) in
  match max_version with
  | TLS_1p3 ->
    let allow_psk_resumption = LWP.list_exists (fun _ -> true) lri in
    let allow_dhe_resumption = LWP.list_exists (fun _ -> true) lri in
    if allow_psk_resumption || allow_dhe_resumption
    then begin
(*
      let psk_kex () : LWP.TWrite unit LWP.emp Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_psk_key_exchange_modes inv =
        LWP.parse_vldata_intro_weak_ho' lwp_pskKeyExchangeModes 0ul 65535ul (fun _ -> // FIXME: should be parse_vldata_intro_ho', but I can't reason on reify
          LWP.parse_vllist_nil lwp_pskKeyExchangeMode 255ul;
          if allow_psk_resumption
          then
            LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ ->
              LWP.start _ pskKeyExchangeMode_writer Psk_ke
            );
          if allow_dhe_resumption
          then
            LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ ->
              LWP.start _ pskKeyExchangeMode_writer Psk_dhe_ke
            );
          LWP.parse_vllist_recast _ _ _ 1ul _;
          LWP.valid_synth Aux.valid_synth_pskKeyExchangeModes_intro'
        );
        LWP.valid_synth Aux.valid_clientHelloExtension_CHE_psk_key_exchange_modes_intro'
      in
      let binders () : LWP.TWrite unit LWP.emp lwp_offeredPsks_binders inv =
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          lwp_pskBinderEntry
          (fun r -> compute_binder_ph (Parsers.ResumeInfo13.lwps_accessor_resumeInfo13_ticket r))
          33ul 65535ul
          lri
          ;
        LWP.valid_synth Aux.valid_offeredPsks_binders_intro'
      in
      let pskidentities () : LWP.TWrite unit LWP.emp lwp_offeredPsks_identities inv =
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          lwp_pskIdentity
          (obfuscate_age now)
          7ul 65535ul
          lri
          ;
        LWP.valid_synth Aux.valid_offeredPsks_identities_intro'
      in
      let ke () : LWP.TWrite unit LWP.emp  Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_pre_shared_key inv =
        LWP.parse_vldata_intro_weak_ho' Parsers.PreSharedKeyClientExtension.lwp_preSharedKeyClientExtension 0ul 65535ul (fun _ -> // FIXME: this should be parse_vldata_intro_ho', but I can't reason on reify
          pskidentities ();
          LWP.frame binders;
          LWP.valid_synth Aux.valid_offeredPsks_intro';
          LWP.valid_synth Aux.valid_preSharedKeyClientExtension_intro'
        );
        LWP.valid_synth Aux.valid_clientHelloExtension_CHE_pre_shared_key_intro'
      in
      LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ ->
        Aux2.constr_clientHelloExtension_CHE_psk_key_exchange_modes psk_kex
      );
      if edi
      then
        LWP.parse_vllist_snoc_weak_ho' _ _ _
          write_clientHelloExtension_CHE_early_data;
      LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ ->
        Aux2.constr_clientHelloExtension_CHE_pre_shared_key ke
      );
*)
      ()
    end else begin
      LWP.parse_vllist_snoc_weak_ho' // FIXME: this should be parse_vllist_snoc_ho', but I can't reason on reify
        Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul (fun _ ->
        write_psk_key_exchange_modes ()
      )
    end
  | _ -> ()
//    L.append_l_nil (Ghost.reveal vin <: list Parsers.ClientHelloExtension.clientHelloExtension)

noextract
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
noextract
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
