module Negotiation.Writers.LayeredEffects

friend Negotiation

module LWP = LowParseWriters.Parsers
module Aux = Negotiation.Writers.Aux
module Aux2 = Negotiation.Writers.Aux2

#reset-options "--z3cliopt smt.arith.nl=false"

open TLSConstants
open Extensions
open Negotiation

module U32 = FStar.UInt32
module B = LowStar.Buffer

#push-options "--z3rlimit 16 --query_stats"

let compute_binder_ph
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: LWP.Write unit LWP.parse_empty lwp_pskBinderEntry (fun _ -> True) (fun _ _ out -> out == compute_binder_ph_new (LWP.deref_spec tc)) inv
=
  let c = LWP.deref CipherSuite.cipherSuite13_reader (Parsers.TicketContents13.lwp_accessor_ticketContents13_cs tc) in
  let (CipherSuite13 _ h) = cipherSuite_of_cipherSuite13 c in
  let len : U32.t = Hacl.Hash.Definitions.hash_len h in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  );
  LWP.valid_rewrite _ _ _ _ _ Aux.valid_pskBinderEntry_intro

let obfuscate_age
  (#inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: LWP.Write unit LWP.parse_empty Parsers.PskIdentity.lwp_pskIdentity (fun _ -> True) (fun _ _ out -> out == obfuscate_age_new now (LWP.deref_spec ri)) inv
=
  LWP.cat (Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_identity ri);
  let tk = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_ticket ri in
  let creation_time = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwp_accessor_ticketContents13_creation_time tk) in
  let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
  let age_add = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwp_accessor_ticketContents13_age_add tk) in
  let obfuscated_age = PSK.encode_age age age_add in
  LWP.append LWP.parse_u32 LowParse.Low.Int.write_u32 obfuscated_age;
  LWP.valid_rewrite _ _ _ _ _ Aux.valid_pskIdentity_intro

#restart-solver

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data
  (#inv: LWP.memory_invariant)
  ()
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ out -> out == Parsers.ClientHelloExtension.CHE_early_data ())
    (fun _ -> True) // FIXME: this should be False, but I can't reason on reify
    inv
=
  LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Early_data;
  LWP.frame' _ _ _ _ (fun _ ->
    LWP.parse_vldata_intro_weak_ho' // FIXME: should be _ho', but cannot reason on reify
      LWP.parse_empty 0ul 65535ul (fun _ -> ());
    LWP.valid_rewrite _ _ _ _ _ Aux.valid_clientHelloExtension_CHE_early_data_intro
  );
  LWP.valid_rewrite _ _ _ _ _ Aux2.valid_rewrite_constr_clientHelloExtension_CHE_early_data

module L = FStar.List.Tot

effect TWrite
  (a:Type)
  (pin: LWP.parser)
  (pout: LWP.parser)
  (inv: LWP.memory_invariant)
= LWP.EWrite a pin pout (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv

#restart-solver

noextract
let write_final_extensions
  (#inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  (max: U32.t { U32.v max > 0 })
: LWP.EWrite
    unit
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul max)
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul max)
    (fun _ -> True)
    (fun vin _ vout -> True
    (*
      match final_extensions_new (LWP.deref_spec cfg) edi (LWP.deref_list_spec lri) now with
      | TLS.Result.Correct l -> (vout <: list Parsers.ClientHelloExtension.clientHelloExtension) == (vin `L.append` l)
      | _ -> False
    *)
    )
    (fun vin ->
      True
(*
      match final_extensions_new (LWP.deref_spec cfg) edi (LWP.deref_list_spec lri) with
      | Correct l -> LWP.list_size Parsers.ClientHelloExtension.lwp_clientHelloExtension vin + LWP.list_size Parsers.ClientHelloExtension.lwp_clientHelloExtension l > U32.v max
      | _ -> True
*)
    )
    inv
= let vin = LWP.get_state () in
  let max_version = LWP.deref Parsers.ProtocolVersion.protocolVersion_reader (Parsers.KnownProtocolVersion.lwp_knownProtocolVersion_accessor_tag (Parsers.MiTLSConfig.lwp_accessor_miTLSConfig_max_version cfg)) in
  match max_version with
  | TLS_1p3 ->
    let allow_psk_resumption = LWP.list_exists allow_psk_resumption_new (fun _ -> true) lri in
    let allow_dhe_resumption = LWP.list_exists allow_dhe_resumption_new (fun _ -> true) lri in
    if allow_psk_resumption || allow_dhe_resumption
    then begin
      let psk_kex () : TWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_psk_key_exchange_modes inv =
        LWP.parse_vldata_intro_weak_ho' lwp_pskKeyExchangeModes 0ul 65535ul (fun _ -> // FIXME: should be parse_vldata_intro_ho', but I can't reason on reify
          LWP.parse_vllist_nil lwp_pskKeyExchangeMode 255ul;
          if allow_psk_resumption
          then
            LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ -> // FIXME: should be _ho', but can't reason on reify
              LWP.start _ pskKeyExchangeMode_writer Psk_ke
            );
          if allow_dhe_resumption
          then
            LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ -> // same
              LWP.start _ pskKeyExchangeMode_writer Psk_dhe_ke
            );
          LWP.parse_vllist_recast _ _ _ 1ul _;
          LWP.valid_rewrite _ _ _ _ _ Aux.valid_rewrite_pskKeyExchangeModes_intro
        );
        LWP.valid_rewrite _ _ _ _ _ Aux.valid_clientHelloExtension_CHE_psk_key_exchange_modes_intro
      in
      let binders () : TWrite unit LWP.parse_empty lwp_offeredPsks_binders inv =
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          lwp_pskBinderEntry
          (fun r -> compute_binder_ph_new r.Parsers.ResumeInfo13.ticket)
          (fun r -> compute_binder_ph (Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_ticket r))
          33ul 65535ul
          lri
          ;
        LWP.valid_rewrite _ _ _ _ _ Aux.valid_offeredPsks_binders_intro
      in
      let pskidentities () : TWrite unit LWP.parse_empty lwp_offeredPsks_identities inv =
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          lwp_pskIdentity
          (obfuscate_age_new now)
          (obfuscate_age now)
          7ul 65535ul
          lri
          ;
        LWP.valid_rewrite _ _ _ _ _ Aux.valid_offeredPsks_identities_intro
      in
      let ke () : TWrite unit LWP.parse_empty  Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_pre_shared_key inv =
        LWP.parse_vldata_intro_weak_ho' Parsers.PreSharedKeyClientExtension.lwp_preSharedKeyClientExtension 0ul 65535ul (fun _ -> // FIXME: this should be parse_vldata_intro_ho', but I can't reason on reify
          pskidentities ();
          LWP.frame' _ _ _ _ binders;
          LWP.valid_rewrite _ _ _ _ _ Aux.valid_offeredPsks_intro;
          LWP.valid_rewrite _ _ _ _ _ Aux.valid_preSharedKeyClientExtension_intro
        );
        LWP.valid_rewrite _ _ _ _ _ Aux.valid_clientHelloExtension_CHE_pre_shared_key_intro
      in
      LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ ->
        Aux2.constr_clientHelloExtension_CHE_psk_key_exchange_modes' psk_kex
      );
      if edi
      then
        LWP.parse_vllist_snoc_weak_ho' _ _ _
          write_clientHelloExtension_CHE_early_data;
      LWP.parse_vllist_snoc_weak_ho' _ _ _ (fun _ ->
        Aux2.constr_clientHelloExtension_CHE_pre_shared_key' ke
      );
      ()
    end else begin
      LWP.parse_vllist_snoc_weak_ho' // FIXME: this should be parse_vllist_snoc_ho', but I can't reason on reify
        Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul max (fun _ ->
        Aux2.constr_clientHelloExtension_CHE_psk_key_exchange_modes' (fun _ ->
          LWP.parse_vldata_intro_weak_ho' // FIXME: this should be parse_vldata_intro_ho', but I can't reason on reify
            Parsers.PskKeyExchangeModes.lwp_pskKeyExchangeModes 0ul 65535ul (fun _ ->
            let open Parsers.PskKeyExchangeMode in
            LWP.parse_vllist_nil lwp_pskKeyExchangeMode 255ul;
            LWP.parse_vllist_snoc_weak_ho' lwp_pskKeyExchangeMode 0ul 255ul (fun _ -> // same
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_ke
            );
            LWP.parse_vllist_snoc_weak_ho' lwp_pskKeyExchangeMode 0ul 255ul (fun _ -> // same
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_dhe_ke
            );
            LWP.parse_vllist_recast _ _ _ 1ul 255ul;
            LWP.valid_rewrite _ _ _ _ _
              Aux.valid_rewrite_pskKeyExchangeModes_intro;
//            let l = LWP.get_state () in
//            assert ((Ghost.reveal l <: list pskKeyExchangeMode) == [Psk_ke; Psk_dhe_ke]); // surprisingly, reification reasoning (on the lambda arguments to parse_vllist_snoc_ho') used to work here!
            ()
          );
          LWP.valid_rewrite _ _ _ _ _
            Aux.valid_clientHelloExtension_CHE_psk_key_exchange_modes_intro;
//          let l = LWP.get_state () in
//          assert ((Ghost.reveal l <: list pskKeyExchangeMode) == [Psk_ke; Psk_dhe_ke]); // FIXME: this should work. WHY WHY WHY not?
          ()
        )
      )
    end
  | _ -> ()
//    L.append_l_nil (Ghost.reveal vin <: list Parsers.ClientHelloExtension.clientHelloExtension)
