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

let write_binder_ph'
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
  ()
: LWP.Write unit LWP.emp lwp_pskBinderEntry (fun _ -> True) (fun _ _ out -> out == compute_binder_ph_new (LWP.deref_spec tc)) inv
=
  let c = LWP.deref CipherSuite.cipherSuite13_reader (Parsers.TicketContents13.lwp_accessor_ticketContents13_cs tc) in
  let (CipherSuite13 _ h) = cipherSuite_of_cipherSuite13 c in
  let len : U32.t = Hacl.Hash.Definitions.hash_len h in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  );
  LWP.valid_synth _ _ _ _ _ Aux.valid_pskBinderEntry_intro

let write_obfuscate_age'
  (#inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.Write unit LWP.emp Parsers.PskIdentity.lwp_pskIdentity (fun _ -> True) (fun _ _ out -> out == obfuscate_age_new now (LWP.deref_spec ri)) inv
=
  LWP.cat (Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_identity ri);
  let tk = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_ticket ri in
  let creation_time = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwp_accessor_ticketContents13_creation_time tk) in
  let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
  let age_add = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwp_accessor_ticketContents13_age_add tk) in
  let obfuscated_age = PSK.encode_age age age_add in
  LWP.append LWP.parse_u32 LowParse.Low.Int.write_u32 obfuscated_age;
  LWP.valid_synth _ _ _ _ _ Aux.valid_pskIdentity_intro

[@@expect_failure] // FIXME: WHY WHY WHY?
inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data
  (#inv: LWP.memory_invariant)
  ()
: LWP.EWrite
    unit
    LWP.emp
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ out -> out == Parsers.ClientHelloExtension.CHE_early_data ())
    (fun _ -> True)
    inv
=
  LWP.start Parsers.ExtensionType.lwp_extensionType
  Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Early_data;
  LWP.frame _ _ _ _ _ _ _ (fun _ ->
    LWP.parse_vldata_intro_ho
      LWP.emp 0ul 65535ul _ _ _ (wret #inv)
  );
  LWP.wfailwith "abc"

[@@expect_failure] // FIXME: WHY WHY WHY?
inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data
  (#inv: LWP.memory_invariant)
  ()
: LWP.EWrite
    unit
    LWP.emp
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ out -> out == Parsers.ClientHelloExtension.CHE_early_data ())
    (fun _ -> True)
    inv
=
  LWP.start Parsers.ExtensionType.lwp_extensionType
  Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Early_data;
  LWP.frame _ _ _ _ _ _ _ (fun _ ->
    LWP.parse_vldata_intro_ho
      LWP.emp 0ul 65535ul _ _ _ (wret #inv);
    LWP.valid_synth _ _ _ _ _ Aux.valid_clientHelloExtension_CHE_early_data_intro
  );
  LWP.valid_synth _ _ _ _ _ Aux2.valid_synth_constr_clientHelloExtension_CHE_early_data

let wret #inv () : LWP.Write unit LWP.emp LWP.emp (fun _ -> True) (fun _ _ _ -> True) inv = ()


inline_for_extraction
let parse_vldata_intro_ho
  (#inv: LWP.memory_invariant)
  (p: LWP.parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
  (pre: LWP.pre_t LWP.emp)
  (post: LWP.post_t unit LWP.emp p pre)
  (post_err: LWP.post_err_t LWP.emp pre)
  ($f: (unit -> LWP.EWrite unit LWP.emp p pre post post_err inv))
  ()
: LWP.EWrite unit LWP.emp (LWP.parse_vldata p min max)
    (fun _ ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, v) ->
        post () () v ==> (U32.v min <= LWP.size p v /\ LWP.size p v <= U32.v max)
      | _ -> True
      end
    )
    (fun _ _ vout ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, v) ->
        post () () v /\
        (vout <: dfst p) == v
      | _ -> False
      end
    )
    (fun vin ->
      post_err ()
    )
    inv
= LWP.parse_vldata_intro_ho p min max pre post post_err f

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data
  (#inv: LWP.memory_invariant)
  ()
: LWP.Write
    unit
    LWP.emp
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ out -> out == Parsers.ClientHelloExtension.CHE_early_data ())
    inv
=
  LWP.start Parsers.ExtensionType.lwp_extensionType
    Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Early_data;
  LWP.frame _ _ _ _ _ _ _ (
    parse_vldata_intro_ho
      LWP.emp 0ul 65535ul _ _ _ (wret #inv)
  );
  LWP.valid_synth _ _ _ _ _
    (LWP.valid_synth_star_compat_l
      _ _ _ _ _
      Aux.valid_clientHelloExtension_CHE_early_data_intro
    );
  LWP.valid_synth _ _ _ _ _ Aux2.valid_synth_constr_clientHelloExtension_CHE_early_data

module L = FStar.List.Tot

[@@expect_failure] // FIXME: WHY WHY WHY?
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
    (fun vin _ vout ->
      match final_extensions_new (LWP.deref_spec cfg) edi (LWP.deref_list_spec lri) now with
      | TLS.Result.Correct l -> (vout <: list Parsers.ClientHelloExtension.clientHelloExtension) == (vin `L.append` l)
      | _ -> False
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
    then
      LWP.wfailwith "not implemented" 
    else begin
      LWP.parse_vllist_snoc_ho Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul max _ _ _ (
        Aux2.constr_clientHelloExtension_CHE_psk_key_exchange_modes (
          parse_vldata_intro_ho Parsers.PskKeyExchangeModes.lwp_pskKeyExchangeModes 0ul 65535ul _ _ _ (fun _ ->
            let open Parsers.PskKeyExchangeMode in
            LWP.parse_vllist_nil lwp_pskKeyExchangeMode 255ul;
            LWP.parse_vllist_snoc_ho lwp_pskKeyExchangeMode 0ul 255ul _ _ _ (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_ke
            );
            LWP.parse_vllist_snoc_ho lwp_pskKeyExchangeMode 0ul 255ul _ _ _ (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_dhe_ke
            );
            LWP.parse_vllist_recast _ _ _ 1ul 255ul;
            LWP.valid_synth _ _ _ _ _
              Aux.valid_synth_pskKeyExchangeModes_intro
          )
        )
      )
    end
  | _ ->
    L.append_l_nil (Ghost.reveal vin <: list Parsers.ClientHelloExtension.clientHelloExtension)
