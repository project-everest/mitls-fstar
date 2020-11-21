module Test
module U32 = FStar.UInt32
module LP = LowParse.Spec.Base
open FStar.Error

let hash_len (c: Parsers.CipherSuite13.cipherSuite13) : Tot (u: U32.t { 32 <= U32.v u /\ U32.v u <= 255 }) =
  let open Parsers.CipherSuite13 in
  match c with
  | Constraint_TLS_AES_128_GCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_256_GCM_SHA384 _ -> 48ul
  | Constraint_TLS_CHACHA20_POLY1305_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_8_SHA256 _ -> 32ul

let compute_binder_ph (t: Parsers.TicketContents13.ticketContents13) : Tot Parsers.PskBinderEntry.pskBinderEntry =
  let cs = t.Parsers.TicketContents13.cs in
  let len : UInt32.t = hash_len cs in
  assert (32 <= U32.v len /\ U32.v len <= 256);
  FStar.Bytes.create len 0uy

let encode_age age mask = U32.(age +%^ mask)

let obfuscate_age (now: U32.t) (tk: Parsers.ResumeInfo13.resumeInfo13) : Tot Parsers.PskIdentity.pskIdentity =
    let age = FStar.UInt32.((now -%^ tk.Parsers.ResumeInfo13.ticket.Parsers.TicketContents13.creation_time) *%^ 1000ul) in
    {Parsers.PskIdentity.identity = tk.Parsers.ResumeInfo13.identity; Parsers.PskIdentity.obfuscated_ticket_age = encode_age age tk.Parsers.ResumeInfo13.ticket.Parsers.TicketContents13.age_add}

module CFG = Parsers.MiTLSConfig

let result t = optResult string t

let final_extensions
  (cfg: CFG.miTLSConfig) (edi: bool) (l: list Parsers.ResumeInfo13.resumeInfo13) (now: U32.t)
: Tot (result (list Parsers.ClientHelloExtension.clientHelloExtension))
= match Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.max_version with
  | Parsers.ProtocolVersion.TLS_1p3 ->
    let allow_psk_resumption = List.Tot.existsb (fun _ -> true) l in
    let allow_dhe_resumption = List.Tot.existsb (fun _ -> true) l in
    if allow_psk_resumption || allow_dhe_resumption
    then
      let psk_kex =
        (if allow_psk_resumption then [Parsers.PskKeyExchangeMode.Psk_ke] else []) @ (if allow_dhe_resumption then [Parsers.PskKeyExchangeMode.Psk_dhe_ke] else [])
      in
      let binders = List.Tot.map (fun r -> compute_binder_ph r.Parsers.ResumeInfo13.ticket) l in
      let pskidentities = List.Tot.map (obfuscate_age now) l in
      if not (Parsers.OfferedPsks.check_offeredPsks_identities_list_bytesize pskidentities)
      then Error "final_extensions: check_offeredPsks_identities_list_bytesize failed"
      else if not (Parsers.OfferedPsks.check_offeredPsks_binders_list_bytesize binders)
      then Error "final_extensions: check_offeredPsks_binders_list_bytesize failed"
      else begin
        let ke = ({ Parsers.OfferedPsks.identities = pskidentities; Parsers.OfferedPsks.binders = binders; }) in
        if
          Parsers.ClientHelloExtension.check_clientHelloExtension_CHE_pre_shared_key_bytesize ke
        then
          Correct ([Parsers.ClientHelloExtension.CHE_psk_key_exchange_modes psk_kex] @
            (if edi then [Parsers.ClientHelloExtension.CHE_early_data ()] else []) @
            [Parsers.ClientHelloExtension.CHE_pre_shared_key ke]
          )
        else Error "final_extensions: check_preSharedKeyClientExtension_bytesize failed"
      end
    else
      Correct [Parsers.ClientHelloExtension.CHE_psk_key_exchange_modes [Parsers.PskKeyExchangeMode.Psk_ke; Parsers.PskKeyExchangeMode.Psk_dhe_ke]]
  | _ -> Correct []

let write_extensions
  (cfg: CFG.miTLSConfig) (edi: bool) (l: list Parsers.ResumeInfo13.resumeInfo13) (now: U32.t)
: Tot (result Parsers.ClientHelloExtensions.clientHelloExtensions)
= match final_extensions cfg edi l now with
  | Error e -> Error e
  | Correct fe ->
    if Parsers.ClientHelloExtensions.check_clientHelloExtensions_list_bytesize fe
    then Correct fe
    else Error "write_extensions: out of bounds"

let total_count = 1048576ul

let rec test
  (cfg: CFG.miTLSConfig) (edi: bool) (l: list Parsers.ResumeInfo13.resumeInfo13) (now: U32.t)
: FStar.All.ML unit
=
    FStar.IO.print_uint32 now;
    begin match write_extensions cfg edi l now with
    | Error e ->
      FStar.IO.print_string " error"
    | Correct fe ->
      let s = Parsers.ClientHelloExtensions.clientHelloExtensions_serializer32 fe in
      FStar.IO.print_string " correct, first byte is ";
      FStar.IO.print_uint8 (FStar.Bytes.get s 0ul)
    end;
    FStar.IO.print_newline ();
    if now `U32.lt` total_count
    then test cfg edi l (now `U32.add` 1ul)

let _ =
  let cfg = {
    Parsers.MiTLSConfig.min_version = Parsers.KnownProtocolVersion.Constraint_TLS_1p2 ();
    Parsers.MiTLSConfig.max_version = Parsers.KnownProtocolVersion.Constraint_TLS_1p3 ();
    Parsers.MiTLSConfig.is_quic = Parsers.Boolean.B_false;
    Parsers.MiTLSConfig.cipher_suites = [];
    Parsers.MiTLSConfig.custom_extensions = [];
  } in
  test cfg true [] 0ul
