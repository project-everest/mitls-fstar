module Negotiation

/// Negotiates the TLS parameters for connection establishment, based
/// on the local configuration, the peer's hello message and
/// extensions, the optional HelloRetryRequest roundtrip, and
/// callbacks to the application.

// We are refactoring this module in state-passing style, using ad-hoc
// state types between the negotiation steps. In particular, [mode]
// will be split into simpler, more precise types.

open FStar.Error
open FStar.Bytes

open Mem
open TLSError
open TLSInfo
open TLS.Callbacks
open TLSConstants

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module HSM = HandshakeMessages
module CH = Parsers.ClientHello
module SH = Parsers.RealServerHello
module HRR = Parsers.HelloRetryRequest

open Extensions // for its aggregated datatypes

#reset-options "--using_facts_from '* -LowParse'"

(**
  Debugging flag.
  F* normalizer will erase debug prints at extraction when set to false.
*)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("NGO| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_NGO then print else (fun _ -> ())


// tracing; hopefully extracted only in debug-mode. 

val string_of_list: 
  #a:Type0 -> f: (a -> string) -> string -> xs: list a -> Tot string (decreases (xs)) 
let rec string_of_list #a f s xs = 
  match xs with 
  | [] -> s^"]"
  | [x] -> s^" "^f x^"]" 
  | x::xs -> string_of_list f (s^" "^f x) xs

let string_of_keyShare (x:keyShareEntry) = string_of_namedGroup (tag_of_keyShareEntry x)
let string_of_ciphersuite x = string_of_cipherSuite (name_of_cipherSuite x)
let string_of_ciphersuites xs = string_of_list string_of_ciphersuite "[" xs 
let string_of_signatureSchemes xs = string_of_list string_of_signatureScheme "[" xs

module LP = LowParse.Low.Base
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

#reset-options

// 19-05-17 Sample low-level printer for namedGroupList. We will need
// plenty of the same, we still don't know what to automate.

let print_namedGroupList
  #rrel #rel sl pos
= let _ = namedGroupList_count sl pos in
  let pos' = namedGroupList_jumper sl pos in
  print "[";
  LP.print_list namedGroup_jumper
    (fun #rrel #rel sl pos ->
      let s = namedGroup_reader sl pos in
      print (string_of_namedGroup s);
      let pos1 = namedGroup_jumper sl pos in
      if pos1 <> pos' then print " ")
    sl
    (pos `U32.add` 2ul)
    pos';
  print "]"

#reset-options "--using_facts_from '* -LowParse'"


let string_of_namedGroups xs = string_of_list string_of_namedGroup "[" xs
let string_of_keyShares xs = string_of_list string_of_keyShare "[" xs
let string_of_che  x = string_of_extensionType (tag_of_clientHelloExtension x)
let string_of_hrre x = string_of_extensionType (tag_of_hRRExtension x)
let string_of_she  x = string_of_extensionType (tag_of_serverHelloExtension x)
let string_of_ee  x = string_of_extensionType (tag_of_encryptedExtension x)
let string_of_ches xs = string_of_list string_of_che "[" xs
let string_of_hrres xs = string_of_list string_of_hrre "[" xs
let string_of_shes xs = string_of_list string_of_she "[" xs
let string_of_ees xs = string_of_list string_of_ee "[" xs
let string_of_ciphersuitenames xs = string_of_list string_of_cipherSuite "[" xs
let string_of_hrrs x = string_of_extensionType (tag_of_serverHelloExtension x)


(* Negotiation: HELLO sub-module *)
type ri = cVerifyData * sVerifyData

type resumption_offer_12 = // part of resumeInfo
  | OfferNothing
  | OfferTicket of b:bytes{ length b <> 0 }
  | OfferSid of b:bytes { length b <> 0 }
// type resumption_mode_12 (o: resumption_offer_12) = b:bool { OfferNothing? o ==> b = false }

// let valid_offer ch = True
// There is a pure function computing a ClientHello from an offer (minus the PSK binders)
// type offer = ch:HandshakeMessages.ch { valid_offer ch }


// Boilerplate code for accessing individual extensions

val find_client_extension: 
  filter: (clientHelloExtension -> bool) -> 
  o:offer -> 
  option (e:clientHelloExtension{filter e}) 

let find_client_extension filter o = 
  List.Tot.find filter o.CH.extensions

let find_client_extension_aux env filter o =
  List.Helpers.find_aux env filter o.CH.extensions

let find_supported_versions o : option supportedVersions =
  match find_client_extension CHE_supported_versions? o with
  | None -> None
  | Some (CHE_supported_versions vs) -> Some vs

let find_signature_algorithms o : option signatureSchemeList =
  match find_client_extension CHE_signature_algorithms? o with
  | None -> None
  | Some (CHE_signature_algorithms algs) -> Some algs

let find_signature_algorithms_cert o : option signatureSchemeList =
  match find_client_extension CHE_signature_algorithms_cert? o with
  | None -> None
  | Some (CHE_signature_algorithms_cert algs) -> Some algs

let find_cookie o =
  match find_client_extension CHE_cookie? o with
  | None -> None
  | Some (CHE_cookie c) -> Some c

// finding the pre-shared keys in ClientHello
let find_pske o : option offeredPsks =
  match find_client_extension CHE_pre_shared_key? o with
  | None -> None
  | Some (CHE_pre_shared_key psks) -> Some psks

let find_psk_key_exchange_modes o =
  match find_client_extension CHE_psk_key_exchange_modes? o with
  | None -> []
  | Some (CHE_psk_key_exchange_modes l) -> l

let find_sessionTicket o =
  match find_client_extension CHE_session_ticket? o with
  | None -> None
  | Some (CHE_session_ticket b) -> Some b

let find_clientPske o =
  match find_client_extension CHE_pre_shared_key? o with
  | None -> None
  | Some (CHE_pre_shared_key e) -> Some e

let find_serverSupportedVersions (ses: serverHelloExtensions): option protocolVersion = 
  match List.Tot.find SHE_supported_versions? ses with
  | None -> None
  | Some (SHE_supported_versions spv) -> Some spv

let find_serverPske sh =
  match List.Tot.find SHE_pre_shared_key? sh.SH.extensions with
  | None -> None
  | Some (SHE_pre_shared_key idx) -> Some (UInt16.v idx)    

let find_supported_groups o =
  match find_client_extension CHE_supported_groups? o with
  | None -> None
  | Some (CHE_supported_groups gns) -> Some gns

// wrong result type? keep the extension contents? 
let find_key_shares (o:offer) : list pre_share =
  match find_client_extension CHE_key_share? o with
  | None -> []
  | Some (CHE_key_share ks) -> CommonDH.validate_many ks

let find_serverKeyShare sh : option pre_share =
  match List.find SHE_key_share? sh.SH.extensions with
  | None -> None
  | Some (SHE_key_share ks) -> CommonDH.validate ks

let find_early_data o =
  match find_client_extension CHE_early_data? o with
  | None -> false 
  | Some (CHE_early_data ()) -> true

let find_server_extension filter sh =
  List.Tot.find filter sh.SH.extensions

let is_resumption12 m =
  not (is_pv_13 m.n_protocol_version)  &&
  m.n_sessionID = m.n_offer.CH.session_id

let is_cacheable12 m =
  not (is_pv_13 m.n_protocol_version)  &&
  ( let sid = m.n_sessionID in
    sid <> m.n_offer.CH.session_id &&
    sid <> empty_bytes)

(*
let ns_step (#r:role) (#cfg:config)
  (ns:negotiationState r cfg) (ns':negotiationState r cfg) =
  match ns, ns' with
  | C_Init nonce, C_Offer offer -> nonce == offer.CH.random
  | C_Offer offer, C_Mode mode -> mode.n_offer == offer
  | C_Offer _, C_Complete _ _ -> True
  | C_Mode _, C_WaitFinished2 _ _ -> True
  | C_Mode _, C_Complete _ _ -> True
  | S_Init _, S_ClientHello _ _ -> True
  | S_ClientHello _ _, S_Mode _ _ -> True
  | _, _ -> ns == ns'

// used? worth the trouble? 
let ns_rel (#r:role) (#cfg:config)
  (ns:negotiationState r cfg) (ns':negotiationState r cfg) =
  ns_step ns ns' \/
  (exists ns0. ns_step ns ns0 /\ ns_step ns0 ns')

let ns_step_lemma #r #cfg (ns0 ns1: negotiationState r cfg): Lemma 
  (requires ns_step ns0 ns1) 
  (ensures ns_rel ns0 ns1) = ()
*)

let rec find_ticket12 
  (acc:option (psk_identifier * t:Ticket.ticket{Ticket.Ticket12? t})) 
  (r: list (psk_identifier * Ticket.ticket)) :
  Tot (option (psk_identifier * t:Ticket.ticket{Ticket.Ticket12? t})) (decreases r) 
=
  match r with   
  | [] -> acc
  | (tid, t) :: r -> find_ticket12 (if Ticket.Ticket12? t then Some (tid, t) else acc) r

let rec filter_ticket13 
  (acc:list (psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t}))
  (r: list (psk_identifier * Ticket.ticket)) :
  Tot (list (psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t})) (decreases r) 
=
  match r with 
  | [] -> List.Tot.rev acc //why?
  | (tid, t) :: r -> filter_ticket13 (if Ticket.Ticket13? t then (tid, t)::acc else acc) r

let rec ticket13_pskinfo 
  (acc:list (psk_identifier * pskInfo))
  (r:list (psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t})): // refinement required for Some?.v below
  Tot (list (psk_identifier * pskInfo)) (decreases r) =
  match r with
  | [] -> List.Tot.rev acc
  | (tid, t) :: r -> ticket13_pskinfo ((tid, Some?.v (Ticket.ticket_pskinfo t))::acc) r

// imported from Extensions 

/// High-level extensions offered by the Client, with plenty of
/// intermediate functions for their implementation refinements.

// skipping inline_for_extraction, to improve readability of C code

let keyshares cfg (ks: option clientHelloExtension_CHE_key_share): list clientHelloExtension = 
  match cfg.max_version, ks with
  | TLS_1p3, Some ks -> [CHE_key_share ks]
  | _,_              -> [] 

// 19-05-17 Experiment using a lower QD-generated [config] representation.
module CFG = Parsers.MiTLSConfig
let keyshares_new cfg (ks: option clientHelloExtension_CHE_key_share): list clientHelloExtension = 
  match Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.max_version, ks with
  | TLS_1p3, Some ks -> [CHE_key_share ks]
  | _,_              -> [] 


//TODO make serverName_bytesize transparent (for all sums)
assume val sz_Sni_host_name: dns: Parsers.HostName.hostName -> Lemma(
  serverName_bytesize (Sni_host_name dns) == 3 + Bytes.length dns)
  [SMTPat (serverName_bytesize (Sni_host_name dns))]

//TODO either 2 lemmas or a transparent function. 
(*
assume val sz_serverNameList_list: sns: list Parsers.ServerName.serverName -> Lemma(
  serverNameList_list_bytesize sns == (
  match sns with 
  | [] -> 0
  | x::xs -> serverName_bytesize x + serverNameList_list_bytesize xs ))
*)
assume val sz_serverNameList_list_nil: squash(
  serverNameList_list_bytesize [] == 0
)

assume val sz_serverNameList_list_cons: x:serverName -> xs: list Parsers.ServerName.serverName -> Lemma(
  serverNameList_list_bytesize (x::xs) == serverName_bytesize x + serverNameList_list_bytesize xs )
  [SMTPat (serverNameList_list_bytesize (x::xs))]

//TODO make transparent 
assume val sz_serverNameList: sns: list Parsers.ServerName.serverName -> Lemma(
  let l = serverNameList_list_bytesize sns in
  ( (1 <= l /\ l <= 65535) ==> serverNameList_bytesize sns == 2 + l))
  [SMTPat (serverNameList_list_bytesize sns)]

//TODO make transparent 
assume val sz_CHE_server_name: sns: Parsers.ServerNameList.serverNameList -> Lemma(
  let l = serverNameList_bytesize sns in 
  ( (0 <= l /\ l <= 65535) ==> clientHelloExtension_bytesize (CHE_server_name sns) == 3 + l))
  [SMTPat (clientHelloExtension_bytesize (CHE_server_name sns))]


#reset-options

let sni cfg: list clientHelloExtension = 
  match cfg.peer_name with 
  | None     -> []
  | Some dns -> [CHE_server_name [Sni_host_name dns]] 

let sni_new cfg: list clientHelloExtension = 
  match cfg.CFG.peer_name with
  | CFG.Peer_name_b_false _  -> []
  | CFG.Peer_name_b_true dns -> [CHE_server_name [Sni_host_name dns]] 

let alpn_extension cfg: list clientHelloExtension = 
  match cfg.alpn with 
  | Some al -> [CHE_application_layer_protocol_negotiation al] 
  | None    -> []

let alpn_extension_new cfg: list clientHelloExtension =
  match cfg.CFG.alpn with
  | CFG.Alpn_b_false _ -> []
  | CFG.Alpn_b_true al -> [CHE_application_layer_protocol_negotiation al]

let ticket_extension o: list clientHelloExtension = 
  match o with 
  | Some t -> [CHE_session_ticket t]
  | None   -> []

// Include extended_master_secret when resuming
let ems_extension cfg: list clientHelloExtension = 
  if cfg.extended_master_secret then [CHE_extended_master_secret ()] else []

let ems_extension_new cfg: list clientHelloExtension =
  match cfg.CFG.extend_master_secret with
  | Parsers.Boolean.B_false -> []
  | Parsers.Boolean.B_true -> [CHE_extended_master_secret ()]

let sigalgs_extension cfg: list clientHelloExtension = 
  // TLS 1.3#23: we never include signature_algorithms_cert, as it
  // is not yet enabled in our API; hence sigAlgs are used both for
  // TLS signing and certificate signing.
  [CHE_signature_algorithms 
    (assume False; // unprovable list bytesize due to double vlbytes
    cfg.signature_algorithms)]

module LPS = LowParse.SLow.Base

let sigalgs_extension_new cfg: Tot (result (list clientHelloExtension)) =
  if check_clientHelloExtension_CHE_signature_algorithms_bytesize cfg.CFG.signature_algorithms
  then Correct [CHE_signature_algorithms cfg.CFG.signature_algorithms]
  else fatal Internal_error "sigalgs_extension: check_CHE_signature_algorithms_bytesize failed"

let ec_extension cfg: list clientHelloExtension  = 
//  if List.Tot.existsb isECDHECipherSuite (list_valid_cs_is_list_cs cfg.TLSConstants.cipher_suites) 
  if List.Tot.existsb isECDHECipherSuite cfg.cipher_suites
  then [CHE_ec_point_formats [Uncompressed]]
  else []

inline_for_extraction
let isECDHECipherSuite_new (cs: Parsers.CipherSuite.cipherSuite) : Tot bool =
  match cipherSuite_of_name cs with
  | Some cs -> isECDHECipherSuite cs
  | _ -> false

let ec_extension_new cfg: list clientHelloExtension  = 
//  if List.Tot.existsb isECDHECipherSuite (list_valid_cs_is_list_cs cfg.TLSConstants.cipher_suites) 
  if List.Tot.existsb isECDHECipherSuite_new cfg.CFG.cipher_suites
  then [CHE_ec_point_formats [Uncompressed]]
  else []

#reset-options "--using_facts_from '* -LowParse'"

// We define these functions at top-level so that Kremlin can compute their pointers
// when passed to higher-order functions.
// REMARK: could use __proj__MkpskInfo__item__allow_psk_resumption, but it's a mouthful.
private let allow_psk_resumption x = x.allow_psk_resumption
private let allow_dhe_resumption x = x.allow_dhe_resumption
private let allow_resumption ((_,x):PSK.pskid * pskInfo) =
  x.allow_psk_resumption || x.allow_dhe_resumption

private let send_supported_groups cs = isDHECipherSuite cs || CipherSuite13? cs


// Annoying plumbing... the intrinsic property on lengths is required to prove a bound on the resulting list type.
private let rec list_valid_ng_is_list_ng (l:CommonDH.supportedNamedGroups) : Tot (r:CommonDH.namedGroups{List.length r = List.length l}) (decreases l) =
  match l with
  | [] -> []
  | [tl] -> [tl]
  | hd :: tl -> 
      // assert(List.Tot.for_all CommonDH.is_supported_group tl);
      let tl: CommonDH.supportedNamedGroups = tl in 
      hd :: list_valid_ng_is_list_ng tl
// We fill binders with placeholders to use QD clientHelloextensions_serializer32

private let compute_binder_ph (pski:pskInfo) : Tot pskBinderEntry =
  let CipherSuite13 _ h = pski.early_cs in
  let len : UInt32.t = Hacl.Hash.Definitions.hash_len h in
  assume (32 <= U32.v len /\ U32.v len <= 256); // hash must not be MD5 or SHA1...
  FStar.Bytes.create len 0uy

#push-options "--z3rlimit 16"

(* a rewrite of the compute_binder_ph spec *)

let compute_binder_ph_new (t: Parsers.TicketContents13.ticketContents13) : Tot pskBinderEntry =
  let pski = Ticket.ticketContents13_pskinfo t in
  let CipherSuite13 _ h = pski.early_cs in
  let len : UInt32.t = Hacl.Hash.Definitions.hash_len h in
  assert (32 <= U32.v len /\ U32.v len <= 256); // hash must not be MD5 or SHA1...
  FStar.Bytes.create len 0uy

(* sanity-check: this rewrite behaves no differently than the old code *)

let compute_binder_ph_new_correct (t: Parsers.TicketContents13.ticketContents13) : Lemma
  (compute_binder_ph_new t == compute_binder_ph (Ticket.ticketContents13_pskinfo t))
= ()

#pop-options

let supported_group_extension cfg: list clientHelloExtension =   
  if List.Tot.existsb send_supported_groups cfg.cipher_suites
  then [CHE_supported_groups ( (* list_valid_ng_is_list_ng *) cfg.named_groups)] 
  else [] 

inline_for_extraction
let send_supported_groups_new cs = 
  match CipherSuite.cipherSuite_of_name cs with
  | None -> false
  | Some cs -> send_supported_groups cs

let supported_group_extension_new cfg: list clientHelloExtension =   
  if List.Tot.existsb send_supported_groups_new cfg.CFG.cipher_suites
  then [CHE_supported_groups cfg.CFG.named_groups] 
  else [] 

#reset-options "--using_facts_from '* -LowParse'"

private val obfuscate_age: UInt32.t -> list (PSK.pskid * pskInfo) -> list pskIdentity
let rec obfuscate_age now = function
  | [] -> []
  | (id, ctx) :: t ->
    let age = FStar.UInt32.((now -%^ ctx.time_created) *%^ 1000ul) in
    {identity = PSK.name id;
    obfuscated_ticket_age = PSK.encode_age age ctx.ticket_age_add} ::
    obfuscate_age now t

module PR = Parsers.ResumeInfo

(* this is how obfuscate_age should be rewritten *)

let obfuscate_age_new (now: U32.t) (tk: Parsers.ResumeInfo13.resumeInfo13) : Tot pskIdentity =
    let age = FStar.UInt32.((now -%^ tk.Parsers.ResumeInfo13.ticket.Parsers.TicketContents13.creation_time) *%^ 1000ul) in
    {identity = tk.Parsers.ResumeInfo13.identity; obfuscated_ticket_age = PSK.encode_age age tk.Parsers.ResumeInfo13.ticket.Parsers.TicketContents13.age_add}

(* this function and this lemma are here only to convince oneself that obfuscate_age_resumeInfo13 is not doing anything fundamentally different from obfuscate_age *)

noextract
let list_pskid_pskinfo_of_list_resumeinfo13 (l: list Parsers.ResumeInfo13.resumeInfo13) : Tot (list (PSK.pskid * pskInfo)) = List.Tot.map
  (fun r -> let i = r.Parsers.ResumeInfo13.identity in
         let t = r.Parsers.ResumeInfo13.ticket in
         (admit(), Some?.v (Ticket.ticketContents_pskinfo (Parsers.TicketContents.T_ticket13 t))))
  l
(*
let rec obfuscate_age_obfuscate_age_new
  (now: U32.t)
  (l: list Parsers.ResumeInfo13.resumeInfo13)
: Lemma
  (obfuscate_age now (list_pskid_pskinfo_of_list_resumeinfo13 l) == List.Tot.map (obfuscate_age_new now) l)
= match l with
  | [] -> ()
  | r :: q ->
    let i = r.Parsers.ResumeInfo13.identity in
    let t = r.Parsers.ResumeInfo13.ticket in
//    assume (PSK.registered_psk i);
    obfuscate_age_obfuscate_age_new now q
*)

let final_extensions cfg edi psks now: list clientHelloExtension =
  match cfg.max_version with
  | TLS_1p3 -> (
    if List.Tot.filter allow_resumption psks <> [] then
      let (pskids, pskinfos) : list PSK.pskid * list pskInfo = List.Tot.split psks in
      let psk_kex =
        ((if List.Tot.existsb allow_psk_resumption pskinfos then [Psk_ke] else []) <: (l: list _ { List.Tot.length l <= 1 } )) @ 
        ((if List.Tot.existsb allow_dhe_resumption pskinfos then [Psk_dhe_ke] else []) <: (l: list _ { List.Tot.length l <= 1 } )) in
      assume (List.Tot.length psk_kex >= 1);
      let binders = List.Tot.map compute_binder_ph pskinfos in
      let pskidentities = obfuscate_age now psks in
      assume (let x = offeredPsks_identities_list_bytesize pskidentities in 7 <= x /\ x <= 65535);
      assume (let x = offeredPsks_binders_list_bytesize binders in 33 <= x /\ x <= 65535);
      let ke = ({ identities = pskidentities; binders = binders }) in
      assume (let x = Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_bytesize ke in 0 <= x /\ x <= 65535);
      [CHE_psk_key_exchange_modes psk_kex] @
      (if edi then [CHE_early_data ()] else []) @
      // MUST BE LAST
      [CHE_pre_shared_key ke]
    else
      [CHE_psk_key_exchange_modes [Psk_ke; Psk_dhe_ke]] )
  | _ -> []
// 19-01-19 We may need better dummy binders! 

(* a rewrite of the spec of final_extensions *)

noextract
let allow_psk_resumption_new (r: Parsers.ResumeInfo13.resumeInfo13) : Tot bool =
  (Ticket.ticketContents13_pskinfo r.Parsers.ResumeInfo13.ticket).allow_psk_resumption

noextract
let allow_dhe_resumption_new (r: Parsers.ResumeInfo13.resumeInfo13) : Tot bool =
  (Ticket.ticketContents13_pskinfo r.Parsers.ResumeInfo13.ticket).allow_dhe_resumption

#reset-options

(*
noextract
let final_extensions_alt
  (cfg: CFG.miTLSConfig) (edi: bool) (l: list Parsers.ResumeInfo13.resumeInfo13) (now: U32.t)
: Tot (result (list clientHelloExtension))
= match Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.max_version with
  | TLS_1p3 ->
    let allow_psk_resumption = List.Tot.existsb allow_psk_resumption_new l in
    let allow_dhe_resumption = List.Tot.existsb allow_dhe_resumption_new l in
    if allow_psk_resumption || allow_dhe_resumption
    then
      let psk_kex =
        (if allow_psk_resumption then [Psk_ke] else []) @ (if allow_dhe_resumption then [Psk_dhe_ke] else [])
      in
      let binders = List.Tot.map (fun r -> compute_binder_ph_new r.Parsers.ResumeInfo13.ticket) l in
      let pskidentities = List.Tot.map (obfuscate_age_new now) l in
      ke <-- (
        if not (check_offeredPsks_identities_list_bytesize pskidentities)
        then fail (fatal Internal_error "final_extensions: check_offeredPsks_identities_list_bytesize failed")
        else if not (check_offeredPsks_binders_list_bytesize binders) 
        then fail (fatal Internal_error "final_extensions: check_offeredPsks_binders_list_bytesize failed")
        else return ({ identities = pskidentities; binders = binders; }) );
      exts <- (
        if
          check_clientHelloExtension_CHE_pre_shared_key_bytesize ke
        then
          return ([CHE_psk_key_exchange_modes psk_kex] @
            (if edi then [CHE_early_data ()] else []) @
            [CHE_pre_shared_key ke]
          )
        else fail (fatal Internal_error "final_extensions: check_preSharedKeyClientExtension_bytesize failed"))
      end
    else
      Correct [CHE_psk_key_exchange_modes [Psk_ke; Psk_dhe_ke]]
  | _ -> Correct []
*)

noextract
let final_extensions_new
  (cfg: CFG.miTLSConfig) (edi: bool) (l: list Parsers.ResumeInfo13.resumeInfo13) (now: U32.t)
: Tot (result (list clientHelloExtension))
= match Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.max_version with
  | TLS_1p3 ->
    let allow_psk_resumption = List.Tot.existsb allow_psk_resumption_new l in
    let allow_dhe_resumption = List.Tot.existsb allow_dhe_resumption_new l in
    if allow_psk_resumption || allow_dhe_resumption
    then
      let psk_kex =
        (if allow_psk_resumption then [Psk_ke] else []) @ (if allow_dhe_resumption then [Psk_dhe_ke] else [])
      in
      let binders = List.Tot.map (fun r -> compute_binder_ph_new r.Parsers.ResumeInfo13.ticket) l in
      let pskidentities = List.Tot.map (obfuscate_age_new now) l in
      if not (check_offeredPsks_identities_list_bytesize pskidentities)
      then fatal Internal_error "final_extensions: check_offeredPsks_identities_list_bytesize failed"
      else if not (check_offeredPsks_binders_list_bytesize binders)
      then fatal Internal_error "final_extensions: check_offeredPsks_binders_list_bytesize failed"
      else begin
        let ke = ({ identities = pskidentities; binders = binders; }) in
        if
          check_clientHelloExtension_CHE_pre_shared_key_bytesize ke
        then
          Correct ([CHE_psk_key_exchange_modes psk_kex] @
            (if edi then [CHE_early_data ()] else []) @
            [CHE_pre_shared_key ke]
          )
        else fatal Internal_error "final_extensions: check_preSharedKeyClientExtension_bytesize failed"
      end
    else
      Correct [CHE_psk_key_exchange_modes [Psk_ke; Psk_dhe_ke]]
  | _ -> Correct []

(* TODO: sanity-check wrt. old final_extensions *)

#reset-options "--using_facts_from '* -LowParse'"

/// The extensions included in ClientHello
/// (specification + high-level implementation)
/// 
val prepareClientExtensions:
  cfg: TLSConstants.config ->
  bool -> // EDI (Nego checks that PSK is compatible)
  option clientHelloExtension_CHE_session_ticket -> // session_ticket
  option (cVerifyData * sVerifyData) ->
  option clientHelloExtension_CHE_key_share ->
  list (PSK.pskid * pskInfo) ->
  now: UInt32.t -> // for obfuscated ticket age
  l: result (list clientHelloExtension) 

let prepareClientExtensions 
  (cfg: config)
  edi
  ticket 
  ri 
  ks 
  psks 
  now
= 
  match Negotiation.Version.support cfg with 
  | Error z -> Error z 
  | Correct supported_versions -> Correct(

  // 18-12-22 TODO cfg.safe_renegotiation is ignored? 

  Extensions.clientHelloExtensions_of_unknownExtensions cfg.custom_extensions @ 
  (* Always send supported extensions.
     The configuration options will influence how strict the tests will be *)
  (* let cri = *)
  (*    match ri with *)
  (*    | None -> FirstConnection *)
  (*    | Some (cvd, svd) -> ClientRenegotiationInfo cvd in *)
  (* let res = [E_renegotiation_info(cri)] in *)
  supported_versions ::
  keyshares cfg ks @
  sni cfg @
  alpn_extension cfg @ 
  ticket_extension ticket @
  ems_extension cfg @ 
  sigalgs_extension cfg @ 
  ec_extension cfg @ 
  supported_group_extension cfg @ 
  final_extensions cfg edi psks now )
  // let res = List.Tot.rev res in
  // assume (List.Tot.length res < 256);  // JK: Specs in type config in TLSInfo unsufficient

/// The extensions included in ClientHello
/// (specification + high-level implementation)
/// 
val prepareClientExtensions_new:
  cfg: CFG.miTLSConfig ->
  bool -> // EDI (Nego checks that PSK is compatible)
  option clientHelloExtension_CHE_session_ticket -> // session_ticket
(*  option (cVerifyData * sVerifyData) -> *)
  option clientHelloExtension_CHE_key_share ->
  list Parsers.ResumeInfo13.resumeInfo13 ->
  now: UInt32.t -> // for obfuscated ticket age
  l: result (list clientHelloExtension) 

let prepareClientExtensions_new
  cfg
  edi
  ticket 
(*  ri  *)
  ks 
  psks 
  now
= begin match Negotiation.Version.support_new cfg with
  | Error z -> Error z
  | Correct supported_versions ->
    begin match sigalgs_extension_new cfg with
    | Error z -> Error z
    | Correct sigalgs_extension ->
      begin match final_extensions_new cfg edi psks now with
      | Error z -> Error z
      | Correct final_extensions ->
        Correct begin
          // 18-12-22 TODO cfg.safe_renegotiation is ignored? 
          Extensions.clientHelloExtensions_of_unknownExtensions cfg.CFG.custom_extensions @
          (* Always send supported extensions.
             The configuration options will influence how strict the tests will be *)
          (* let cri = *)
          (*    match ri with *)
          (*    | None -> FirstConnection *)
          (*    | Some (cvd, svd) -> ClientRenegotiationInfo cvd in *)
          (* let res = [E_renegotiation_info(cri)] in *)
          supported_versions ::
          keyshares_new cfg ks @
          sni_new cfg @
          alpn_extension_new cfg @ 
          ticket_extension ticket @
          ems_extension_new cfg @ 
          sigalgs_extension @ 
          ec_extension_new cfg @ 
          supported_group_extension_new cfg @ 
          final_extensions 
        end
      end
    end
  end

  // let res = List.Tot.rev res in
  // assume (List.Tot.length res < 256);  // JK: Specs in type config in TLSInfo unsufficient

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

let prepareClientExtensions_inverse pv cs sres sren sigAlgs namedGroups ri ks:
  Lemma(
    matchExtensions (prepareClientExtensions pv cs sres sren sigAlgs namedGroups ri ks) =
    (pv, cs, sres, sren, sigAlgs, namedGroups, ri, ks)) = ()
*)

/// 18-12-22 The plan is to patiently lower each of the functions
/// above with precise chained pre- and post- and to rely on a lemma
/// for committing writes and concatenations. Possibly with
/// intermediate lemmas bounding their wire sizes, based on safe
/// static overapproximations.
///
/// Meanwhile, we will serialize32 the enclosing ClientHello. 

(*
let write_supported_versions slice pos cfg = 
  assert(pos + 5 <slice.max);
  if cfg.max_version = TLS_1p3 then 
    let pos = start_write_E_supported_version slice pos in 
    let pos = write_TLS_1p3 slice pos in 
    let pos = if cfg.min_version = TLS1p2 then write_TLS1p2 slice pos else pos in 
    let pos = finish_write_E_supported_Versions slice pos in 
    pos 
  else pos

(...) 

let write_ClientExtensions slice pos cfg edi ticket ri ks psks now = 
  let pos = write_CustomExtensions slice pos cfg in 
  let pos = write_supported_versions slice pos cfg in 
  (...)
  let pos = write_final_extensions slice pos cfg edi psks now in 
  pos 

*)



/// Commenting out support for TLS 1.2 renegotiation
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

#reset-options "--using_facts_from '* -LowParse'"


/// Negotiating server extensions.
/// pure code as spec & implementation so far.
/// was in Extensions.

// respond to client extensions in two steps
private val server_clientExtension:
  protocolVersion -> 
  config -> 
  cipherSuite -> 
  option (cVerifyData * sVerifyData) -> 
  option (pski:nat {pski < 65536}) -> 
  option Extensions.serverHelloExtension_SHE_key_share -> 
  bool -> 
  clientHelloExtension -> option serverHelloExtension

private val encrypted_clientExtension:
  protocolVersion -> 
  config -> 
  cipherSuite -> 
  option (cVerifyData * sVerifyData) -> 
  option (pski:nat {pski < 65536}) -> 
  option Extensions.serverHelloExtension_SHE_key_share -> 
  bool -> 
  clientHelloExtension -> option encryptedExtension 

//19-01-22  recheck what this does
let alpn_response cfg cal: option serverHelloExtension_SHE_application_layer_protocol_negotiation = 
  match cfg.alpn with
  | None -> None
  | Some sal ->
    let common = List.Helpers.filter_aux sal List.Helpers.mem_rev cal in
    match common with
    | a :: _ -> Some (assume False;[a])
    | _ -> None

let server_name_response snl resuming = 
  if resuming 
  then None // RFC 6066 page 6
  else (
    match List.Tot.tryFind Sni_host_name? snl with
    | Some name -> Some () // acknowledge client's choice
    | _ -> None )

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2 --initial_fuel 2 --initial_ifuel 2"
let server_clientExtension pv cfg cs ri pski ks resuming ce =
  if pv = TLS_1p3 then 
    match ce with 
    | CHE_supported_versions _ -> Some (SHE_supported_versions pv)
    | CHE_key_share _ ->  Option.mapTot SHE_key_share ks // ks should be in one of client's groups
    | CHE_pre_shared_key _ ->
      if pski = None then None
      else
        let x = Some?.v pski in
        Some (SHE_pre_shared_key (UInt16.uint_to_t x))
    | _ -> None
  else 
    match ce with
    | CHE_application_layer_protocol_negotiation cal -> 
      Option.mapTot SHE_application_layer_protocol_negotiation (alpn_response cfg cal)
    | CHE_server_name snl -> Option.mapTot SHE_server_name (server_name_response snl resuming)
    | CHE_extended_master_secret ms ->
      if cfg.extended_master_secret then Some (SHE_extended_master_secret ()) else None
    | CHE_ec_point_formats ec_point_format_list -> // REMARK: ignores client's list
      Some (SHE_ec_point_formats [Uncompressed])
    | CHE_session_ticket b ->
      if cfg.enable_tickets 
      then Some (SHE_session_ticket ()) // TODO we may not always want to refresh the ticket
      else None
    | _ -> None // TODO: recheck completeness
#pop-options

let encrypted_clientExtension pv cfg cs ri pski ks resuming ce = 
  match ce with
//19-01-22 RECHECK RFC
//| CHE_server_name snl -> Option.mapTot EE_server_name (server_name_response snl resuming)
//| CHE_max_fragment_length 
  | CHE_supported_groups named_group_list -> Some (EE_supported_groups cfg.named_groups) // purely informative
//| CHE_use_srtp
//| CHE_heartbeat
  | CHE_application_layer_protocol_negotiation cal -> 
    Option.mapTot EE_application_layer_protocol_negotiation (alpn_response cfg cal)
//| CHE_client_certificate_type
//| CHE_server_certificate_type
  | CHE_early_data b -> // EE
    if Some? cfg.max_early_data && pski = Some 0 
    then Some (EE_early_data ()) 
    else None
  | _ -> None

// 19-01-05 boring, and not tail-recursive, use an iterator instead?
// we defer the length check on the result
let rec server_clientExtensions pv cfg cs ri pski ks resuming (ches:list clientHelloExtension) =
  match ches with
  | [] -> []
  | che::ches ->
    let es = server_clientExtensions pv cfg cs ri pski ks resuming ches in 
    match server_clientExtension pv cfg cs ri pski ks resuming che with
    | None -> es
    | Some e -> e::es
let rec encrypted_clientExtensions pv cfg cs ri pski ks resuming (ches:list clientHelloExtension) =
  match ches with
  | [] -> []
  | che::ches ->
    let es = encrypted_clientExtensions pv cfg cs ri pski ks resuming ches in 
    match encrypted_clientExtension pv cfg cs ri pski ks resuming che with
    | None -> es
    | Some e -> e::es

(* dead code since we don't support SSL3.
     begin
     match pv with
       | SSL_3p0 ->
          let cre =
              if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV csl then
                 Some [E_renegotiation_info (FirstConnection)] //, {ne_default with ne_secure_renegotiation = RI_Valid})
              else None //, ne_default in
          in Correct cre
*)

type tickets = list (psk_identifier * Ticket.ticket) 

#push-options "--z3rlimit 50"
let rec unseal_tickets 
  (acc: tickets)
  (l:list (psk_identifier * ticket_seal)): 
  St tickets 
  = match l with
  | [] -> List.Tot.rev acc
  | (tid, seal) :: r -> (
    let acc: tickets =
      match Ticket.check_ticket true seal with
      | Some t -> (tid, t) :: acc
      | None -> trace ("WARNING: failed to unseal the session data for ticket "^print_bytes tid^" (check sealing key)"); acc in
    unseal_tickets acc r )

let create region r cfg nonce =
  let resume = unseal_tickets [] cfg.use_tickets in
  assume False; //18-12-16 ??
  let resume: resumeInfo = 
    find_ticket12 None resume, 
    filter_ticket13 [] resume in
  match r with
  | Client ->
    let state = Mem.ralloc region (C_Init nonce) in
    NS cfg resume nonce state
  | Server ->
    let state = Mem.ralloc region (S_Init nonce) in
    NS cfg resume nonce state

// a bit too restrictive: use a single Hash in any given offer
let hashAlg m =
  //18-12-16 TODO actually a partial function, requiring a private refinement!
  assume False;
  verifyDataHashAlg_of_ciphersuite m.n_cipher_suite

let kexAlg m =
  if is_pv_13 m.n_protocol_version then
    (match m.n_pski with
    | None -> Kex_ECDHE
    | Some _ ->
      if Some? m.n_server_share then Kex_PSK_ECDHE
      else Kex_PSK)
  else (
    //18-12-16 TODO partial pattern matching
    assume(CipherSuite? m.n_cipher_suite); 
    let CipherSuite kex _ _ = m.n_cipher_suite in kex )

let aeAlg m =
  TLSConstants.get_aeAlg m.n_cipher_suite

//let is_che_ems che = (tag_of_clientHelloExtension che = Extended_master_secret)
//let is_she_ems che = (tag_of_serverHelloExtension che = Extended_master_secret)
let emsFlag mode =
  if is_pv_13 mode.n_protocol_version then
    true
  else (
    List.existsb CHE_extended_master_secret? mode.n_offer.CH.extensions &&
    (mode.n_server_extensions = [] || 
     List.existsb SHE_extended_master_secret? mode.n_server_extensions)
  )

// used only for TLS 1.2. FIXME: properly negotiate
let chosenGroup mode =
  match kexAlg mode with
  | Kex_PSK_DHE
  | Kex_DHE -> CommonDH.group_of_namedGroup CommonDH.Ffdhe2048
  | Kex_PSK_ECDHE
  | Kex_ECDHE -> CommonDH.group_of_namedGroup CommonDH.Secp256r1

let zeroRTToffer o = find_early_data o

let zeroRTT mode =
  find_early_data mode.n_offer &&
  Some? mode.n_pski &&
  List.Tot.existsb SHE_early_data? mode.n_server_extensions

let sendticket_12 mode =
  List.Tot.existsb SHE_session_ticket? mode.n_server_extensions

let resume_12 mode =
  not (is_pv_13 mode.n_protocol_version) &&
  Some? (find_sessionTicket mode.n_offer) &&
  length mode.n_offer.CH.session_id > 0 &&
  mode.n_sessionID = mode.n_offer.CH.session_id

let local_config #region #role ns = ns.cfg
let nonce        #region #role ns = ns.nonce
let resume       #region #role ns = ns.resume

let getOffer #region #role ns =
  match !ns.state with
  | C_Offer offer -> offer
  | _ -> admit() //18-12-16 TODO incomplete pattern, add a pre?

let getMode #region #role ns =
  match !ns.state with
  | C_Mode mode
  | C_WaitFinished2 mode _
  | C_Complete mode _
  | S_ClientHello mode _
  | S_Mode mode _
  | S_Complete mode _ ->  mode
  | _ -> admit() //18-12-16 TODO incomplete pattern, add a pre?

let version #region #role ns =
  let x = !ns.state in
//  TLS_1p3
  match x with
  | C_Init _ -> ns.cfg.max_version
  | C_Offer _ -> ns.cfg.max_version
  | C_WaitFinished1 _ -> ns.cfg.max_version
  | C_Mode mode
  | C_WaitFinished2 mode _
  | C_Complete mode _ -> mode.n_protocol_version
  | S_Init _ -> ns.cfg.max_version
  | S_ClientHello mode _
  | S_Mode mode _
  | S_Complete mode _ -> mode.n_protocol_version
//19-01-23 slow TC??

(*
val getSigningKey: #a:Signature.alg -> #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST (option (Signature.skey a))
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let getSigningKey #a #region #role ns =
  Signature.lookup_key #a ns.cfg.private_key_file
*)

private
let const_true _ = true

let sign #region #role ns tbs =
  // 18-10-29 review usage of Bad_certificate to report signing error
  // TODO(adl) make the pattern below a static pre-condition
  assume False;
  let S_Mode mode (Some (cert, sa)) = !ns.state in
  match cert_sign_cb ns.cfg.cert_callbacks cert sa tbs with
  | None -> fatal Bad_certificate (perror __SOURCE_FILE__ __LINE__ "Failed to sign with selected certificate.")
  | Some sigv ->
    Correct HSM.({algorithm = sa; signature = sigv})

(* CLIENT *)

// effect ST0 (a:Type) = ST a (fun _ -> True) (fun h0 _ h1 -> modifies_none h0 h1)
// val map_ST: ('a -> ST0 'b) -> list 'a -> ST0 (list 'b)
// let rec map_ST f x = match x with
//   | [] -> []
//   | a::tl -> f a :: (
//     assume False; //18-12-16 TODO
//     map_ST f tl)

// let i_psk_info i = (i, PSK.psk_info i)

(*
 * AR: 1/27: this seems wip, since the precondition does not have liveness of ns.state etc.
 *)

// #set-options "--admit_smt_queries true" 
// TR: added according to AR's remark above
// CF: restored; let's keep at least high-level code under CI

let client_offer cfg nonce ks resume now =
  let ticket12, sid =
    match fst resume, cfg.enable_tickets, cfg.min_version with
    | _, _, TLS_1p3 -> 
      // Don't bother sending 1.2 session_ticket when offering 1.3 
      None, empty_bytes 

    | Some (tid, _), true, _ ->
      // Similar to what OpenSSL does, when we offer a 1.2 ticket
      // we send the hash of the ticket as SID to disambiguate the state machine
      // FIXME Cannot compute hash in Tot
      //let sid = Hashing.compute Hashing.Spec.SHA2_256 t
      let sid = if length tid <= 32 then tid else fst (split tid 32ul) in
      Some (assume False;tid), sid

    | None, true, _ -> Some (assume False; empty_bytes), empty_bytes
    | _ -> None, empty_bytes in
  let pskinfo = 
    assume false; //18-12-16 FIXME 
    ticket13_pskinfo [] (snd resume) in
  // Don't offer EDI if there is no PSK or first PSK doesn't have ED enabled
  let compatible_psk =
    match pskinfo with
    | (_, i) :: _ -> i.allow_early_data // Must be the first PSK
    | _ -> false in
  match prepareClientExtensions 
      cfg 
      (compatible_psk && Some? cfg.max_early_data)
      ticket12
      None //: option (cVerifyData * sVerifyData)
      ks
      pskinfo
      now
  with 
  | Error z -> Error z 
  | Correct extensions -> Correct CH.({
    version = minPV TLS_1p2 cfg.max_version; // legacy for 1.3
    random = nonce;
    session_id = sid;
    cipher_suites = nameList_of_cipherSuites cfg.TLSConstants.cipher_suites;
    // This file is reconstructed from ch_cipher_suites in HandshakeMessages.clientHelloBytes;
    compression_methods = [NullCompression];
    extensions = (assume False; extensions)
  })

#reset-options

//19-05-04 ?
val client_offer_new:
  cfg: CFG.miTLSConfig -> 
  nonce:TLSInfo.random -> 
  ks: option clientHelloExtension_CHE_key_share ->
  resume: Parsers.ResumeInfo.resumeInfo ->
  now:UInt32.t ->
  Tot (result offer)

let client_offer_new cfg nonce ks resume now =
  if Nil? cfg.CFG.cipher_suites
  then
    // TODO: remove this case by strengthening the type of cfg.cipher_suites
    fatal Internal_error "computeOffer: not enough cipher_suites in cfg"
  else
    let ticket12, sid =
      match resume.Parsers.ResumeInfo.resumeInfo12, cfg.CFG.enable_tickets, Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.min_version with
      | _, _, TLS_1p3 -> None, empty_bytes // Don't bother sending session_ticket
      // Similar to what OpenSSL does, when we offer a 1.2 ticket
      // we send the hash of the ticket as SID to disambiguate the state machine
      | Parsers.ResumeInfo_resumeInfo12.ResumeInfo12_b_true ({ Parsers.ResumeInfo12.identity = tid }), Parsers.Boolean.B_true, _ ->
        // FIXME Cannot compute hash in Tot
        //let sid = Hashing.compute Hashing.Spec.SHA2_256 t
        let sid = if length tid <= 32 then tid else fst (split tid 32ul) in
        Some tid, sid
      | Parsers.ResumeInfo_resumeInfo12.ResumeInfo12_b_false _, Parsers.Boolean.B_true, _ -> Some empty_bytes, empty_bytes
      | _ -> None, (empty_bytes <: FStar.Bytes.bytes)
    in
    let pskinfo = resume.Parsers.ResumeInfo.resumeInfo13 in
    // Don't offer EDI if there is no PSK or first PSK doesn't have ED enabled
    let compatible_psk =
      match pskinfo with
      | ({ Parsers.ResumeInfo13.ticket = i }) :: _ -> (Ticket.ticketContents13_pskinfo i).allow_early_data // Must be the first PSK
      | _ -> false
    in
    match prepareClientExtensions_new
      cfg 
      (compatible_psk && CFG.Max_early_data_b_true? cfg.CFG.max_early_data)
      ticket12
(*      None //: option (cVerifyData * sVerifyData) *)
      ks
      pskinfo
      now
    with
    | Error z -> Error z
    | Correct extensions ->
      if check_clientHelloExtensions_list_bytesize extensions
      then
        Correct CH.({
          version = minPV TLS_1p2 (Parsers.KnownProtocolVersion.tag_of_knownProtocolVersion cfg.CFG.max_version); // legacy for 1.3
          random = nonce;
          session_id = sid;
          cipher_suites = cfg.CFG.cipher_suites;
          compression_methods = [NullCompression];
          extensions = extensions;
        })
      else
        fatal Internal_error "computeOffer: check_clientHelloExtensions_list_bytesize failed"

let client_ClientHello #region ns oks =
  match !ns.state with
  | C_Init _ ->
      trace(
        if (match ticket13_pskinfo [] (snd ns.resume) with
        | (_, i) :: _ -> i.allow_early_data && Some? ns.cfg.max_early_data // Must be the first PSK
        | _ -> false)
        then "Offering a PSK compatible with 0-RTT"
        else "No PSK or 0-RTT disabled");

      let now = UInt32.uint_to_t (FStar.Date.secondsFromDawn()) in
      match client_offer ns.cfg ns.nonce oks ns.resume now with 
      | Error z -> Error z 
      | Correct offer -> (
      trace ("offering client extensions "^string_of_ches offer.CH.extensions);
      trace ("offering cipher suites "^string_of_ciphersuitenames offer.CH.cipher_suites);
      ns.state := C_Offer offer;
      Correct offer )

private
let choose_extension (s:share) (e:clientHelloExtension) =
  match e with
  // 2018.03.08 SZ: TODO We must Update PSK extension if present
  // See https://tools.ietf.org/html/draft-ietf-tls-tls13-26#section-4.1.2
  // | CHE_pre_shared_key psk -> FIXME() update ticket_age, remove incompatible PSKs
  | CHE_early_data _ -> None
  | CHE_key_share sl ->
    let (| g, gx |) = s in
    let ks = CommonDH.format gx in 
    assume(Parsers.KeyShareEntry.keyShareEntry_bytesize ks <= 65531); 
      // to be proved as a post of format in CommonDH? we could use a tighter bound to prevent dynamic failures
      // assert(let l = Parsers.KeyShareClientHello.keyShareClientHello_list_bytesize [ks] in 0 <= l /\ l <= 65535);
      // assert(let l = Parsers.KeyShareClientHello.keyShareClientHello_bytesize [ks] in 0 <= l /\ l <= 65535);
    Some (CHE_key_share [ks])
  | e -> Some e

let group_of_hrr = TLS.Cookie.find_keyshare

#push-options "--admit_smt_queries true"
let client_HelloRetryRequest ch1 hrr s =
  let open Parsers.HelloRetryRequest in
  let { version = _; session_id = sid; cipher_suite = cs; extensions = el } = hrr in
  let old_shares = find_key_shares ch1 in
  let old_psk = match find_pske ch1 with None -> [] | Some pskl -> pskl.identities in
  let ext' = List.Helpers.choose_aux s choose_extension ch1.CH.extensions in
  let ext', no_cookie : list clientHelloExtension * bool =
    match List.Tot.find HRRE_cookie? el with
    | Some (HRRE_cookie c) -> CHE_cookie c :: ext', false
    | None -> ext', true in
  if sid <> ch1.CH.session_id then
    fatal Illegal_parameter "mismatched session ID in HelloRetryRequest"
  else
   begin
    assume(clientHelloExtensions_list_bytesize ext' <= 65535);
    let ch2 = {ch1 with CH.extensions = ext'} in
    let ri = (hrr, old_shares, old_psk) in
    Correct(ri, ch2)
   end
#pop-options

let check_retry ch1 ri sh =
  // FIXME(adl) check SH is consistent with HRR
  Correct ()

// usable on both sides; following https://tlswg.github.io/tls13-spec/#rfc.section.4.2.1
// vs Nego.Version? 

(*
  Checks that the protocol version in ClientHello is
  within the range of versions supported by the server configuration
  and outputs the negotiated version if true
*)

(* --- subsumed by Negotiation.Version 
// we might also check no proposal is below min_pv
private let rec filter_unknown_versions: list protocolVersion' -> list protocolVersion = function
  | Unknown_protocolVersion _::vs -> filter_unknown_versions vs 
  | v::vs -> v::filter_unknown_versions vs
  | [] -> []

let offered_versions min_pv (o: offer): result (l: list protocolVersion {l <> []}) =
  match find_supported_versions o with
  | Some vs ->
      let known = filter_unknown_versions vs in 
      if known <> [] 
      then Correct known 
      else fatal Protocol_version "protocol version negotiation: proposal does not include any known version"
  | None -> // use legacy offer
      match o.CH.version, min_pv with
      | TLS_1p0, TLS_1p0 -> Correct [TLS_1p0]
      | TLS_1p1, TLS_1p0 -> Correct [TLS_1p2; TLS_1p1]
      | TLS_1p1, TLS_1p1 -> Correct [TLS_1p1]
      | TLS_1p2, TLS_1p0 -> Correct [TLS_1p2; TLS_1p1; TLS_1p0]
      | TLS_1p2, TLS_1p1 -> Correct [TLS_1p2; TLS_1p1]
      | TLS_1p2, TLS_1p2 -> Correct [TLS_1p2]
      | _, _ -> fatal Protocol_version "protocol version negotation: bad legacy proposal"
let is_client13 (o:offer) =
  match offered_versions TLS_1p3 o with
  | Correct vs -> List.Tot.existsb is_pv_13 vs
  | Error _ -> false
*)



(**
  For use in negotiating the ciphersuite, takes two lists and
  outputs the first ciphersuite in list2 that also is in list
  one and is a valid ciphersuite, or [None]
*)
private
let is_cs_in_l (l1, sa) s =
  if CipherSuite? s then
    List.mem (name_of_cipherSuite s) l1 && 
    CipherSuite?._1 s = Some sa
  else false

(**
  For use in ensuring the result from negotiate is a Correct
  ciphersuite with associated kex, sig and ae algorithms,
  and throws an error if No ciphersuites were supported in both lists
*)
val negotiateCipherSuite: 
  cfg:config -> 
  pv:protocolVersion -> // unused?
  ccs: list cipherSuiteName -> 
  sa:sigAlg -> 
  result (valid_cipher_suite)
let negotiateCipherSuite cfg pv ccs sa =
  assume False; //18-12-16 TODO cipherSuiteName vs valid_cipher_suite + weakening of refinement under option constructor
  match List.Helpers.find_aux (ccs, sa) is_cs_in_l cfg.cipher_suites with
  | None    -> fatal Internal_error (perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")
  | Some cs -> Correct cs

(*
val negotiateGroupKeyShare13
  config ->
  list extension ->
  Tot (result (option (kexAlg * namedGroup * option share))
let rec negotiateGroupKeyShare cfg pv exts =
  // first fetch the two relevant extensions
  let supported, keyshares =
    match o.ch_extensions with
    | None -> None, None
    | Some es ->
      ( match List.Tot.find Extensions.E_supported_groups? es with
        | None -> None
        | Some (Extensions.E_supported_groups gs) -> Some gs)
      ( match List.Tot.find Extensions.E_key_share? es with
        | None -> None
        | Some (Extensions.E_key_share (CommonDH.ClientKeyShare gl)) ->
            let filter (g, gx) =
              List.Tot.mem g cfg.named_groups &&
              ( (SEC? g && (kex = Kex_ECDHE || kex = Kex_PSK_ECDHE)) ||
                (FFDHE? g && (kex = Kex_DHE || kex = Kex_PSK_DHE)) ) in
            Some(match List.Tot.filter filter gl)) in

  if pv = TLS_1p3 then
    match keyshares with
    | None -> Error(AD_decode_error, "no supported group or key share extension found")
    | Some [] -> Error(AD_decode_error, "no shared group between client and server config")
    | Some (share::_) -> Correct (Some share)
    // todo support HRR depending on supported_groups

  else if kex = Kex_ECDHE && Some? supported then
    let filter g = SEC? g && List.Tot.mem g cfg.named_groups in
    let gs = List.Tot.filter

    Correct(Some (match List.Tot.filter filter gs), None)

    match supported with

    | Some
  List.Tot.existsb E_supported_groups? exts


  | Some exts when (kex = Kex_ECDHE && List.Tot.existsb E_supported_groups? exts) ->
    let Some (E_supported_groups gl) = List.Tot.find E_supported_groups? exts in

    let filter g =
    (match List.Tot.filter filter gl with
    | gn :: _ -> Correct (Some gn, None)
    | [] -> Error(AD_decode_error, "no shared curve configured"))
  | _ ->
    let filter x =
      (match kex with | Kex_DHE -> FFDHE? x | Kex_ECDHE -> SEC? x | _ -> false) in
    if kex = Kex_DHE || kex = Kex_ECDHE then
      (match List.Tot.filter filter cfg.named_groups with
      | gn :: _ -> Correct (Some gn, None)
      | [] -> Error(AD_decode_error, "no valid group is configured for the selected cipher suite"))
    else Correct(None, None)
*)



(* TODO (adl):
   The negotiation of renegotiation indication is incorrect,
   Needs to be consistent with clientToNegotiatedExtension
*)



private let illegal msg = fatal Illegal_parameter (perror __SOURCE_FILE__ __LINE__ msg)
private let unsupported msg = fatal Unsupported_extension (perror __SOURCE_FILE__ __LINE__ msg)

// 18-12-23 various checks on the received server extensions (still
// missing e.g. check on mandatory responses)

let same_she_che_type (s: serverHelloExtension) (c: clientHelloExtension) = 
  tag_of_clientHelloExtension c = tag_of_serverHelloExtension s 

let same_che_che_type (c0 c1: clientHelloExtension) = 
  tag_of_clientHelloExtension c0 = tag_of_clientHelloExtension c1 

// 19-06-12 Although we have different types for SE and EE, the same
// extension may occur in SE for 1.2 and EE for 1.3. We could be more
// restrictive depending on [pv] here.
let accept_ServerExtension resuming (ces: clientHelloExtensions) (se: serverHelloExtension): result unit =
  if not (List.Helpers.exists_b_aux se same_she_che_type ces) then
    unsupported "received unsolicited server extension"
  else 
    match se with
    | SHE_server_name _ -> 
        // RFC 6066, bottom of page 6, when resuming a session, the
        // server MUST NOT include a server_name extension in the
        // server hello
        if resuming then unsupported "server sent SNI acknowledge in resumption"
        else correct () 
      
    | SHE_application_layer_protocol_negotiation sal -> 
        // The wire format is too permissive, hence this additional check
        if List.length sal <> 1 then illegal "Multiple ALPN selected by server"
        else correct() 
        
    | SHE_supported_groups named_group_list ->
        if resuming then unsupported "server sent supported groups in resumption"
        else correct()
        
    | SHE_ec_point_formats _  // can be sent in resumption, apparently (RFC 4492, 5.2)
    | SHE_pre_shared_key _    // bound check later in  Nego
    | SHE_supported_versions _ // validated earlier 
    | SHE_session_ticket _
    | SHE_extended_master_secret _
    | SHE_key_share _
    | SHE_Unknown_extensionType _ _ -> correct()
    | _ -> 
        fatal Handshake_failure (perror __SOURCE_FILE__ __LINE__ ("unhandled server extension: " ^ string_of_she se))
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

/// Client validation of the ServerHello extensions;
/// returns the negotiated protocol version .
/// 
val accept_ServerExtensions:
  resuming: bool ->
//option (cVerifyData * sVerifyData) ->
  clientHelloExtensions ->
  serverHelloExtensions ->
  result unit
let rec accept_ServerExtensions resuming ces ses = 
  match ses with
  | [] -> Correct () 
  | se ::  ses -> 
      match accept_ServerExtension resuming ces se with 
      | Error z   -> Error z 
      | Correct _ -> accept_ServerExtensions resuming ces ses 

(* now in Negotiation.Version:

(* Confirms that the version negotiated by the server was:
  - within the range specified by client config AND
  - is not an unnecessary downgrade AND
  - is not a newer version than offered by the client
*)
val acceptableVersion: 
  config -> 
  protocolVersion -> 
  TLSInfo.random -> bool

let acceptableVersion cfg pv sr =
  // we statically know that the offered versions are compatible with our config
  // (we may prove e.g. acceptableVersion pv ==> pv in offered_versions
  pv `geqPV` cfg.min_version &&
  cfg.max_version `geqPV` pv &&
  not (isSentinelRandomValue cfg.max_version pv sr)

val negotiateVersion:
  config ->
  protocolVersion ->
  option (list extension) ->
  TLSInfo.random -> 
  result protocolVersion

// 18-12-23 separate protocol-version negotiation, usable as spec & implementation.
let negotiateVersion cfg pv ses sr = 
  if pv = TLS_1p3 then 
    illegal "cannot negotiate TLS 1.3 explicitly" 
  else 
  if pv = SSL_3p0 && Some? ses then 
    illegal "received extensions in SSL 3.0 ServerHello" 
  else 
    let chosen = 
      match find_serverSupportedVersions ses with
      | None    -> pv // old style
      | Some pv -> pv in
    if chosen = TLS_1p3 && pv <> TLS_1p2 then 
      illegal "extension-based version negotiation requires TLS 1.2 apparent version"  
    else 
    if acceptableVersion cfg chosen sr then correct pv 
    else
      illegal "client did not offer this protocol version"
*) 


(** Confirms that the ciphersuite negotiated by the server was:
  - consistent with the client config;
  - TODO: [s_cs] is supported by the protocol version (e.g. no GCM with
    TLS<1.2).
 BD: Removed that the ciphersuite is acceptable given CHELO
 given that the clientOffer is prepared with the entire list
 of valid cipher suites in the client config
*)
val acceptableCipherSuite: config -> protocolVersion -> valid_cipher_suite -> Tot bool
let eq_cs (cs:valid_cipher_suite) x = x = cs
let acceptableCipherSuite cfg spv cs =
  List.Helpers.exists_b_aux cs eq_cs cfg.cipher_suites

let is_share_eq (g:CommonDH.group) (s:keyShareEntry) =
  CommonDH.group_of_namedGroup (tag_of_keyShareEntry s) = Some g

let matching_share 
  (cext:clientHelloExtensions)
  (g:CommonDH.group) :
  option share // i.e. (g:CommonDH.group & CommonDH.share g) 
=
  match List.Tot.find CHE_key_share? cext with
  | None -> None
  | Some (CHE_key_share l) ->
    match List.Helpers.find_aux g is_share_eq l with
    | _       -> None
    | Some ks -> CommonDH.validate ks

let accept_pski offer sh: result (option (pski offer)) =
  match find_clientPske offer, find_serverPske sh with
  | Some offered, Some idx ->
    if idx < List.length offered.identities then
      Correct (Some #(pski offer) idx) // REMARK: we can't check yet consistency with early_data in EE
    else
      fatal Illegal_parameter (perror __SOURCE_FILE__ __LINE__ "PSK out of bounds")
  | None, Some _ ->
    fatal Illegal_parameter (perror __SOURCE_FILE__ __LINE__ "PSK not offered")
  | _, _ -> Correct None


// experimenting with lightweight error propagation

inline_for_extraction
let return (#a:Type) (x:a) : result a = Correct x

inline_for_extraction
let fail (#a:Type) z : result a = Error z

let cs_pv pv = 
  cs: cipherSuite { (TLS_1p2? pv /\ CipherSuite? cs) \/ (TLS_1p3? pv /\ CipherSuite13? cs) }
    
let ciphersuite_accept cfg pv sh : result (cs_pv pv) 
= 
  match cipherSuite_of_name sh.SH.cipher_suite with 
  | None -> fatal Illegal_parameter (perror __SOURCE_FILE__ __LINE__ "Server cipherSuite") 
  | Some cs -> 
    if acceptableCipherSuite cfg pv cs then 
      if (TLS_1p2? pv && CipherSuite? cs) || (TLS_1p3? pv && CipherSuite13? cs) 
      then 
        correct cs 
      else 
        fatal Internal_error "Statically Excluded"
    else
      fatal Illegal_parameter (perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")

let accept_ServerHello cfg offer sh = 
  [@inline_let]
  let r = m:mode{Mode?.n_offer m == offer} in 
  pv <-- Negotiation.Version.accept cfg sh; 
  cs <-- ciphersuite_accept cfg pv sh;
  pski <-- accept_pski offer sh;  
  let ssid = sh.SH.session_id in
  let resume = 
    ssid = offer.CH.session_id && 
    length offer.CH.session_id > 0 in
  let ses  = sh.SH.extensions in
  _ <-- accept_ServerExtensions resume offer.CH.extensions ses;
  let sr = sh.SH.random in
  let m:r = (
  match cs with
  // | NullCipherSuite | SCSV -> fatal #r Internal_error "Statically Excluded"
  | CipherSuite kex sa ae -> 
      Mode
        offer
        None
        pv
        sr
        ssid
        cs
        None // pski
        ses
        None // n_encrypted_extensions (not yet reeived)
        None // n_server_share; unknwon before SKE is received
        NoRequest // n_client_cert_request
        None // n_server_cert
        None // n_client_share
        
  | CipherSuite13 ae ha -> (
      //assert(pv != TLS_1p3);
      let server_share, client_share = 
        match find_serverKeyShare sh with 
        | None -> (None, None) 
        | Some (| g, gy |) ->
          let server_share = (|g, gy|) in
          let client_share = matching_share offer.CH.extensions g in
          (Some server_share, client_share) 
      in 
      Mode
        offer
        None // n_hrr
        pv
        sr
        ssid
        cs
        pski
        ses
        None // n_encrypted_extensions (not yet received)
        server_share
        NoRequest // n_client_cert_request
        None // n_server_cert
        client_share 
        )) in 
  return #(m:mode{Mode?.n_offer m == offer}) m

let client_ServerHello #region ns sh =
  match !ns.state with
  | C_Offer offer -> (
    match accept_ServerHello ns.cfg offer sh with 
    | Error z -> Error z 
    | Correct mode -> 
      ns.state := C_Mode mode;
      Correct mode )

//19-01-04 should we check that we have a matching client share? 

(* ---------------- signature stuff, to be removed from Handshake -------------------- *)

// why an option? why csr instead of the two nonces? we'll need to prove some injectivity property, which seems to rely on nonces not being all zeros

#push-options "--z3rlimit 30"
let to_be_signed pv role csr tbs =
  if pv = TLS_1p3 then 
    let pad = Bytes.create_ 64 32uy in
    let ctx = bytes_of_string (
      match role with
      | Server -> "TLS 1.3, server CertificateVerify"
      | Client -> "TLS 1.3, client CertificateVerify" ) in
    assume(
      Bytes.length ctx = 33 /\
      Bytes.length (abyte 0z) = 1); // TODO bytes/string libraries
    pad @| ctx @| abyte 0z @| tbs
  else
    Some?.v csr @| tbs
#pop-options 

// 19-01-06 we can't use || and && because of Kremlin's let bindings :(
inline_for_extraction let kor a b = if a then b else true 
inline_for_extraction let kand a b = if a then b else false 

private let matches_sigHashAlg_of_signatureScheme sa (alg: signatureScheme) =
  is_supported_signatureScheme alg && (
  let (sa',_) = sigHashAlg_of_signatureScheme alg in
  sa' = sa )

(* was: 
private let matches_sigHashAlg_of_signatureScheme ((osa,sa):(option signatureScheme * _)) (alg: signatureScheme) =
  // exclude it in locally-issued offer?
  // (None? osa || Some?.v osa = alg) &&
  // not (SIG_UNKNOWN? alg) && 
  // ( let (sa',_) = sigHashAlg_of_signatureScheme alg in
  //   sa' = sa // TODO filter_ske_salg12 osa alg 
  // )
  (None? osa `kor` (Some?.v osa = alg)) `kand` (
  not (SIG_UNKNOWN? alg) `kand` 
  ( let (sa',_) = sigHashAlg_of_signatureScheme alg in
    sa' = sa // TODO filter_ske_salg12 osa alg 
  ) )
*)

// Clients verifies the server's choice of signature scheme

let filter_ske_salg12 (sa: signatureScheme) (sa': signatureScheme) = 
    if sa <> sa'
    then fatal Handshake_failure "Signature algorithm negotiation failed"
    else correct sa

#push-options "--z3rlimit 200"
let accept_salg12 mode (sa:signatureScheme)
  : result signatureScheme  =
  let pv = mode.n_protocol_version in 
  assume(
    pvcs pv mode.n_cipher_suite /\ 
    ~ (Unknown_protocolVersion? pv) /\ //19-04-19 TODO mismatch with TLSonstants
    pv <> TLS_1p3); //18-12-16 TODO preconditions
  let ha0 = sessionHashAlg pv mode.n_cipher_suite in
  match sigAlg_of_ciphersuite mode.n_cipher_suite with 
  | Error z -> Error z 
  | Correct sa' -> (
    match mode.n_protocol_version with
    | TLS_1p0 | TLS_1p1 | SSL_3p0 -> 
      filter_ske_salg12 sa (signatureScheme_of_sigHashAlg sa' ha0)
    | TLS_1p2 ->
    match find_signature_algorithms mode.n_offer with
    | None -> filter_ske_salg12 sa (signatureScheme_of_sigHashAlg sa' ha0)
    | Some algs -> 
      (match List.Helpers.find_aux sa' matches_sigHashAlg_of_signatureScheme algs with
        | Some sa -> Correct sa 
        | None -> fatal Handshake_failure "Signature algorithm negotiation failed" ))

// TLS 1.2 only. Sets [server_share; client_cert_request; server_cert] in mode. 
// Too restrictive for RSA? 

// annoying differently refined bytes, to be reviewed
private let coerce_asncert (x:Parsers.ASN1Cert.aSN1Cert): cert_repr = x
private let coerce_crt crt = List.Tot.map coerce_asncert crt 

let client_ServerKeyExchange #region ns crt kex ske ocr =
  if version ns <> TLS_1p2 then 
    fatal Internal_error "TLS 1.2 only" //19-04-19 TODO make it static
  else 
  let open Parsers.KeyExchangeAlgorithm in
  let open Parsers.ServerKeyExchange in
  match kex with
  | Dh_anon | Rsa ->
    fatal Handshake_failure (perror __SOURCE_FILE__ __LINE__ "Illegal message")

  | Dhe | Ecdhe ->
    let sig, tbs = match ske with
      | Ske_dhe dh ->
        let open Parsers.SignedDHParams in
	let open Parsers.SignedDHKeyExchange in
	dh.signature, signedDHParams_serializer32 dh.params
      | Ske_ecdhe ecdh ->
        let open Parsers.ServerECDHParams in
	let open Parsers.SignedECDHKeyExchange in
	ecdh.signature, serverECDHParams_serializer32 ecdh.params in
    if length tbs > 128 then 
      fatal Internal_error "tbs is too large" // our parsers tolerate much larger ones?!
    else 
    let open Parsers.Signature in
    match CommonDH.parse_partial (kex=Ecdhe) tbs with
    | Error z -> Error z
    | Correct (gy, _) ->
    let mode = getMode ns in
    match accept_salg12 mode sig.algorithm with
    | Error z -> Error z 
    | Correct sa ->
      let csr = ns.nonce @| mode.n_server_random in
      let tbs = to_be_signed mode.n_protocol_version Server (Some csr) tbs in

      // verify both the certicate chain and the signature using the leaf verification key. 
      //let h = get() in assert(inv ns h);
      let valid = cert_verify_cb ns.cfg.cert_callbacks (coerce_crt crt) sa tbs sig.signature_payload in
      //let h = get() in assume(inv ns h);
      trace ("ServerKeyExchange signature: " ^ (if valid then "Valid" else "Invalid"));
      if not valid then
        fatal Handshake_failure (perror __SOURCE_FILE__ __LINE__ "Failed to check SKE signature")
      else
        let ocr = match ocr with | None -> NoRequest | Some cr -> CertRequest12 cr in
        let scert = Some (Cert.chain_up crt, sa) in
        let        Mode offer hrr pv sr sid cs pski sext _ _ _ _                  gx = mode in
        let mode = Mode offer hrr pv sr sid cs pski sext None (Some gy) ocr scert gx in
        let ccert = None in // TODO
        ns.state := C_WaitFinished2 mode ccert;
        Correct mode

let clientComplete_13 #region ns ee optCertRequest optServerCert optCertVerify digest =
  trace "Nego.clientComplete_13";
  match !ns.state with
  | C_Mode mode ->
    let pv = TLS_1p3 in // mode.n_protocol_version  
    let ccert = None in
    trace ("Encrypted Extensions "^string_of_ees ee);
    let nego_cb = ns.cfg.nego_callback in
    let uexts = List.Tot.filter EE_Unknown_extensionType? ee in
    // this could be statically excluded from the definition of filtering 
    if not (check_encryptedExtensions_list_bytesize uexts) then 
      fatal Internal_error "encrypted extensions are too large"
    else
    let uexts_bytes = encryptedExtensions_serializer32 uexts in
    trace ("Negotiation callback to process application extensions.");

    // to be simplified (see TLS.Callbacks)
    match nego_cb.negotiate nego_cb.nego_context pv uexts_bytes None with
    | Nego_abort -> fatal Handshake_failure (perror __SOURCE_FILE__ __LINE__ "application requested to abort the handshake")
    | Nego_retry _ -> fatal Internal_error (perror __SOURCE_FILE__ __LINE__ "client application requested a server retry")
    | Nego_accept _ ->
      let validSig, schain =
        match kexAlg mode, optServerCert, optCertVerify, digest with
        | Kex_DHE, Some c, Some cv, Some digest
        | Kex_ECDHE, Some c, Some cv, Some digest -> (
          // TODO ensure that valid_offer mandates signature extensions for 1.3
          let sal = match find_signature_algorithms mode.n_offer with 
          | Some sal -> sal
          | None -> [] in
          let sa = cv.HSM.algorithm in
          let chain = Some (c, sa) in
          let r = 
          if List.Tot.mem sa sal then
            let tbs = to_be_signed pv Server None digest in            
            cert_verify_cb ns.cfg.cert_callbacks
	      (coerce_crt (Cert.chain_down c)) sa tbs cv.HSM.signature,
	    chain
          else false, None in // The server signed with an algorithm we did not offer
          // let h0 = HST.get() in 
          // assert(h0 `HS.contains` ns.state);
          r )
        | Kex_PSK_ECDHE, None, None, None
        | Kex_PSK, None, None, None -> true, None // FIXME recall chain from PSK
        | _ -> false, None
        in
      //19-04-23 TODO where did we lose it? The callbacks are (allegedly) modifies_none 
      let h0 = HST.get() in 
      assume(h0 `HS.contains` ns.state);
      trace ("Certificate & signature 1.3 callback result: " ^ (if validSig then "valid" else "invalid"));
      if validSig then
        let mode = Mode
          mode.n_offer
          mode.n_hrr
          pv
          mode.n_server_random
          mode.n_sessionID
          mode.n_cipher_suite
          mode.n_pski
          mode.n_server_extensions
	  (Some ee)
          mode.n_server_share
          (match optCertRequest with None -> NoRequest | Some cr -> CertRequest13 cr)
          schain
          mode.n_client_share
        in
        ns.state := C_Complete mode ccert;
        Correct mode
      else
        fatal Bad_certificate "Failed to validate signature or certificate"

(* SERVER *)

// The KEX selected by the server, with its parameters. Note that
// PSK_EDH covers two kexes, with or without EDH.
//
// Consider keeping it instead of the server mode
// can we also use it for client accept? 

let names_group_of gns ((| g, _ |): share) = 
  match CommonDH.namedGroup_of_group g with
  | None -> false 
  | Some gn -> List.Tot.mem gn gns

// TODO: strengten property to prove that the share itself is included
// in the offer.
type selected_share cfg offer = 
  s: share { 
    cfg.named_groups `names_group_of` s /\ 
    ( match find_supported_groups offer with
      | Some ngs -> ngs `names_group_of` s 
      | None -> False ) }

let names_cs13 ncss (cs: cipherSuite): bool =
  CipherSuite13? cs && 
  List.Tot.mem (name_of_cipherSuite cs) ncss 

type selected_cs cfg offer = 
  cs: cipherSuite13 { 
    List.Tot.mem cs cfg.cipher_suites /\ 
    offer.CH.cipher_suites `names_cs13` cs }

let is_named_cs cs n : bool = 
  Some cs = cipherSuite_of_name n

let select_cs cfg offer : option (selected_cs cfg offer) = 
  match List.Helpers.find_aux offer.CH.cipher_suites names_cs13 cfg.cipher_suites with 
  | None -> None 
  | Some cs -> 
    assume(List.Tot.mem cs cfg.cipher_suites); // List.find post?
    Some cs

type cs13 server_cert cfg offer =
  | PSK_EDH: 
    j:pski offer -> 
    cks: option (selected_share cfg offer) ->
    cs: selected_cs cfg offer -> cs13 server_cert cfg offer
  | JUST_EDH: 
    cks: selected_share cfg offer -> 
    cs: selected_cs cfg offer { b2t server_cert } -> cs13 server_cert cfg offer

let is_allowed_kex ((info:PSK.pskInfo), (share:bool)) kex = 
  let open TLS.Callbacks in 
  match kex with
  | Psk_dhe_ke -> share && info.allow_dhe_resumption 
  | Psk_ke     -> info.allow_psk_resumption
  | _          -> false 


// The PSK sets the ciphersuite and constrains the kex.
// The ciphersuite must also be offered and acceptable 
let select_psk 
  (cfg:config)
  (o:offer) 
  (g_gx:option (s:selected_share cfg o))
  (server_cert:bool) (* is the server ready to sign? *) 
  (i:pski o) (id:PSK.pskid) (info:PSK.pskInfo): option (cs13 server_cert cfg o)
=
  let cs = info.early_cs in
  if not (List.Tot.mem cs cfg.cipher_suites) then None else 
  if not (o.CH.cipher_suites `names_cs13` cs) then None else
  let kexes = find_psk_key_exchange_modes o in
  match List.Helpers.find_aux (info,Some? g_gx) is_allowed_kex kexes with
  | None -> None 
  | Some Psk_ke -> Some (PSK_EDH i None cs)
  | Some Psk_dhe_ke -> assert (Some? g_gx); Some (PSK_EDH i g_gx cs) 

// heavy-handed? we need to keep the two aligned 
type psks (o:offer) = 
  v: list (option (PSK.pskid & PSK.pskInfo))
  { match find_clientPske o with
    | Some psk -> List.length v == List.length psk.Extensions.identities
    | None     -> List.length v == 0}

//#reset-options "--log_queries"
val compute_cs13_aux 
  (cfg: config)
  (o:offer)
  (psks: psks o) // from the offer, after registration 
  (g_gx:option (s:selected_share cfg o))
  (server_cert:bool) (* is the server ready to sign? *) : 
  i:nat{ i <= List.length psks } (* PSK index to try next *) ->
  Tot (option (cs13 server_cert cfg o)) (decreases ( (List.length psks - i) <: nat ))

#reset-options "--z3rlimit 40"
// to be lowered as a vlbyte loop on psks
let rec compute_cs13_aux cfg o psks g_gx server_cert i : option (cs13 server_cert cfg o)
=
  if i = List.length psks || i >= 65536 then
    if not server_cert then None else 
    match g_gx with
    | None -> None #(cs13 server_cert cfg o)
    | Some x -> 
      match select_cs cfg o with
      | None    -> None 
      | Some cs -> 
         Some (JUST_EDH x cs)
  else
    let choice = 
      match List.Tot.index psks i with 
      | None -> None 
      | Some (id, info) -> select_psk cfg o g_gx server_cert i id info in 
    if Some? choice then choice else
    compute_cs13_aux cfg o psks g_gx server_cert (i+1) 

let group_of_named_group (x:_{Some? (CommonDH.group_of_namedGroup x)}) =
  Some?.v (CommonDH.group_of_namedGroup x)

let share_in_named_group gl (x :share) =
  let (| g, _ |) = x in
  List.Tot.mem g gl

//#set-options "--admit_smt_queries true"

/// selects a "core modes" for TLS 1.3, if any

val compute_cs13:
  cfg: config ->
  o: offer ->
  psks: psks o ->
  shares: list share (* pre-registered *) ->
  server_cert: bool (* is a certificate available for signing? *) ->
  o: option (cs13 server_cert cfg o)
  // the server needs a certificate with JUST_EDH 
  { match o with Some (JUST_EDH _ _) -> server_cert | _ -> True } 


let compute_cs13 cfg o psks shares server_cert =
  // first pick an offered group & share usable for DHE/ECDHE
  // for now the client ordering takes precedence 
  let g_gx = //: option (s:share {cfg.named_groups `names_group_of` s}) =   
    match List.Helpers.find_aux cfg.named_groups names_group_of shares with
    | None -> None 
    | Some s -> 
      match find_supported_groups o with 
      | None -> None
      | Some ngs -> if ngs `names_group_of` s then Some s else None in
  compute_cs13_aux cfg o psks g_gx server_cert 0

/// Negotiation failed, but may still succeed after an HRR: the server
/// selects its preferred group and ciphersuite in those offered by
/// the client.
///
/// We do not check whether the client already provided a share for
/// that group, as otherwise internal negotiation succeeded and the
/// application may decide to retry anyway. Similarly, we do not check
/// whether the server is ready to sign.

(*
let is_g_share (g:CommonDH.namedGroup) (gx: share) = dfst gx = g 
let is_supported_but_not_shared (supported,shares) g = 
  List.Tot.mem supported g &&
  not (List.Tot.exists_b_aux g is_shared shares)
*)
let mem_group gs g = List.Tot.mem #CommonDH.namedGroup g gs 

let compute_hrr cfg o =
  cs <-- (
    match select_cs cfg o with 
    | None -> fatal Handshake_failure "ciphersuite negotiation failed: no acceptable ciphersuite"
    | Some cs -> return cs);
  support <-- (
    match find_supported_groups o with
    | None -> fatal Handshake_failure "ciphersuite negotiation failed: no supported group extension"
    | Some support -> return support); 
  g <-- (
    match List.Helpers.find_aux support mem_group cfg.named_groups with
    | None -> fatal Handshake_failure "ciphersuite negotiation failed: no acceptable group" 
    | Some g -> return g ); 
  let hrr = TLS.Cookie.hrr0 o.CH.session_id cs in 
  let hrr = TLS.Cookie.append_keyshare hrr g in 
  Correct(ServerRetry hrr)


// Registration and filtering of PSK identities
//
// To avoid psk re-indexing, we produce a list of options rather than
// a filtered list; to be revisited to avoid this intermediate list.
let rec filter_psk (l:list pskIdentity)
  : St (r:list (option (PSK.pskid * PSK.pskInfo)) {List.length r = List.length l}) =
  match l with
  | [] -> []
  | ({identity = id; obfuscated_ticket_age = _}) :: t ->
    (match Ticket.check_ticket13 id with
    | Some info -> 
        //19-04-23 should be check_ticket post? 
        assume(not model /\ PSK.non_zero id);
        Some (PSK.coerce id, info) :: (filter_psk t)
//    | None ->
//      (match PSK.psk_lookup id with
//      | Some info -> trace ("Loaded PSK from ticket <"^print_bytes id^">"); Some (id, info) :: filter_psk t
      | None -> trace ("WARNING: the PSK <"^print_bytes id^"> has been filtered"); None :: filter_psk t)
//      )

// Registration of DH shares
let rec register_shares (l:list pre_share): 
  ST (list share)
  (requires fun h0 -> True) 
  (ensures fun h0 r h1 -> B.(modifies loc_none h0 h1)) // TODO framing of registration 
=
  let r = 
  match l with
  | [] -> []
  | (| g, gx |) :: t -> (| g, CommonDH.register_dhi #g gx |) :: register_shares t in
  // 19-06-17 TODO framing of registration 
  assume False; r

let get_sni o =
  match find_client_extension CHE_server_name? o with
  | Some (CHE_server_name ((Sni_host_name sni)::_)) -> sni
  | _ -> empty_bytes
  // 19-04-23 TODO recheck error cases in case we don't understand the extension contents; should we return a result? 

let get_alpn o =
  match find_client_extension CHE_application_layer_protocol_negotiation? o with
  | None -> 
      // 19-04-23 TODO return a result (list can't be empty); requires adapting QUIC API?
      assume False; 
      []
  | Some (CHE_application_layer_protocol_negotiation pl) -> pl

let nego_alpn (o:offer) (cfg:config) : bytes =
  match cfg.alpn with
  | None -> empty_bytes
  | Some sal ->
    match find_client_extension CHE_application_layer_protocol_negotiation? o with
    | None -> empty_bytes
    | Some (CHE_application_layer_protocol_negotiation cal) ->
      match List.Helpers.filter_aux sal List.Helpers.mem_rev cal with
      | a :: _ -> a
      | _ -> empty_bytes

irreducible val computeServerMode12:
  cfg: config ->
  co: offer ->
  serverRandom: TLSInfo.random ->
  ST (result serverMode)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> 
    B.(modifies loc_none h0 h1) /\ 
    ( match r with 
      | Correct (ServerRetry _) -> False // incompatible with TLS 1.2
      | _ -> True )
    )

#push-options "--admit_smt_queries true" 
let computeServerMode12 cfg co serverRandom = 
  let pv = TLS_1p2 in 
  let valid_ticket =
    match find_sessionTicket co with
    | None -> None
    | Some t ->
      // No tickets if client desn't send an SID (too messy)
      if length co.CH.session_id = 0 then None
      else Ticket.check_ticket12 t in
  match valid_ticket with
  | Some (pv, cs, ems, _, _) ->
    Correct (ServerMode 
      (Mode
        co
        None // TODO: no HRR
        pv
        serverRandom
        co.CH.session_id
        cs
        None
	[]
        None // Extensions
        None
        NoRequest
        None
        None) 
      None [])
      
  | None ->
    // Not required anymore? Make sure NullCompression is offered
    if not (List.Tot.mem NullCompression co.CH.compression_methods)
    then fatal Illegal_parameter "Compression is deprecated" else
    let salgs =
      match find_signature_algorithms co with
      | None -> [Unknown_signatureScheme 0xFFFFus; Ecdsa_sha1]
      | Some sigalgs -> List.Helpers.filter_aux cfg.signature_algorithms List.Helpers.mem_rev sigalgs
    in
    match cert_select_cb cfg.cert_callbacks pv (get_sni co) (nego_alpn co cfg) salgs with
    | None -> 
      //18-10-29 review Certificate_unknown; was No_certificate
      fatal Certificate_unknown (perror __SOURCE_FILE__ __LINE__ "No compatible certificate can be selected")
    | Some (cert, sa) ->
      let schain = cert_format_cb cfg.cert_callbacks cert in
      let sig, _ = sigHashAlg_of_signatureScheme sa in
      match negotiateCipherSuite cfg pv co.CH.cipher_suites sig with
      | Error z -> Error z
      | Correct cs -> 
        let CipherSuite kex _ ae = cs in 
        Correct (ServerMode (Mode
          co
          None // no HRR before TLS 1.3
          pv
          serverRandom
          (Random.sample32 32ul)
          cs
          None
          []
          None // Extensions will be filled later
          None // no server key share yet
          NoRequest
          (Some (Cert.chain_up schain, sa))
          None) // no client key share yet for 1.2
        (Some(cert, sa)) [] )
#pop-options 

irreducible val computeServerMode:
  cfg: config ->
  co: offer ->
  serverRandom: TLSInfo.random ->
  ST (result serverMode)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> 
    B.(modifies loc_none h0 h1) /\ 
    ( match r with 
      | Correct (ServerRetry hrr) -> TLS.Cookie.hrr_len hrr <= 16 // leaving enough room for the cookie 
      | _ -> True )
    )
 
#push-options "--z3rlimit 40"
let computeServerMode cfg offer serverRandom =
  match Negotiation.Version.choose cfg offer with
  | Error z -> Error z
  | Correct TLS_1p2 -> computeServerMode12 cfg offer serverRandom 
  | Correct TLS_1p3 -> (
    let h0 = get() in 
    let pske = // Filter and register offered PSKs
      match find_pske offer with
      | Some pske -> filter_psk pske.identities
      | None -> [] in
    let shares = register_shares (find_key_shares offer) in
    let scert =
      match find_signature_algorithms offer with
      | None -> None
      | Some sigalgs ->
        if sigalgs = [] then
	  (trace "No shared signature algorithm, restricting to PSK"; None)
        else 
          cert_select_cb cfg.cert_callbacks TLS_1p3 (get_sni offer) (nego_alpn offer cfg) sigalgs
      in
    //19-06-17 TODO framing of PSK and keyshare registration 
    let h1 = get() in assume(B.(modifies loc_none h0 h1)); 
    match compute_cs13 cfg offer pske shares (Some? scert) with
    | None -> compute_hrr cfg offer 
    | Some r -> (
      // the actual outcome
      let cs, oj, oc, ogx, scert = 
        match r with 
        | PSK_EDH j ogx cs -> 
          trace "Negotiated PSK_EDH key exchange"; // two kexes, depending on ogx
          let ogx = match ogx with Some gx -> Some gx | None -> None in // structural subtyping...
          cs, Some j, None, ogx, None
        | JUST_EDH gx cs -> 
          let Some (cert, sa) = scert in
          trace ("Negotiated Pure EDH key exchange with signature scheme "^string_of_signatureScheme sa);
          let schain = cert_format_cb cfg.cert_callbacks cert in
          cs, None, Some (Cert.chain_up schain, sa), Some gx, scert 
      in
      Correct (ServerMode 
        (Mode
          offer
          None
          TLS_1p3
          serverRandom
          offer.CH.session_id
          cs
          oj 
          []
          None // extensions will be filled in next pass 
          None // no server key share yet
          NoRequest // TODO: n_client_cert_request
          oc
          ogx)
        scert []))) 
#pop-options 

let accum_string_of_pv s pv = s ^ " " ^ string_of_pv pv

let valid_ch2_extension (o1, hrr) (e:clientHelloExtension) =
  match e with
  | CHE_key_share ecl ->
    (match ecl, TLS.Cookie.find_keyshare hrr with
    | [ks], Some ng -> tag_of_keyShareEntry ks = ng
//19-01-21 do we need this case? 
//        | _, None -> (
//          let shares1 = find_key_shares o1 in
//          CommonDH.clientKeyShareBytes shares1 = CommonDH.clientKeyShareBytes ecl)
          | _ -> false)
  | CHE_early_data _ -> false // Forbidden
  | CHE_cookie c -> true // FIXME we will send cookie
      // If we add cookie support we need to treat this case separately
      // | Extensions.E_cookie c -> c = S_HRR?.cookie ns.state
  | e ->
    (match find_client_extension_aux e same_che_che_type o1 with
    | None -> (IO.debug_print_string "Extra extension\n") `kand` false
    // This allows the client to send less extensions,
    // but the ones that are sent must be exactly the same
    | Some e' ->
      //FIXME: Extensions.E_pre_shared_key "may be updated" 4.1.2
      true) // FIXME
      //(extensionBytes e) = (extensionBytes e'))

// Not enforceable by a stateless server? The client can change its
// mind, but at least the whole exchange integrity is guaranteed by
// the digest computation. The (unauthenticated) HRR won't not
// convince the client to use a weaker CS for 0RTT, since it is bound
// to the PSK.

let valid_retry o1 hrr o2 = 
  let extension_ok = List.Helpers.forall_aux (o1, hrr) valid_ch2_extension o2.CH.extensions in
  o1.CH.version = o2.CH.version &&
  o1.CH.random = o2.CH.random &&
  o1.CH.session_id = o2.CH.session_id &&
  List.Tot.mem hrr.HRR.cipher_suite o2.CH.cipher_suites &&
  o1.CH.compression_methods = o2.CH.compression_methods &&
  extension_ok


/// Should we also check for a cookie in o2?
/// Note that our server always produces a cookie.

// Now called from Handshake
let trace_offer offer =
  trace ("offered client extensions "^string_of_ches offer.CH.extensions);
  trace ("offered cipher suites "^string_of_ciphersuitenames offer.CH.cipher_suites);
  trace (match find_supported_groups offer with
    | Some ngl -> "offered groups "^string_of_namedGroups ngl(*^", supported groups "^string_of_namedGroups cfg.named_groups*)
    | None -> "no groups offered, only PSK (1.3) and FFDH (1.2) can be used");
  trace (match find_client_extension CHE_key_share? offer with
    | Some (CHE_key_share ksl) -> "offered shares on groups "^string_of_keyShares ksl
    | None -> "no key shares offered, only PSK and HRR possible");
  trace (List.Tot.fold_left accum_string_of_pv "offered versions"
    (Negotiation.Version.offered_versions offer))

//19-06-17 possibly disabled for v1?
#push-options "--admit_smt_queries true"
let server_ClientHello2 #region ns o1 hrr o2 app_cookie = 
  trace ("Processing second offer based on existing HRR state (stateful HRR).");
  if not (valid_retry o1 hrr o2) then 
    fatal Illegal_parameter "Inconsistant parameters between first and second client hello"
  else
    let sm = computeServerMode ns.cfg o2 ns.nonce in
    match sm with
    | Error z -> 
      trace ("negotiation failed: "^string_of_error z); Error z
    | Correct (ServerRetry hrr) ->
      fatal Illegal_parameter "client sent the same hello in response to hello retry"
    | Correct (ServerMode m cert _) ->
      trace ("negotiated after HRR "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
      let nego_cb = ns.cfg.nego_callback in
      let exts = List.Tot.filter CHE_Unknown_extensionType? o2.CH.extensions in
      let exts_bytes = clientHelloExtensions_serializer32 exts in
      trace ("Negotiation callback to handle extra extensions.");
      match nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes (Some app_cookie) with
      | Nego_accept sexts ->
        ns.state := S_ClientHello m cert;
        Correct (ServerMode m cert sexts)
      | _ ->
        trace ("Application requested to abort the handshake after internal HRR.");
        fatal Handshake_failure "application aborted the handshake by callback"
#pop-options 

/// Checks that the mode selected for a second ClientHello is
/// compatible with our HelloRetryRequest: the required ciphersuite
/// and group (if any) are those negotiated. No need to check the
/// sessionId is unchanged since it is included in the digest.

let server_hrr_verify offer mode hrr = 
  is_named_cs mode.n_cipher_suite hrr.HRR.cipher_suite &&
  ( match TLS.Cookie.find_keyshare hrr with
    | None -> true 
    | Some g -> kexAlg mode <> Kex_PSK && chosenGroup mode = CommonDH.group_of_namedGroup g )

//19-06-17 Verification of this function is particularly slow and brittle; what to do? 

#reset-options "--using_facts_from '* -LowParse'"
#restart-solver

// 20190625 JP: Overflow error. Reducing rlimits and/or ifuel yields unknown instead of
// error. Disabling until we switch to a version of Z3 with the fix.
#push-options "--z3rlimit 2048 --max_ifuel 12 --initial_ifuel 12"
let server_ClientHello #region ns offer =
  let sm = computeServerMode ns.cfg offer ns.nonce in
  match sm with
  | Error z -> trace ("negotiation failed: "^string_of_error z); Error z
  | Correct r ->
    let h = get() in assert (inv ns h);
    match r with 
    | ServerRetry hrr ->
      trace ("no common group, sending a retry request..."); sm
    | ServerMode m cert _ ->
      let nego_cb = ns.cfg.nego_callback in
      let exts = List.Tot.filter CHE_Unknown_extensionType? offer.CH.extensions in
      // 19-06-16 recurring problem with list filtering; might disappear by lowering, or we could use the list serializer.
      assume(clientHelloExtensions_list_bytesize exts <= 65535);
      let exts_bytes = clientHelloExtensions_serializer32 exts in
      trace ("Negotiation callback to handle extra extensions and query for stateless retry.");
      let r = nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes None in
      let h = get() in assert (inv ns h);
      match r with
      | Nego_abort ->
        trace ("Application requested to abort the handshake.");
        fatal Handshake_failure "application requested to abort the handshake."
      | Nego_retry filling ->
        trace ("Application requested to retry the handshake.");
        assume(CipherSuite13? m.n_cipher_suite); // from ServerMode 
        let hrr = TLS.Cookie.hrr0 offer.CH.session_id m.n_cipher_suite in
        Correct (ServerRetry hrr)
      | Nego_accept sexts ->
        trace ("Application accepted "^
          string_of_pv m.n_protocol_version^" "^
          string_of_ciphersuite m.n_cipher_suite);
        ns.state := S_ClientHello m cert;
        Correct (ServerMode m cert sexts)
#pop-options

(* 
let share_of_serverKeyShare (ks:CommonDH.serverKeyShare) : share =
  assume False; //18-12-16 TODO incomplete pattern
  let CommonDH.Share g gy = ks in (| g, gy |)
*)

#restart-solver

#reset-options "--using_facts_from '* -LowParse'"
#set-options "--z3rlimit 100"
private let keyShareEntry_of_ks (|g,gx|) : Parsers.ServerHelloExtension.serverHelloExtension_SHE_key_share = 
  let r = CommonDH.format #g gx in
  //19-06-17 push to CommonDH? 
  assume(Parsers.KeyShareEntry.keyShareEntry_bytesize r <= 65535);
  r

// pure except for ns.state and tracing

#reset-options "--z3rlimit 40" 
let server_ServerShare #region ns oks app_ees =
  let S_ClientHello mode cert = !ns.state in  
  let pv = mode.n_protocol_version in 

  //19-06-17 we should probably split this function into two,
  // returning version-specific modes
  
  if pv = TLS_1p3 then (
    let pski = match mode.n_pski with | Some i -> Some i | None -> None in 
    let ches = mode.n_offer.CH.extensions in
    let shes = server_clientExtensions
      pv
      ns.cfg
      mode.n_cipher_suite
      None  // option (TI.cVerifyData*TI.sVerifyData)
      pski 
      (Option.mapTot keyShareEntry_of_ks oks)
      (mode.n_sessionID = mode.n_offer.CH.session_id)
      ches in 
    trace ("processing client extensions "^string_of_ches ches);
    trace ("including server extensions "^string_of_shes shes);
    if not (Parsers.ServerHelloExtensions.check_serverHelloExtensions_list_bytesize shes) then
      fatal Handshake_failure "serverHello extensions overflow"
    else (
    let tls_ees = encrypted_clientExtensions
      mode.n_protocol_version
      ns.cfg
      mode.n_cipher_suite
      None  // option (TI.cVerifyData*TI.sVerifyData)
      pski
      (Option.mapTot keyShareEntry_of_ks oks)
      (mode.n_sessionID = mode.n_offer.CH.session_id)
      ches in 
    let app_ees = Extensions.encryptedExtensions_of_unknownExtensions app_ees in
    trace ("including application encrypted extensions "^string_of_ees app_ees);
    trace ("including other encrypted extensions "^string_of_ees tls_ees);
    let ees = List.Tot.append tls_ees app_ees in 
    if not (Parsers.EncryptedExtensions.check_encryptedExtensions_list_bytesize ees) then
      fatal Handshake_failure "serverHello extensions overflow"
    else 
    let mode = Mode
      mode.n_offer
      mode.n_hrr
      mode.n_protocol_version
      mode.n_server_random
      mode.n_sessionID
      mode.n_cipher_suite
      mode.n_pski
      shes
      (Some ees)
      oks
      mode.n_client_cert_request
      mode.n_server_cert
      mode.n_client_share 
    in
    ns.state := S_Mode mode cert;
    Correct mode ))

  else (
    // TLS 1.2, probably worth splitting in two functions 
    let ches = mode.n_offer.CH.extensions in
    let shes = server_clientExtensions
      pv
      ns.cfg
      mode.n_cipher_suite
      None  // option (TI.cVerifyData*TI.sVerifyData)
      None
      (Option.mapTot keyShareEntry_of_ks oks)
      (mode.n_sessionID = mode.n_offer.CH.session_id)
      ches in 
    trace ("processing client extensions "^string_of_ches ches);
    trace ("including server extensions "^string_of_shes shes);
    if not (Parsers.ServerHelloExtensions.check_serverHelloExtensions_list_bytesize shes) then
      fatal Handshake_failure "serverHello extensions overflow"
    else (
    let mode = Mode
      mode.n_offer
      mode.n_hrr
      mode.n_protocol_version
      mode.n_server_random
      mode.n_sessionID
      mode.n_cipher_suite
      None
      shes
      None
      oks
      mode.n_client_cert_request
      mode.n_server_cert
      mode.n_client_share 
    in
    ns.state := S_Mode mode cert;
    Correct mode ))
