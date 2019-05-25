module TLS.Callbacks

open FStar.Bytes
open Mem 

//include Parsers.ProtocolVersion 
include Parsers.ServerName
include Parsers.ProtocolName
include Parsers.ProtocolNameList
include Parsers.PskIdentity
include CipherSuite 

/// opaque context pointers provided by the application and passed back to it.

val context: Type0
val default_context: unit -> EXT context 

/// ------------------------------------------------------------------------------
/// Ticket callback, used to store received tickets with their authenticated info

type psk_identifier = pskIdentity_identity

[@unifier_hint_injective]
inline_for_extraction
let vlbytespl (min max: nat) = (x: bytes { min <= length x /\ length x <= max })

type pskInfo = {
  ticket_nonce: option (vlbytespl 0 255);
  time_created: UInt32.t;
  ticket_age_add: UInt32.t;
  allow_early_data: bool;      // New draft 13 flag
  allow_dhe_resumption: bool;  // New draft 13 flag
  allow_psk_resumption: bool;  // New draft 13 flag
  early_ae: aeadAlg;
  early_hash: hash_alg;
  identities: bytes * bytes; // TODO certs 
}

type ticketInfo =
  | TicketInfo_12 of Parsers.ProtocolVersion.protocolVersion * cipherSuite * ems:bool
  | TicketInfo_13 of pskInfo

type ticket_seal = b:bytes{length b < 65536}


/// Calls Client to store received tickets and their context.
///
/// TODO consider adding pre-condition capturing the authenticated
/// properties of the context.

// 2018.03.10 SZ: Allow it to modify [psk_region]?
// Missing refinements on arguments from types in PSK

inline_for_extraction
type ticket_cb_fun =
  sni:string -> 
  ticket:ticket_seal -> 
  info:ticketInfo -> 
  rawkey:bytes -> 
  ST unit
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1)

noeq type ticket_cb = {
  ticket_context: context;
  new_ticket: context -> ticket_cb_fun;
}


/// ------------------------------------------------------------------------------
/// Negotiation callback, for both clients and servers.
///
/// Only the server gets to retry or to respond with
/// custom_extensions. Consider separating the two callbacks.

/// Custom Extensions sent and received from the negotiation callback.

include Parsers.ExtensionType
include Parsers.UnknownExtension

// 18-12-22 TODO use a vl wire format instead of a list
type custom_id = v:UInt16.t{~(known_extensionType_repr v)}
type custom_extension = custom_id * unknownExtension
type custom_extensions = list custom_extension

(* Helper functions for the C API to construct the list from array *)
let empty_custom_extensions () : list custom_extension = []
let add_custom_extension 
  (l:list custom_extension) 
  (hd:custom_id) 
  (b:bytes {length b < 65533}) = (hd, b) :: l

type cookie = Parsers.Cookie.cookie 
type nego_action =
  | Nego_abort: nego_action
  | Nego_retry: cookie_extra: cookie -> nego_action
  | Nego_accept: extra_ext: custom_extensions -> nego_action

/// Witnessing the callback's decision as an abstract property that
/// can be provably authenticated by the peer connection.
///
/// This suggests we are not passing enough of the mode, including at
/// least some unique identifiers. And also that we need to separate
/// client and server callbacks.

val negotiated:  
  Parsers.ProtocolVersion.protocolVersion -> 
  client_ext: bytes -> 
  cookie: option cookie -> 
  nego_action -> 
  Type0

inline_for_extraction 
type nego_cb_fun =
  pv: Parsers.ProtocolVersion.protocolVersion -> 
  client_ext: bytes -> 
  cookie: option cookie -> 
  ST nego_action
    (requires fun _ -> True)
    (ensures fun h0 r h1 -> 
      negotiated pv client_ext cookie r /\ 
      (Nego_retry? r ==> None? cookie /\ modifies_none h0 h1))

noeq type nego_cb = {
  nego_context: context;
  negotiate: context -> nego_cb_fun;
}

// TODO authentication properties: 
//
// * cookie: from the retry to the second ClientHello
// * extensions: from Client to Server, from Server to Client

/// ------------------------------------------------------------------------------
/// Certificate callbacks
///
/// Each callback takes an application context (app_context) and a
/// function pointer to an application-provided functionality.
///
/// The callback is actually performed in FFI.fst, which calls into
/// ffi.c and takes care of marshalling miTLS parameters like
/// signatureSchemeList to the types expected by the application.
///
/// This explicit representation of closures is necessary for
/// compiling this to C via KreMLin. The representation is hidden from
/// callers and the wrappers are provided below to implement it.

type cert_repr = b:bytes {length b < 16777216}
type cert_type = FFICallbacks.callbacks

include Parsers.SignatureScheme
include Parsers.SignatureSchemeList

// outline authorization predicates--but we miss identifiers. 

// TODO: parametricity in a "logical payload" formula defined by the
// handshake, passed as an input to select, used in the preconditiong
// of sign, and in the postcondition of verify.
//
noextract val payload: cert_type -> bytes -> Type0 

noextract 
val cert_selected: 
  Parsers.ProtocolVersion.protocolVersion -> 
  bytes -> 
  bytes -> 
  signatureSchemeList -> 
  cert_type -> 
  signatureScheme ->
  Type0 
inline_for_extraction
type cert_select_cb_fun = 
  pv:Parsers.ProtocolVersion.protocolVersion -> 
  sni:bytes -> 
  alpn:bytes -> 
  sig:signatureSchemeList -> 
  ST (option (cert_type * signatureScheme))
    (requires fun _ -> True)
    (ensures fun h0 r h1 -> 
      modifies_none h0 h1 /\ (
      match r with 
      | Some (ct, sa) -> cert_selected pv sni alpn sig ct sa 
      | None -> True
      // TODO the caller needs to know the cert_type is for its payload
      ))

noextract 
val cert_format: cert_type -> list cert_repr 

noextract 
val cert_parse: cc: list cert_repr -> option (ct:cert_type{ cc == cert_format ct })


// TODO add an error case; use it as default. 
inline_for_extraction
type cert_format_cb_fun =
  ct:cert_type -> 
  ST (list cert_repr)
    (requires fun _ -> True)
    (ensures fun h0 r h1 -> 
      (r == [] \/ r == cert_format ct) /\
      modifies_none h0 h1)

inline_for_extraction
type cert_sign_cb_fun = 
  ct:cert_type -> 
  signatureScheme -> 
  tbs:bytes -> 
  ST (option bytes)
    (requires fun _ -> payload ct tbs)
    (ensures fun h0 _ h1 -> 
      modifies_none h0 h1)

inline_for_extraction
type cert_verify_cb_fun = 
  cc:list cert_repr -> 
  signatureScheme -> 
  tbs:bytes -> 
  sigv:bytes -> ST bool
    (requires fun _ -> True)
    (ensures fun h0 b h1 -> 
      modifies_none h0 h1 /\
      (b ==> (
        match cert_parse cc with 
        | None -> False
        | Some ct -> payload ct tbs)))

val cert_cb: Type0
val cert_select_cb: cert_cb -> cert_select_cb_fun
val cert_format_cb: cert_cb -> cert_format_cb_fun
val cert_sign_cb:   cert_cb -> cert_sign_cb_fun 
val cert_verify_cb: cert_cb -> cert_verify_cb_fun


/// Defaults callbacks in configurations

val defaultServerNegoCB: nego_cb 
val defaultCertCB: cert_cb 


