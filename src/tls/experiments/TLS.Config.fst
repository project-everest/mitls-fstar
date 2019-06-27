module TLS.Config 
 

/// Initial connection configurations & application callbcks. We use a
/// top-level struct, relying on QD types for all list-like fields.
/// 
/// No need for an interface, as this file mostly declares datatypes.
/// This could probably be just a "Repr" module. 


open TLS.Callbacks 

// it may be best to declare RFC-level shared types.

//19-01-22 carried by CH,EE,SH...; was CommonDH.supportedNamedGroups, overly restrictive. 
type groups       = Parsers.ClientHelloExtension.clientHelloExtension_CHE_supported_groups
type versions     = Parsers.SupportedVersions.supportedVersions
type ciphersuites = cs: list Parsers.CipherSuite.cipherSuite { let l = List.length cs in 0 <= l /\ l <= (65536/2 - 2)}
type signatures   = Parsers.SignatureScheme.signatureScheme
type alpn         = Parsers.ClientHelloExtension.clientHelloExtension_CHE_application_layer_protocol_negotiation
type server_names = Parsers.ClientHelloExtension_CHE_server_name.clientHelloExtension_CHE_server_name
//WAS simpler: n:Parsers.HostName.hostName{Bytes.length n <= 65535 - 5}); 
// 19-01-19 Hoisted parser refinements for, to be propagated. 

noeq type shared: Type0 = {
    // negotiable protocol parameters, in decreasing order of preference.
    supported_versions: versions;
    supported_ciphersuites: ciphersuites;
    supported_groups: groups;
    supported_signatures_algorithms: signatures;

    // ALPN offers (for client) or preferences (for server)
    // we use the wire-format type, structurally shared between clients and servers. 
    alpn: option alpn;

    // selects QUIC labels for key derivations
    is_quic: bool; 

    // I/O style for underlying TCP in the TLS API
    non_blocking_read: bool;

    // 0-RTT offer (client) and support (server) and data limit.
    // by convention 0 means 0-RTT is not offered. 
    max_early_data: UInt32.t; 
    
    safe_renegotiation: bool;        // demands this extension when renegotiating
    extended_master_secret: bool;    // turn on RFC 7627 extended master secret support

    // Certificate callbacks; could be split, as (for now) the client
    // calls only to verify the server signature and certificate
    // chain.
    cert_callbacks: cert_cb;
    }

open LowParse.Low.Base 
open Mem

type ptr_len = slice (srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _)) (srel_of_buffer_srel (LowStar.Buffer.trivial_preorder _))

noeq type shared_low: Type0 = { 
    low_supported_versions: ptr_len;
    low_supported_ciphersuites: ptr_len;
    low_supported_groups: ptr_len;
    low_supported_signatures_algorithms: ptr_len;
    alpn: ptr_len;
    is_quic: bool; 
    non_blocking_read: bool;
    max_early_data: UInt32.t;
    safe_renegotiation: bool;
    extended_master_secret: bool;
    cert_callbacks: cert_cb;
}    

// repr design: how much abstraction over those? 

noextract let shared_live (h0:mem) x = 
  live_slice h0 x.low_supported_versions /\
  live_slice h0 x.low_supported_ciphersuites /\
  live_slice h0 x.low_supported_groups /\
  live_slice h0 x.low_supported_signatures_algorithms 
  // nothing so far for the callbacks

noextract let shared_inv (h0:mem) (s:shared) (x:shared_low) = 
  valid_content Parsers.SupportedVersions.supportedVersions_parser h0 x.low_supported_versions 0ul s.supported_versions 
  // same for the 3 others --- valid_repr should help
  // valid_content _ h0 x.low_supported_ciphersuites 0ul s.supported_ciphersuites 
  // valid_content _ h0 x.low_supported_groups 0ul s.supported_groups
  // valid_content _ h0 x.low_supported_signatures_algorithms 0ul s.supported_signatures_algorithms 

assume val validate_shared_config (h0:mem) (x:shared_low): 
  ST (Ghost.erased shared)
  (requires fun h0 -> shared_live h0 x)
  (ensures fun h0 r h1 -> 
    modifies_none h0 h1 /\
    shared_inv h1 (Ghost.reveal r) x)

// not sure what's the most convenient here; maybe passing (erased s & x). 

// we may need here boilerplate code such as the ..._new in Negotiation 


type offered_groups (base: shared) = 
    groups
//19-05-18 ??
// gs:groups{ List.Tot.for_all (fun g -> List.mem g base.supported_groups) gs }


noeq type client = | Client: 
    base: shared -> 
    // honor hello retry requests from the server
    // currently not used? DELETE? 
    // hello_retry: bool;          

    // propose share from these groups (it should it be a subset of [named_groups]).
    //19-05-04 only makes sense with TLS 1.3; but must be non-empty?
    //19-05-28 recoverable from CH.
    shares: offered_groups base -> 
    
    // Send a [server_name] extension with these indications. 
    // Not used to accept the resulting server certificate chain
    // (since we rely on a callback for it).
    servers: option server_names ->

    //QD: see new [TaggedUnknownExtension]. Missing list? 
    // We will use a manually-written coercion in [Extensions] but we
    // still need to prove that the two parsers coincide.
    custom_extensions: Callbacks.custom_extensions -> 

    // Offered tickets, should be *after* decryption in the spec
    //QD: for now we decrypt them and pass resumeInfo as an extra
    // parameter. One low-level approach might be to decrypt them
    // in-place. Or we could decrypt before passing the config to the
    // new connection.
    offer_tickets: list (psk_identifier * ticket_seal) ->
    // offer ticket support
    enable_tickets: bool -> 
    // called when receiving a new ticket
    ticket_callback: ticket_cb -> 

    // called to negotiate custom extensions and confirm the mode 
    nego_callback: nego_cb ->
    client

noeq type server = { 
    (* SERVER *)
    
    enable_tickets: bool; // accepts and emits tickets
    send_ticket: option FStar.Bytes.bytes; 
    // contents??
    // could instead use a callback for issuing a new ticket 
    // ticket_callback: ticket_cb;  

    // called to respond to the client custom extensions and confirm the mode 
    nego_callback: nego_cb;

    // TODO. Not supported yet; should include the CertificateRequest contents (a list of CA)
    request_client_certificate: bool; 

    // should always be on!
    // check_client_version_in_pms_for_old_tls: bool;
}

