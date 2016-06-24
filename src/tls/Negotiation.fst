module Negotiation

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages

//16-05-31 these opens are implementation-only; overall we should open less
open TLSExtensions 
open CoreCrypto

(* Negotiation: HELLO sub-module *)
type ri = cVerifyData * sVerifyData 

type nego = {
     n_resume: bool;
     n_client_random: TLSInfo.random;
     n_server_random: TLSInfo.random;
     n_sessionID: option sessionID;
     n_protocol_version: protocolVersion;
     n_kexAlg: TLSConstants.kexAlg;
     n_aeAlg: TLSConstants.aeAlg;
     n_sigAlg: option TLSConstants.sigAlg;
     n_cipher_suite: cipherSuite;
     n_dh_group: option namedGroup;
     n_compression: option compression;
     n_extensions: negotiatedExtensions;
     n_scsv: list scsv_suite;
}                 

type hs_id = {
     id_cert: Cert.chain;
     id_sigalg: option sigHashAlg;
}

type session = {
     session_nego: nego;
}     


// represents the outcome of a successful handshake, 
// providing context for the derived epoch
type handshake = 
  | Fresh of session // was sessionInfo
  | Resumed of session // was abbrInfo * sessionInfo 
// We use SessionInfo as unique session indexes.
// We tried using instead hs, but this creates circularities
// We'll probably need a global log to reason about them.
// We should probably do the same in the session store.

// extracts a transport key identifier from a handshake record
val hsId: handshake -> Tot id 
//16-05-31 TODO breaking TC in TLS; was (i:id { is_stream_ae i }) //16-05-19 focus on TLS 1.3

let hsId h = noId // Placeholder 

