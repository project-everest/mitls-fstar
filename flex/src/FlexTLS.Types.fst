(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Types

open Platform.Bytes

open MiTLS.TLSInfo
open MiTLS.TLSConstants
open MiTLS.TLSExtensions



/// <summary>
/// Fragmentation policy union type,
/// The constructor represents the number of fragments that will be sent to the network
/// The value represents the length of the fragments that will be sent
/// </summary>
type fragmentationPolicy =
  /// <summary> Will send All fragments, each of length LEN bytes </summary>
  | All of int
  /// <summary> Will send One fragment of length LEN bytes </summary>
  | One of int

/// <summary>
/// DH key exchange parameters record,
/// Contains both public and secret values associated to Diffie Hellman parameters
/// </summary>
type kexDH = {
  /// <summary> Tuple (p,g) that contains both p and g public DH parameters </summary>
  pg: bytes * bytes;
  /// <summary> Local secret value of the DH exchange </summary>
  x:  bytes;
  /// <summary> Local public value (g^x mod p) of the DH exchange </summary>
  gx: bytes;
  /// <summary> Peer's public value (g^y mod p) of the DH exchange </summary>
  gy: bytes
}

/// <summary>
/// FFDH key exchange parameters record, for negotiated DH parameters
/// Contains both public and secret values associated of Diffie Hellman parameters
/// </summary>
type kexFFDH = {
  /// <summary> Negotiated Finite Field DH group </summary>
  group: dhGroup;
  /// <summary> Local secret value of the DH exchange </summary>
  x:  bytes;
  /// <summary> Local public value (g^x mod p) of the DH exchange </summary>
  gx: bytes;
  /// <summary> Peer's public value (g^y mod p) of the DH exchange </summary>
  gy: bytes;
}

/// <summary>
/// ECDH key exchange parameters record, for negotiated ECDH parameters
/// Contains both public and secret values associated of EC Diffie Hellman parameters
/// </summary>
type kexECDH = {
  /// <summary> Negotiated Elliptic Curve </summary>
  curve: ec_curve;
  /// <summary> Point format compression </summary>
  comp: bool;
  /// <summary> Local secret value of the ECDH exchange </summary>
  x:  bytes;
  /// <summary> Local public value represented as a point coordinates </summary>
  ecp_x: bytes * bytes;
  /// <summary> Peer's public value represented as a point coordinates </summary>
  ecp_y: bytes * bytes;
}

/// <summary>
/// Key exchange union type,
/// The constructor represents the type of Key Exchange Mechanism used in the Handshake
/// </summary>
type kex =
  /// <summary> Key Exchange Type is RSA and the constructor holds the pre-master secret </summary>
  | RSA of bytes
  /// <summary> Key Exchange Type is Diffie-Hellman and the constructor holds all DH parameters </summary>
  | DH of kexDH
  /// <summary> Key Exchange Type is Finite Field Diffie-Hellman with negotiated group and the constructor holds all DH parameters </summary>
  | FFDH of kexFFDH
  /// <summary> Key Exchange Type is Elliptic Curve Diffie-Hellman with negotiated curve and the constructor holds all ECDH parameters </summary>
  | ECDH of kexECDH

/// <summary>
/// Hold certificates private keys
/// </summary>
type priKey =
  /// <summary> No key set </summary>
  | PK_None
  /// <summary> Private signing key and associated algorithm </summary>
  | PK_Sig of sigHashAlg * CoreSig.sigskey
  /// <summary> Private (RSA) decryption key </summary>
  | PK_Enc of CoreACiphers.sk

/// <summary>
/// Session Secrets record,
/// This structure contains all secret information of a Handshake
/// </summary>
type secrets = {
  /// <summary> Private key associated to the current certificate (in sessionInfo) </summary>
  pri_key: priKey;
  /// <summary> Key Exchange bytes </summary>
  kex: kex;
  /// <summary> Pre Master Secret bytes </summary>
  pms: bytes;
  /// <summary> Master Secret bytes </summary>
  ms: bytes;
  /// <summary> Keys bytes of an epoch, as a tuple (reading keys, writing keys) </summary>
  epoch_keys: bytes * bytes;
  (* read  , write *)
}

/// <summary>
/// Channel record,
/// Keeps track of the Record state and the associated Epoch of an I/O channel
/// </summary>
/// <remarks> There is no CCS buffer because those are only one byte </remarks>
type channel = {
  /// <summary> Secret and mutable state of the current epoch (keys, sequence number, etc...) </summary>
  record: Record.ConnectionState;
  /// <summary> Public immutable data of the current epoch </summary>
  epoch:  TLSInfo.epoch;
  /// <summary> Raw bytes of the secrets currently in use. This is meant to be a read-only (informational) field: changes to this field will have no effect </summary>
  secrets: secrets;
  /// <summary> Initially chosen protocol version before negotiation </summary>
  epoch_init_pv: ProtocolVersion;
  /// <summary> Verify data of the channel </summary>
  verify_data: bytes;
  /// <summary> Buffer for messages of the Handshake content type </summary>
  hs_buffer: bytes;
  /// <summary> Buffer for messages of the Alert content type </summary>
  alert_buffer: bytes;
  /// <summary> Buffer for messages of the ApplicationData content type </summary>
  appdata_buffer: bytes
}

/// <summary>
/// Global state of the application
/// </summary>
type state = {
  /// <summary> Reading channel (Incoming) </summary>
  read: channel;
  /// <summary> Writing channel (Outgoing) </summary>
  write: channel;
  /// <summary> Network stream where the data is exchanged with the peer </summary>
  ns: Tcp.NetworkStream;
  /// <summary> Handshake log </summary>
  hs_log: bytes;
}

/// <summary>
/// Next security context record used to generate a new epoch
/// </summary>
type nextSecurityContext = {
  /// <summary> Next session information (for the future epoch/record state) </summary>
  si: SessionInfo;
  /// <summary> Most recent client random; used to generate new keys </summary>
  crand: bytes;
  /// <summary> Most recent server random; used to generate new keys </summary>
  srand: bytes;
  /// <summary> Secrets to be used by the next epoch </summary>
  secrets: secrets;
  /// <summary> Offers of DH groups and public keys from the client (useful for negotiated DH groups, and hence for TLS 1.3) </summary>
  offers: list kex;
}

/// <summary>
/// Handshake Message record type for Hello Request
/// </summary>
type FHelloRequest = {
  /// <summary> Message Bytes </summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Client Hello
/// </summary>
type FClientHello = {
  /// <summary> Protocol version </summary>
  pv: option<ProtocolVersion>;
  /// <summary> Client random bytes </summary>
  rand: bytes;
  /// <summary> Session identifier. A non-empty byte array indicates that the client wants resumption </summary>
  sid: option bytes;
  /// <summary> List of ciphersuite names supported by the client </summary>
  ciphersuites: option (list cipherSuiteName);
  /// <summary> List of compression mechanisms supported by the client </summary>
  comps: option (list Compression);
  /// <summary> List of extensions proposed by the client; None: user asks for default; Some<list>: user gives value. A returned client hello always has Some<list>. </summary>
  ext: option (list clientExtension);
  /// <summary> Message Bytes </summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Server Hello
/// </summary>
type FServerHello = {
  /// <summary> Protocol version </summary>
  pv: option<ProtocolVersion>;
  /// <summary> Server random bytes </summary>
  rand: bytes;
  /// <summary> Session identifier. A non-empty byte array indicates that the server accepted resumption </summary>
  sid: option bytes;
  /// <summary> Ciphersuite selected by the server </summary>
  ciphersuite: option cipherSuiteName;
  /// <summary> Compression selected by the server </summary>
  comp: Compression;
  /// <summary> List of extensions agreed by the server </summary>
  ext: option (list serverExtension);
  /// <summary> Message bytes </summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for ServerConfiguration
/// </summary>
type FServerConfiguration = {
  /// <summary> The configuration identifier to be used in 0-RTT mode </summary>
  id: configurationId;
  /// <summary> The last time when this configuration is expected to be valid </summary>
  expirationDate: int;
  /// <summary> The group for the long-term DH key </summary>
  group: dhGroup;
  /// <summary> The long-term DH key associated to the configuration </summary>
  key: bytes;
  /// <summary> The type of 0-RTT handshake that this configuration is to be used for </summary>
  earlyDataType: earlyDataType;
  /// <summary> List of extensions associated to the serverConfiguration message </summary>
  ext: option (list serverConfigurationExtention);
  /// <summary> Message bytes</summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Certificate
/// </summary>
type FCertificate = {
  /// <summary> Full certificate chain bytes </summary>
  chain: Cert.chain;
  /// <summary> Message bytes</summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Server Key Exchange
/// </summary>
type FServerKeyExchange = {
  /// <summary> Signature algorithm </summary>
  sigAlg: Sig.alg;
  /// <summary> Signature </summary>
  signature: bytes;
  /// <summary> Key Exchange Information </summary>
  kex: kex;
  /// <summary> Message bytes </summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Certificate Request
/// </summary>
type FCertificateRequest = {
  /// <summary> List of certificate types </summary>
  certTypes: list certType;
  /// <summary> List of Signature algorithms </summary>
  sigAlgs: list Sig.alg;
  /// <summary> List of user provided cert names </summary>
  names: list string;
  /// <summary> Message bytes </summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Server Hello Done
/// </summary>
type FServerHelloDone = {
  /// <summary> Message Bytes</summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Certificate Verify
/// </summary>
type FCertificateVerify = {
  /// <summary> Signature algorithm </summary>
  sigAlg: Sig.alg;
  /// <summary> Signature </summary>
  signature: bytes;
  /// <summary> Message bytes </summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Client Key Exchange
/// </summary>
type FClientKeyExchange = {
  /// <summary> Key Exchange mechanism information </summary>
  kex: kex;
  /// <summary> Message bytes </summary>
  payload: bytes;
}

/// <summary>
/// CCS Message record type
/// </summary>
type FChangeCipherSpecs = {
  /// <summary> Message bytes </summary>
  payload: bytes;
}

/// <summary>
/// Handshake Message record type for Finished
/// </summary>
type FFinished = {
  /// <summary> Typically PRF(ms,hash(handshake log)) </summary>
  verify_data: bytes;
  /// <summary> Message bytes </summary>
  payload: bytes;
}
