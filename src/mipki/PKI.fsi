open Microsoft.FSharp.Core
open Microsoft.FSharp.Collections
open System.Collections

(* ideal functionality *)

module Sig = begin

  type keyUsage = 
  | CertSign     // for root or intermediate certs
  | CRLSign      // also covering OCSP

  // applicative usages
  | Sign         // sig, eg TLS
  | DataEncipher // encryption, eg TLS-RSA
  | KeyEncipher  // encryption, eg TLS-RSA too
  // we ignore others here, rejected at parsing.

  type curve = // TBD curves we support
  | NIST_P256
  | NIST_P384
  | NIST_P521

  type ec_point =
  | Uncompressed of x:bigint * y:bigint
  | Compressed_Prime of x:bigint * s:byte

  type pk =
  | RSA_Modulus of n:bigint * e:int
  | EC_Point of c:curve * p:ec_point (* TBD: point formats we support *)
  | DH_Element of p:bigint * e:bigint

  type sk =
  | RSA_Factors of p:bigint * q:bigint * e:int
  | EC_Private of c:curve * f:bigint
  | DH_Exponent of p:bigint * g:bigint * n:bigint

  type keyalg = // algorithm recorded in certs
  | RSA
  | ECDH
  | DH  // deprecated

  type hashalg =
  | MD5
  | SHA1
  | SHA256
  | SHA384
  | SHA512

  // all algorithms needed for signing, 
  // including formatting, hashing & core signing.
  // for simplicity, we assume only one is used with every honest cert-signing key
  type sigalg = 
    | RSA_PSS   of hashalg // only RSA
    | RSA_PKCS1 of hashalg // only RSA?
    | ECDSA     of hashalg
    | DSA       of hashalg // deprecated

  type sigval
  type signed = byte[]  // before encoding & compression, e.g. certificate bytes

  val keyGen: sigalg -> Set<keyUsage> -> pk * sk  // sk will be kept internal
  val sign  : sigalg -> keyUsage -> sk -> signed -> sigval
  val verify: sigalg -> pk -> signed -> sigval -> bool

  (* keys are honest, or corrupted, or coerced (worse) *)                                     
  val coerce: keyalg -> byte[] -> pk
  val corrupt: keyalg -> pk -> sk

end

module Asn1 = begin
 type oid = byte[]
 type x500 = (oid * string) list // e.g. C=US/O=Microsoft/CN=windows.com/CN=b.com/...
 type time
 type ip
 type email

 type sn = byte[]
 
 type tlsname =
 | DNS of string  // regexp over domains

 // for TLS, we do not plan to interpret the rest:
 | IP of ip
 | URI of string (* over-specific; not used much *)
 | X500 of x500
 | Email of email
 | Other of byte[]

 type ocsp_status = Ok // the only helpful one.


 type ocsp_cert_status =   // authenticated:
   | Revoked | NonExistent // reject, for different reasons
   | Valid                 // accept 
   | Unknown               // lame CA, but acceptable

  // OCSP Response
  type ocsp = {
    status: ocsp_status; // gone after parsing & filtering
    version: int;        // gone after parsing & filtering
    produceTime: time;   // for freshness, ~ 1 day, threshold in Cert.config
    responses: (sn * ocsp_cert_status) list
    thisUpdate: time     // useless? time of last write to the CA DB
    nextUpdate: time     // useless? for freshness too: how long to cache
    sigAlg: Sig.sigalg;
    sigVal: Sig.sigval;
  }

  type extension = 
  | BasicConstraint of int option option // critical, Some when CA, with an optional path length
  | KeyUsage of Set<Sig.keyUsage>
  | ExtendedKeyUsage of list<oid>   // notably TLS's ClientAuthentication & ServerAuthentication
  | SAN of tlsname list             // subject alternative names, e.g. DNS=*.live.com/IPv6=[::1]/URL=https://a.com/q//email=a@b.com/...
  | CertificatePolicy of oid list   // for EV; omitting details after parsing
  | AuthorityInformationAccess of string list * string list // OCSP Responder URLs and Issuer Certificate URLs
  | CRLDistribution of string list       // classic CRLs; not used for security model
  | NameConstraint                       // for restricting delegation, todo later
  | Other of oid * byte[]           // including some MS-specific ones

   // Problem: parsing correction if we omit details here
  type cert = { (* a large ad-hoc record, treated abstractly by most *)
    version: int;
    sn: sn;             // serial number, fresh when issuer is honest
    sigAlg: Sig.sigalg;     // algorithm used for signing this cert
    issuer: x500;      // matches subject of certificate used in create
    notBefore: time;
    notAfter: time;
    subject: x500;     // 
    subjectPK: Sig.keyalg * Sig.pk;  // algorithm & key being certified
    extensions: (extension * bool (*critical?*)) list;
    sigval: Sig.sigval;      // omitting the repeated SigAlg, checked at parsing.
  }

  val parseCert : byte[] -> cert option
  val parseOcsp : byte[] -> ocsp option
  val serializeCert : cert -> byte[]
  val serializeOcsp : ocsp -> byte[]
end

module CA = begin
  type certUsage =
  | TLS_server_auth of Asn1.tlsname list option (* specifying a matching predicate on origins *)
  | Email_signature of Asn1.email list
  | TLS_client_auth
  | EV
  | OCSPSignature
  | OtherUsage of Asn1.oid

  // CA's identity is the last signing certificate within the chain
  val createSelf: Sig.sigalg * certUsage * Sig.pk -> Asn1.cert 
  val createCert: Asn1.cert (* cert signer *) -> (Sig.sigalg * certUsage * Sig.pk) -> Asn1.cert 
  val OCSPsign: Asn1.cert (* cert signer *) -> Asn1.sn (* cert serial number *) -> Asn1.ocsp (* signed *) 

  val revokeCert: Asn1.cert (* cert signer *) -> Asn1.sn -> unit // authorization TBD

  // CA state: tree of all issued certificates, with revocation flag [plus owner credentials]
end

module TLS = begin
  // could separate client & server
  // design: we keep the chain abstract for the application
  type cipher
  type tlsversion

  (* DESIGN: 
  
  We need to revise TLS.fs7
  - currently, we are "low-level", opportunistically/implicitly re-using
    cached sessions, and assuming apps will inspect the resulting complete SIs
  - we need an abstract applicative context
    e.g. for HTTPS, the requested origin for the client, and the virtual host for the server
    [more precisely, the vhost is a partial map from optional origins to TLS configs + certificates] 
    It would be nice to choose the vhost after peeking at the ClientHello's SNI.
    By design, we ignore the IP in the vhost selection (as it is malleable, and invisible to the app)

    We need to (re-)authorize any resumption and any connection pooling.

    TLS can silently resume as long as those contexts are unchanged.
    In particular, in case a server cert supports several origins and there was no SNI, 
    we'll systematically seek re-authorization.
    
    TODO: explain that, for TLS, what we use is actually the domain, not the origin:
    - the protocol is implicit when using the TLS API; this is Ok inasmuch as it is fixed by the cert.
    - the port number is useless for security, as it is not authenticated in practice.

  - still, for agreement, we need that application context to be a function of SIs
    (when complete and/or authorizing)
  - make sessionID (and tickets) internal to TLS
  - call authorize when re-using with different applicative context (e.g. when resuming)

  ? do we need to record the effective chain, or just the communicated one?

  
  *)

  // Possible types of pinning requested by application
  type pin_policy =
  | Pin_CA of string * Asn1.sn
  | Pin_SN of string * Asn1.sn                         
  | Pin_Trusted of string

  type si = { // what we need out of the (client) extensions
    Version: tlsversion;
    SNI: string option;
    Supported_ECCurves: Sig.curve list option;
    Supported_ECPFormat: Asn1.oid list option;
    Cert_Status_Request: bool;      // client asking OCSP stapling?
    Certificate_Transparency: bool; // client asking CT stapling?
    Signature_Algorithms: Sig.sigalg list option;

    Client_ciphers: cipher list;
    Negotiated_cipher: cipher option;

    Verify_request: bool;
    Certificate_request_authorities: Asn1.cert list option

    Server_certificates: Asn1.cert list option; 
    ALPN: string list option; // if we care about SPDY connection pooling?
  }
  
  // what remains after automated checking, 
  // to be endorsed/questioned by the app
  // informally ordered by severity; could be excluded by strict config
  type doubt = 
    | Revoked of Asn1.cert
    | PIN_Mismatch of pin_policy * Asn1.cert
    | UnknownRoot of Asn1.cert     (* we don't know the root CA *)
//    | DomainMismatch of string * string list
    | UsageMismatch of CA.certUsage
    | Expired of Asn1.cert
    | NoRevokeInfo of Asn1.cert

  type trust =
    | DV of doubt list // basic validation    
    | EV of string     // extended validation of an organization, displayed differently, with no doubt!

  val client_configure : pin_policy list  (* -> doubt_policy ? *) -> unit
  val server_configure : (string -> Asn1.cert list option) -> (Asn1.cert list list option) -> unit
  // or
  val client_select : Asn1.cert list -> Asn1.cert option
  val server_select: string -> Asn1.cert list option

  // access the key & details of the leaf; usage is implicitly HTTPS-server
  val client_accept : si -> (Sig.sigalg * Sig.pk * trust) option // None: invalid

  // the doubts are not the same; we could just return (an abstraction of) the chain
  val server_accept : si -> (Sig.sigalg * Sig.pk * string * doubt list) option

end
