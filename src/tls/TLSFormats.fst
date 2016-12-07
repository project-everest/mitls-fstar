module TLSFormats

(**
This file implements seraliazation and parsing functions
for the different values negotiated during the TLS
handshake. For instance protocol version, key exchange mechanism,
hash algorithm etc.

@summary Module for serialization and parsing
*)

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

open FStar.SeqProperties
open Platform.Bytes
open Platform.Error
open TLSError
open CoreCrypto
open TLSConstants

module HH = FStar.HyperHeap
module HS = FStar.HyperStack


(* This is the old version of the inverse predicate. According to CF,
   verification was harder with this style, so we moved to the new style with
   pinverse_t + lemmas. The type abbrevations lemma_inverse_* minimize the
   syntactic overhead.

  logic type pinverse (#a:Type) (#b:Type) (r:b -> b -> Type) (=f:a -> Tot b) =
    y:b -> Tot (xopt:result a{(forall (x:a). r (f x) y <==> (xopt = Correct x))})
*)

type pinverse_t (#a:Type) (#b:Type) ($f:(a -> Tot b)) = b -> Tot (result a)

unfold type lemma_inverse_g_f (#a:Type) (#b:Type) ($f:a -> Tot b) ($g:b -> Tot (result a)) (x:a) =
  g (f x) == Correct x

unfold type lemma_pinverse_f_g (#a:Type) (#b:Type) (r:b -> b -> Type) ($f:a -> Tot b) ($g:b -> Tot (result a)) (y:b) =
  Correct? (g y) ==> r (f (Correct?._0 (g y))) y


(** Serializing function for signature algorithms *)
val sigAlgBytes: sigAlg -> Tot (lbytes 1)
let sigAlgBytes sa =
  match sa with
  | CoreCrypto.RSASIG -> abyte 1z
  | CoreCrypto.DSA    -> abyte 2z
  | CoreCrypto.ECDSA  -> abyte 3z
  | CoreCrypto.RSAPSS -> abyte 0z // TODO fix me!

(** Parsing function associated to sigAlgBytes *)
val parseSigAlg: pinverse_t sigAlgBytes
let parseSigAlg b =
  match cbyte b with
  | 1z -> Correct CoreCrypto.RSASIG
  | 2z -> Correct CoreCrypto.DSA
  | 3z -> Correct CoreCrypto.ECDSA
  | 0z -> Correct CoreCrypto.RSAPSS
  | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_sigAlg: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f sigAlgBytes parseSigAlg x)
  [SMTPat (parseSigAlg (sigAlgBytes x))]
let inverse_sigAlg x = ()

val pinverse_sigAlg: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal sigAlgBytes parseSigAlg x))
  [SMTPat (sigAlgBytes (Correct?._0 (parseSigAlg x)))]
let pinverse_sigAlg x = ()


#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 2"

(** Serializing of the Hash algorithm *)
val hashAlgBytes: hashAlg' -> Tot (lbytes 1)
let hashAlgBytes ha =
  match ha with
  | Hash MD5     -> abyte 1z
  | Hash SHA1    -> abyte 2z
  | Hash SHA224  -> abyte 3z
  | Hash SHA256  -> abyte 4z
  | Hash SHA384  -> abyte 5z
  | Hash SHA512  -> abyte 6z
  | NULL -> abyte 7z // FIXME!!

(** Parsing of the Hash algorithm *)
val parseHashAlg: pinverse_t hashAlgBytes
let parseHashAlg b =
  match cbyte b with
  | 1z -> Correct (Hash MD5)
  | 2z -> Correct (Hash SHA1)
  | 3z -> Correct (Hash SHA224)
  | 4z -> Correct (Hash SHA256)
  | 5z -> Correct (Hash SHA384)
  | 6z -> Correct (Hash SHA512)
  | 7z -> admit();  //TODO: FIXME!!!!
         Correct (NULL)
  | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_hashAlg: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f hashAlgBytes parseHashAlg x)
  [SMTPat (parseHashAlg (hashAlgBytes x))]
let inverse_hashAlg x = ()

val pinverse_hashAlg: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal hashAlgBytes parseHashAlg x))
  [SMTPat (hashAlgBytes (Correct?._0 (parseHashAlg x)))]
let pinverse_hashAlg x = ()

(** Serializing function for compression algorithms *)
val compressionBytes: compression -> Tot (lbytes 1)
let compressionBytes comp =
  match comp with
  | NullCompression      -> abyte 0z
  | UnknownCompression b -> abyte b

// Not pinverse_t compressionBytes, because it never fails

(** Parsing function for compression algorithm *)
val parseCompression: b:lbytes 1
  -> Tot (cm:compression{Seq.equal (compressionBytes cm) b})
let parseCompression b =
  match cbyte b with
  | 0z -> NullCompression
  | b  -> UnknownCompression b

// We ignore compression methods we don't understand. This is a departure
// from usual parsing, where we fail on unknown values, but that's how TLS
// handles compression method lists.

(** Parsing function for compression algorithm lists *)
val parseCompressions: b:bytes -> Tot (list compression) (decreases (length b))
let rec parseCompressions b =
  if length b > 0
  then
    let cmB,b = split b 1 in
    let cm = parseCompression cmB in
    cm::(parseCompressions b)
  else []


#set-options "--max_fuel 1 --initial_fuel 1 --max_ifuel 1 --initial_ifuel 1"

(** Serializing function for lists of compression algorithms *)
val compressionMethodsBytes: cms:list compression
  -> Tot (lbytes (List.Tot.length cms))
let rec compressionMethodsBytes cms =
  match cms with
  | c::cs -> compressionBytes c @| compressionMethodsBytes cs
  | []   -> empty_bytes


#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

(** Serializing function for the protocol version *)
val versionBytes: protocolVersion -> Tot (lbytes 2)
let versionBytes pv =
  match pv with
  | SSL_3p0 -> abyte2 ( 3z, 0z)
  | TLS_1p0 -> abyte2 ( 3z, 1z)
  | TLS_1p1 -> abyte2 ( 3z, 2z )
  | TLS_1p2 -> abyte2 ( 3z, 3z )
  | TLS_1p3 -> abyte2 ( 3z, 4z )

(** Parsing function for the protocol version *)
val parseVersion: pinverse_t versionBytes
let parseVersion v =
  match cbyte2 v with
  | ( 3z, 0z ) -> Correct SSL_3p0
  | ( 3z, 1z ) -> Correct TLS_1p0
  | ( 3z, 2z ) -> Correct TLS_1p1
  | ( 3z, 3z ) -> Correct TLS_1p2
  | ( 3z, 4z ) -> Correct TLS_1p3
  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Parsed an unknown version")

val inverse_version: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f versionBytes parseVersion x)
  [SMTPat (parseVersion (versionBytes x))]
let inverse_version x = ()

val pinverse_version: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal versionBytes parseVersion x))
  [SMTPat (versionBytes (Correct?._0 (parseVersion x)))]
let pinverse_version x = ()

(* JK: injectivity proof requires extra specification for the UnknownCipherSuite objects as they
   have to be distinct from the 'correct' ones *)
val cipherSuiteBytesOpt: cipherSuite -> Tot (option (lbytes 2))
let cipherSuiteBytesOpt cs =
  let abyte2 b: option (lbytes 2) = Some (abyte2 b) in
    match cs with
    | UnknownCipherSuite b1 b2 -> abyte2 (b1,b2)
    | NullCipherSuite                                              -> abyte2 ( 0x00z, 0x00z )

    | CipherSuite Kex_RSA None (MACOnly MD5)                       -> abyte2 ( 0x00z, 0x01z )
    | CipherSuite Kex_RSA None (MACOnly SHA1)                      -> abyte2 ( 0x00z, 0x02z )
    | CipherSuite Kex_RSA None (MACOnly SHA256)                    -> abyte2 ( 0x00z, 0x3Bz )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) MD5)           -> abyte2 ( 0x00z, 0x04z )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) SHA1)          -> abyte2 ( 0x00z, 0x05z )

    | CipherSuite Kex_RSA None(MtE (Block TDES_EDE_CBC) SHA1)      -> abyte2 ( 0x00z, 0x0Az )
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA1)       -> abyte2 ( 0x00z, 0x2Fz )
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA1)       -> abyte2 ( 0x00z, 0x35z )
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA256)     -> abyte2 ( 0x00z, 0x3Cz )
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA256)     -> abyte2 ( 0x00z, 0x3Dz )

    (**************************************************************************)
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x0Dz )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x10z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x13z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x16z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x30z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x31z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x32z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x33z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x36z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x37z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x38z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x39z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x3Ez )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x3Fz )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x40z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x67z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x68z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x69z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x6Az )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x6Bz )

    (**************************************************************************)
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)       -> abyte2 ( 0xc0z, 0x11z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0xc0z, 0x12z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0xc0z, 0x13z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0xc0z, 0x14z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0xc0z, 0x27z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384)  -> abyte2 ( 0xc0z, 0x28z )

    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256) -> abyte2 ( 0xc0z, 0x2fz )
    | CipherSuite Kex_ECDHE (Some ECDSA)  (AEAD AES_128_GCM SHA256) -> abyte2 ( 0xc0z, 0x2bz )
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384) -> abyte2 ( 0xc0z, 0x30z )
    | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_256_GCM SHA384) -> abyte2 ( 0xc0z, 0x2cz )

    (**************************************************************************)
    | CipherSuite Kex_PSK_DHE None (AEAD AES_128_GCM SHA256) -> abyte2 ( 0x00z, 0xaaz )
    | CipherSuite Kex_PSK_DHE None (AEAD AES_256_GCM SHA384) -> abyte2 ( 0x00z, 0xabz )
    | CipherSuite Kex_PSK_ECDHE None (AEAD AES_128_GCM SHA256) -> abyte2 ( 0xd0z, 0x01z )
    | CipherSuite Kex_PSK_ECDHE None (AEAD AES_256_GCM SHA384) -> abyte2 ( 0xd0z, 0x02z )

    (**************************************************************************)
    | CipherSuite Kex_DHE None   (MtE (Stream RC4_128) MD5)         -> abyte2 ( 0x00z, 0x18z )
    | CipherSuite Kex_DHE None   (MtE (Block TDES_EDE_CBC) SHA1)    -> abyte2 ( 0x00z, 0x1Bz )
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA1)     -> abyte2 ( 0x00z, 0x34z )
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA1)     -> abyte2 ( 0x00z, 0x3Az )
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA256)   -> abyte2 ( 0x00z, 0x6Cz )
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA256)   -> abyte2 ( 0x00z, 0x6Dz )

    (**************************************************************************)
    | CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0x9Cz )
    | CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0x9Dz )

    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0x9Ez )
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0x9Fz )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA0z )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA1z )

    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA2z )
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA3z )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA4z )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA5z )

    | CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA6z )
    | CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA7z )

    | SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)         -> abyte2 ( 0x00z, 0xFFz )
    | _ -> None

(** Determine if a ciphersuite is valid *)
let validCipherSuite (c:cipherSuite) = Some? (cipherSuiteBytesOpt c)
let valid_cipher_suite = c:cipherSuite{validCipherSuite c}

(** List of valid ciphersuite *)
let valid_cipher_suites = list valid_cipher_suite

(** Serializing function for a valid ciphersuite *)
val cipherSuiteBytes: valid_cipher_suite -> Tot (lbytes 2)
let cipherSuiteBytes c = Some?.v (cipherSuiteBytesOpt c)


(** Auxillary parsing function for ciphersuites *)
val parseCipherSuiteAux : lbytes 2 -> Tot (result (c:cipherSuite{validCipherSuite c}))
let parseCipherSuiteAux b =
  match cbyte2 b with
  | ( 0x00z, 0x00z ) -> Correct(NullCipherSuite)

  | ( 0x00z, 0x01z ) -> Correct(CipherSuite Kex_RSA None (MACOnly MD5))
  | ( 0x00z, 0x02z ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA1))
  | ( 0x00z, 0x3Bz ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA256))
  | ( 0x00z, 0x04z ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5))
  | ( 0x00z, 0x05z ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1))

  | ( 0x00z, 0x0Az ) -> Correct(CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x2Fz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA1))
  | ( 0x00z, 0x35z ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA1))
  | ( 0x00z, 0x3Cz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA256))
  | ( 0x00z, 0x3Dz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA256))

  (**************************************************************************)
  | ( 0x00z, 0x0Dz ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x10z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x13z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x16z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))

  | ( 0x00z, 0x30z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_128_CBC) SHA1))
  | ( 0x00z, 0x31z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))
  | ( 0x00z, 0x32z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA1))
  | ( 0x00z, 0x33z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))

  | ( 0x00z, 0x36z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_256_CBC) SHA1))
  | ( 0x00z, 0x37z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))
  | ( 0x00z, 0x38z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA1))
  | ( 0x00z, 0x39z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))

  | ( 0x00z, 0x3Ez ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_128_CBC) SHA256))
  | ( 0x00z, 0x3Fz ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))
  | ( 0x00z, 0x40z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA256))
  | ( 0x00z, 0x67z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))

  | ( 0x00z, 0x68z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_256_CBC) SHA256))
  | ( 0x00z, 0x69z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_256_CBC) SHA256))
  | ( 0x00z, 0x6Az ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA256))
  | ( 0x00z, 0x6Bz ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256))

  (**************************************************************************)
  | ( 0xc0z, 0x11z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1))
  | ( 0xc0z, 0x12z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0xc0z, 0x13z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))
  | ( 0xc0z, 0x14z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))
  | ( 0xc0z, 0x27z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))
  | ( 0xc0z, 0x28z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384))

  (**************************************************************************)
  | ( 0xc0z, 0x2bz ) -> Correct(CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_128_GCM SHA256))
  | ( 0xc0z, 0x2fz ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256))
  | ( 0xc0z, 0x2cz ) -> Correct(CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_256_GCM SHA384))
  | ( 0xc0z, 0x30z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384))

  (**************************************************************************)
  | ( 0xd0z, 0x01z ) -> Correct(CipherSuite Kex_PSK_ECDHE None (AEAD AES_128_GCM SHA256))
  | ( 0xd0z, 0x02z ) -> Correct(CipherSuite Kex_PSK_ECDHE None (AEAD AES_256_GCM SHA384))

  (**************************************************************************)
  | ( 0x00z, 0x18z ) -> Correct(CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5))
  | ( 0x00z, 0x1Bz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x34z ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA1))
  | ( 0x00z, 0x3Az ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA1))
  | ( 0x00z, 0x6Cz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA256))
  | ( 0x00z, 0x6Dz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA256))

  (**************************************************************************)
  | ( 0x00z, 0x9Cz ) -> Correct(CipherSuite Kex_RSA None (AEAD AES_128_GCM SHA256))
  | ( 0x00z, 0x9Dz ) -> Correct(CipherSuite Kex_RSA None (AEAD AES_256_GCM SHA384))

  | ( 0x00z, 0x9Ez ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256))
  | ( 0x00z, 0x9Fz ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384))
  | ( 0x00z, 0xA0z ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256))
  | ( 0x00z, 0xA1z ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384))

  | ( 0x00z, 0xA2z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256))
  | ( 0x00z, 0xA3z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384))
  | ( 0x00z, 0xA4z ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256))
  | ( 0x00z, 0xA5z ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384))

  | ( 0x00z, 0xA6z ) -> Correct(CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256))
  | ( 0x00z, 0xA7z ) -> Correct(CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384))

  (**************************************************************************)
  | ( 0x00z, 0xaaz ) -> Correct(CipherSuite Kex_PSK_DHE None (AEAD AES_128_GCM SHA256))
  | ( 0x00z, 0xabz ) -> Correct(CipherSuite Kex_PSK_DHE None (AEAD AES_256_GCM SHA384))

  (**************************************************************************)
  | ( 0x00z, 0xFFz ) -> Correct(SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV))
  | (b1, b2) -> Correct(UnknownCipherSuite b1 b2)
// Was:  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Parsed unknown cipher")

(** Parsing function for ciphersuites *)
val parseCipherSuite: pinverse_t cipherSuiteBytes
let parseCipherSuite b =
  match parseCipherSuiteAux b with
  | Correct c -> Correct c
  | Error z -> Error z


//#reset-options "--z3rlimit 60 --max_ifuel 6 --initial_ifuel 6 --max_fuel 1 --initial_fuel 1"

(** Lemma for ciphersuite serializing/parsing inversions *)
val inverse_cipherSuite: x:cipherSuite -> Lemma
  (requires (~ (UnknownCipherSuite? x)))
  // parse (bytes (Unknown 0 0)) = NullCiphersuite
  // must exclude this case...
  (ensures (let y = cipherSuiteBytesOpt x in
	(Some? y ==> parseCipherSuiteAux (Some?.v y) = Correct x)))
  [SMTPat (parseCipherSuiteAux (Some?.v (cipherSuiteBytesOpt x)))]
let inverse_cipherSuite x = ()

(** Lemma for ciphersuite serializing/parsing inversions *)
val pinverse_cipherSuite : x:lbytes 2 -> Lemma
  (requires (True))
  (ensures (let y = parseCipherSuiteAux x in
	    (Correct? y ==>
              (if UnknownCipherSuite? (Correct?._0 y) then true
              else Some? (cipherSuiteBytesOpt (Correct?._0 y))
               /\ Seq.equal x (Some?.v (cipherSuiteBytesOpt (Correct?._0 y)))))))
  [SMTPat (cipherSuiteBytesOpt (Correct?._0 (parseCipherSuiteAux x)))]
let pinverse_cipherSuite x = ()


#reset-options
#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 1 --initial_fuel 1"

(** Serializing function for a list of ciphersuite *)
val cipherSuitesBytes: css:list (c:cipherSuite{validCipherSuite c}) -> Tot (lbytes (op_Multiply 2 (List.Tot.length css)))
let rec cipherSuitesBytes css =
  match css with
  | [] -> empty_bytes
  | cs::css -> (cipherSuiteBytes cs) @| (cipherSuitesBytes css)

// Called by the server handshake;
// ciphersuites that we do not understand are parsed, but ignored

(** Parsing function for a list of ciphersuites *)
val parseCipherSuites: b:bytes -> Tot (result (list (c:cipherSuite{validCipherSuite c}))) (decreases (length b))
let rec parseCipherSuites b =
  if length b > 1 then
    let (b0,b1) = split b 2 in
    match parseCipherSuites b1 with
      | Correct(css) ->
	(match parseCipherSuite b0 with
	 | Error z ->	Correct css
	 | Correct cs -> Correct (cs::css))
      | Error z -> Error z
  else
  if length b = 0 then Correct []
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Odd cs bytes number")


#reset-options
#set-options "--max_ifuel 2 --initial_ifuel 2 --max_fuel 2 --initial_fuel 2"

(** Lemma for ciphersuite lists serializing/parsing inversions *)
val inverse_cipherSuites: x:list (c:cipherSuite{validCipherSuite c}) -> Lemma
  (requires (true))
  (ensures (parseCipherSuites (cipherSuitesBytes x) = Correct x))
  [SMTPat (parseCipherSuites (cipherSuitesBytes x))]
let rec inverse_cipherSuites x =
  match x with
  | [] -> ()
  | cs::css ->
     assume (~ (UnknownCipherSuite? cs)); // TODO enforce it
     let b = (cipherSuiteBytes cs) @| (cipherSuitesBytes css) in
     let (b0,b1) = split b 2 in
     lemma_append_inj b0 b1 (cipherSuiteBytes cs) (cipherSuitesBytes css);
     inverse_cipherSuite cs;
     inverse_cipherSuites css

// REMARK: cipherSuitesBytes is not a partial inverse of parseCipherSuites,
// because parseCipherSuites drops unknown ciphersuites.
// Alternatively, we could add an UNKNOWN of (lbyte 2) constructor in cipherSuite
// to make this hold.
//
// TODO: We added such constructor, so this is the case now. Prove it.


// Note:
// Migrated contentType to Content.fst (this is internal to TLS)

(** Transforms a sequence of natural numbers into bytes *)
val bytes_of_seq: n:nat{ repr_bytes n <= 8 } -> Tot bytes
let bytes_of_seq sn = bytes_of_int 8 sn

(** Transforms bytes into a sequence of natural numbers *)
val seq_of_bytes: b:bytes{ length b <= 8 } -> Tot nat
let seq_of_bytes b = int_of_bytes b

(** Transform and concatenate a natural number to bytes *)
val vlbytes: lSize:nat -> b:bytes{repr_bytes (length b) <= lSize} -> Tot (r:bytes{length r = lSize + length b})
let vlbytes lSize b = bytes_of_int lSize (length b) @| b

(** Lemmas associated to bytes manipulations *)
val lemma_vlbytes_len : i:nat -> b:bytes{repr_bytes (length b) <= i}
  -> Lemma (ensures (length (vlbytes i b) = i + length b))
let lemma_vlbytes_len i b = ()

val lemma_vlbytes_inj : i:nat
  -> b:bytes{repr_bytes (length b) <= i}
  -> b':bytes{repr_bytes (length b') <= i}
  -> Lemma (requires (Seq.equal (vlbytes i b) (vlbytes i b')))
          (ensures (b == b'))
let lemma_vlbytes_inj i b b' =
  let l = bytes_of_int i (length b) in
  SeqProperties.lemma_append_inj l b l b'

val vlbytes_length_lemma: n:nat -> a:bytes{repr_bytes (length a) <= n} -> b:bytes{repr_bytes (length b) <= n} -> 
  Lemma (requires (Seq.equal (Seq.slice (vlbytes n a) 0 n) (Seq.slice (vlbytes n b) 0 n)))
        (ensures (length a = length b))
let vlbytes_length_lemma n a b = 
  let lena = Seq.slice (vlbytes n a) 0 n in
  let lenb = Seq.slice (vlbytes n b) 0 n in
  assert(Seq.equal lena (bytes_of_int n (length a)));
  assert(Seq.equal lenb (bytes_of_int n (length b)));
  int_of_bytes_of_int n (length a); int_of_bytes_of_int n (length b)


#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 0 --initial_fuel 0"   //need to reason about length


val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:bytes{lSize <= length vlb}
  -> Tot (result (b:(bytes * bytes){
                    repr_bytes (length (fst b)) <= lSize
                  /\ Seq.equal vlb (vlbytes lSize (fst b) @| (snd b))}))
let vlsplit lSize vlb =
  let (vl,b) = Platform.Bytes.split vlb lSize in
  let l = int_of_bytes vl in
  if l <= length b
  then Correct(Platform.Bytes.split b l)
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


val vlparse: lSize:nat{lSize <= 4} -> vlb:bytes{lSize <= length vlb}
  -> Tot (result (b:bytes{repr_bytes (length b) <= lSize /\ Seq.equal vlb (vlbytes lSize b)}))
let vlparse lSize vlb =
  let vl,b = split vlb lSize in
  if int_of_bytes vl = length b
  then Correct b
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


val vlparse_vlbytes: lSize:nat{lSize <= 4} -> vlb:bytes{repr_bytes (length vlb) <= lSize} -> Lemma 
  (requires (True))
  (ensures (vlparse lSize (vlbytes lSize vlb) == Correct vlb))
  [SMTPat (vlparse lSize (vlbytes lSize vlb))]
let vlparse_vlbytes lSize vlb =
  let vl,b = split (vlbytes lSize vlb) lSize in
  assert (Seq.equal vl (bytes_of_int lSize (length vlb)));
  int_of_bytes_of_int lSize (length vlb);
  match vlparse lSize (vlbytes lSize vlb) with
  | Error z   -> ()
  | Correct b -> lemma_vlbytes_inj lSize vlb b

(** Serializing function for the certificate type *)
val certTypeBytes: certType -> Tot (lbytes 1)
let certTypeBytes ct =
  match ct with
  | RSA_sign     -> abyte 1z
  | DSA_sign     -> abyte 2z
  | RSA_fixed_dh -> abyte 3z
  | DSA_fixed_dh -> abyte 4z

(** Parsing function for the certificate type *)
val parseCertType: pinverse_t certTypeBytes
let parseCertType b =
  match cbyte b with
  | 1z -> Correct RSA_sign
  | 2z -> Correct DSA_sign
  | 3z -> Correct RSA_fixed_dh
  | 4z -> Correct DSA_fixed_dh
  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


(** Lemmas associated to serializing/parsing of certificate types *)
val inverse_certType: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f certTypeBytes parseCertType x)
  [SMTPat (parseCertType (certTypeBytes x))]
let inverse_certType x = ()

val pinverse_certType: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal certTypeBytes parseCertType x))
  [SMTPat (certTypeBytes (Correct?._0 (parseCertType x)))]
let pinverse_certType x = ()


#set-options "--max_fuel 1 --initial_fuel 1"

(** Serializing function for lists of certificate types *)
val certificateTypeListBytes: ctl:list certType -> Tot (lbytes (List.Tot.length ctl))
let rec certificateTypeListBytes ctl =
  match ctl with
  | [] -> empty_bytes
  | h::t ->
    let ct = certTypeBytes h in
    ct @| certificateTypeListBytes t

(** Parsing function for lists of certificate types *)
val parseCertificateTypeList: data:bytes -> Tot (list certType) (decreases (length data))
let rec parseCertificateTypeList data =
  if length data = 0 then []
  else
    let (thisByte,data) = Platform.Bytes.split data 1 in
    match parseCertType thisByte with
    | Error z -> // we skip this one
      parseCertificateTypeList data
    | Correct ct ->
      let rem = parseCertificateTypeList data in
      ct :: rem


(** Serializing function for a list of Distinguished Names of certificates *)
val distinguishedNameListBytes: names:list dn -> Tot (b:bytes{length b <= op_Multiply 258 (List.Tot.length names)})
let rec distinguishedNameListBytes names =
  match names with
  | [] -> empty_bytes
  | h::t ->
    lemma_repr_bytes_values (length (utf8 h));
    let name = vlbytes 2 (utf8 h) in
    name @| distinguishedNameListBytes t

(** Parsing function for a list of Distinguished Names of certificates *)
val parseDistinguishedNameList: data:bytes -> res:list dn -> Tot (result (list dn)) (decreases (length data))
let rec parseDistinguishedNameList data res =
  if length data = 0 then
    Correct res
  else
    if length data < 2 then
      Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else
      match vlsplit 2 data with
      | Error z -> Error z
      | Correct (nameBytes,data) ->
        begin
	match iutf8_opt nameBytes with
        | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        | Some name ->
	  if length (utf8 name) < 256 then
          let res = name :: res in
          parseDistinguishedNameList data res
	  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        end

(** Serializing function for (EC)DHE named groups *)
val namedGroupBytes: namedGroup -> Tot (lbytes 2)
let namedGroupBytes ng =
  match ng with
  | SEC ec ->
    begin
    match ec with
    | ECC_P256		-> abyte2 (0x00z, 0x17z)
    | ECC_P384		-> abyte2 (0x00z, 0x18z)
    | ECC_P521		-> abyte2 (0x00z, 0x19z)
    end
  | EC_UNSUPPORTED b	-> abyte2 (0x00z, b)
  | FFDHE dhe ->
    begin
    match dhe with
    | FFDHE2048		-> abyte2 (0x01z, 0x00z)
    | FFDHE3072		-> abyte2 (0x01z, 0x01z)
    | FFDHE4096		-> abyte2 (0x01z, 0x02z)
    | FFDHE6144		-> abyte2 (0x01z, 0x03z)
    | FFDHE8192		-> abyte2 (0x01z, 0x04z)
    end
  | FFDHE_PRIVATE_USE b -> abyte2 (0x01z, b)
  | ECDHE_PRIVATE_USE b -> abyte2 (0xFEz, b)

(** Parsing function for (EC)DHE named groups *)
val parseNamedGroup: pinverse_t namedGroupBytes
let parseNamedGroup b =
  match cbyte2 b with
  | (0x00z, 0x17z) -> Correct (SEC ECC_P256)
  | (0x00z, 0x18z) -> Correct (SEC ECC_P384)
  | (0x00z, 0x19z) -> Correct (SEC ECC_P521)
  | (0x00z, b)     -> Correct (EC_UNSUPPORTED b) // REMARK: only values 0x01z-0x16z and 0x1Az-0x1Ez are assigned
  | (0x01z, 0x00z) -> Correct (FFDHE FFDHE2048)
  | (0x01z, 0x01z) -> Correct (FFDHE FFDHE3072)
  | (0x01z, 0x02z) -> Correct (FFDHE FFDHE4096)
  | (0x01z, 0x03z) -> Correct (FFDHE FFDHE6144)
  | (0x01z, 0x04z) -> Correct (FFDHE FFDHE8192)
  | (0x01z, b)     ->
    if b = 0xFCz || b = 0xFDz || b = 0xFEz || b = 0xFFz
    then Correct (FFDHE_PRIVATE_USE b)
    else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong ffdhe private use group")
  | (0xFEz, b)     -> Correct (ECDHE_PRIVATE_USE b)
  | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong named group")

(** Lemmas for named groups parsing/serializing inversions *)
val inverse_namedGroup: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f namedGroupBytes parseNamedGroup x)
  [SMTPat (parseNamedGroup (namedGroupBytes x))]
let inverse_namedGroup x = ()

val pinverse_namedGroup: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal namedGroupBytes parseNamedGroup x))
  [SMTPat (namedGroupBytes (Correct?._0 (parseNamedGroup x)))]
let pinverse_namedGroup x = ()


private val namedGroupsBytes0: groups:list namedGroup
  -> Tot (b:bytes { length b = op_Multiply 2 (List.Tot.length groups)})
let rec namedGroupsBytes0 groups =
  match groups with
  | [] -> empty_bytes
  | g::gs -> namedGroupBytes g @| namedGroupsBytes0 gs

(** Serialization function for a list of named groups *)
val namedGroupsBytes: groups:list namedGroup{List.Tot.length groups < 65536/2}
  -> Tot (b:bytes { length b = 2 + op_Multiply 2 (List.Tot.length groups)})
let namedGroupsBytes groups =
  let gs = namedGroupsBytes0 groups in
  lemma_repr_bytes_values (length gs);
  vlbytes 2 gs

private val parseNamedGroups0: b:bytes -> l:list namedGroup
  -> Tot (result (groups:list namedGroup{List.Tot.length groups = List.Tot.length l + length b / 2}))
  (decreases (length b))
let rec parseNamedGroups0 b groups =
  if length b > 0 then
    if length b >= 2 then
      let (ng, bytes) = split b 2 in
      lemma_split b 2;
      match parseNamedGroup ng with
      |Correct ng ->
        let groups' = ng :: groups in
        parseNamedGroups0 bytes groups'
      | Error z    -> Error z
    else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  else
   let grev = List.Tot.rev groups in
   assume (List.Tot.length grev == List.Tot.length groups);
   Correct grev

(** Parsing function for a list of named groups *)
val parseNamedGroups: b:bytes { 2 <= length b /\ length b < 65538 }
  -> Tot (result (groups:list namedGroup{List.Tot.length groups = (length b - 2) / 2}))
let parseNamedGroups b =
  match vlparse 2 b with
  | Correct b -> parseNamedGroups0 b []
  | Error z   ->
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse named groups")


(** Serializing function for the configuration identifier *)
val configurationIdBytes: configurationId -> Tot (b:bytes{2 < length b /\ length b < 65538})
let configurationIdBytes cid =
  lemma_repr_bytes_values (length cid);
  vlbytes 2 cid

(** Parsing function for the configuration identifier *)
val parseConfigurationId: pinverse_t configurationIdBytes
let parseConfigurationId b =
  match vlparse 2 b with
  | Error z -> Error z
  | Correct b -> Correct b

(** Lemmas for configurationId serializing/parsing inversion *)
val inverse_configurationId: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f configurationIdBytes parseConfigurationId x)
  [SMTPat (parseConfigurationId (configurationIdBytes x))]
let inverse_configurationId x =
  lemma_repr_bytes_values (length x)

val pinverse_configurationId: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal configurationIdBytes parseConfigurationId x))
  [SMTPat (configurationIdBytes (Correct?._0 (parseConfigurationId x)))]
let pinverse_configurationId x = ()


//
// BB.TODO: Some of the following code should be moved outside TLSConstants !
//          In particular, the integer definitions can be taken from F* ulib.

type uint32 = b:lbytes 4

val uint32Bytes: uint32 -> Tot (lbytes 4)
let uint32Bytes u = u

val parseUint32: pinverse_t uint32Bytes
let parseUint32 b =
  if length b = 4 then Correct(b)
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_uint32: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f uint32Bytes parseUint32 x)
  [SMTPat (parseUint32 (uint32Bytes x))]
let inverse_uint32 x = ()

val pinverse_uint32: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal uint32Bytes parseUint32 x))
  [SMTPat (uint32Bytes (Correct?._0 (parseUint32 x)))]
let pinverse_uint32 x = ()



(** Serializing function for Early Data values *)
val earlyDataTypeBytes: earlyDataType -> Tot (lbytes 1)
let earlyDataTypeBytes edt =
  match edt with
  | ClientAuthentication        -> abyte 1z
  | EarlyData                   -> abyte 2z
  | ClientAuthenticationAndData -> abyte 3z

(** Parsing function for Early Data values *)
val parseEarlyDataType: pinverse_t earlyDataTypeBytes
let parseEarlyDataType b =
  match cbyte b with
  | 1z -> Correct ClientAuthentication
  | 2z -> Correct EarlyData
  | 3z -> Correct ClientAuthenticationAndData
  | _  -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse early data type")


(** Lemmas for Early Data parsing/serializing inversions *)
val inverse_earlyDataType: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f earlyDataTypeBytes parseEarlyDataType x)
  [SMTPat (parseEarlyDataType (earlyDataTypeBytes x))]
let inverse_earlyDataType x = ()

val pinverse_earlyDataType: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal earlyDataTypeBytes parseEarlyDataType x))
  [SMTPat (earlyDataTypeBytes (Correct?._0 (parseEarlyDataType x)))]
let pinverse_earlyDataType x = ()


// TODO: Should we strengthen the result type to b:bytes{length b >= 4}?
(** Serialization of the configuration extension values *)
val configurationExtensionBytes: ce:configurationExtension -> Tot bytes
let configurationExtensionBytes ce =
  match ce with
  | UnknownConfigurationExtension typ payload -> typ @| vlbytes 2 payload

(** Parsing of the configuration extension values *)
val parseConfigurationExtension: pinverse_t configurationExtensionBytes
let parseConfigurationExtension b =
  if length b >= 4 then
    let (typ,payload) = split b 2 in
    match vlparse 2 payload with
    | Correct payload -> Correct (UnknownConfigurationExtension typ payload)
    | Error z -> Error z
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse a configuration extension")


(** Lemmas for Configuration Extension parsing/serializing inversions *)
val inverse_configurationExtension: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f configurationExtensionBytes parseConfigurationExtension x)
  [SMTPat (parseConfigurationExtension (configurationExtensionBytes x))]
let inverse_configurationExtension x =
  match x with
  | UnknownConfigurationExtension typ payload ->
  let b = typ @| vlbytes 2 payload in
  let b0,b1 = split b 2 in
  let vl,b = split b1 2 in
  vlparse_vlbytes 2 b;
  assert (Seq.equal vl (bytes_of_int 2 (length b)));
  assert (Seq.equal b0 typ);
  assert (Seq.equal b payload)

val pinverse_configurationExtension: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal configurationExtensionBytes parseConfigurationExtension x))
  [SMTPat (configurationExtensionBytes (Correct?._0 (parseConfigurationExtension x)))]
let pinverse_configurationExtension x = ()


// TODO: Choice, truncate when maximum length is exceeded
(** Serialization of the configuration extension list of values *)
val configurationExtensionsBytes: list configurationExtension -> Tot bytes
let configurationExtensionsBytes ce =
  let rec configurationExtensionsBytes_aux (b:bytes{length b < 65536}) (ces:list configurationExtension): Tot (b:bytes{length b < 65536}) (decreases ces) =
  match ces with
  | [] -> b
  | ce::ces ->
    if length (b @| configurationExtensionBytes ce) < 65536 then
      configurationExtensionsBytes_aux (b @| configurationExtensionBytes ce) ces
    else b
  in
  let b = configurationExtensionsBytes_aux empty_bytes ce in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

(** Parsing of the configuration extension list of values *)
val parseConfigurationExtensions: pinverse_t configurationExtensionsBytes
let parseConfigurationExtensions b =
  let rec (aux: b:bytes -> list configurationExtension -> Tot (result (list configurationExtension)) (decreases (length b))) =
    fun b exts ->
    if length b > 0 then
      if length b >= 4 then
	let typ, len, data = split2 b 2 2 in
	let len = int_of_bytes len in
	if length b >= 4 + len then
	  let ext, bytes = split b len in
	  match parseConfigurationExtension ext with
	  | Correct(ext') -> aux bytes (ext'::exts)
	  | Error(z) -> Error(z)
	else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse configuration extension length")
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Configuration extension length should be at least 4")
    else Correct(exts) in
  if length b >= 2 then
  match vlparse 2 b with
  | Correct (b) ->  aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse configuration extension")
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse configuration extension")


(** Serializing function for the Signature algorithm *)
val sigHashAlgBytes: sigHashAlg -> Tot (lbytes 2)
let sigHashAlgBytes sha =
  let sign = sigAlgBytes (fst sha) in
  let hash = hashAlgBytes (snd sha) in
  hash @| sign

val sigSchemeBytes: sigScheme -> Tot (lbytes 2)
let sigSchemeBytes ss = 
  match ss with
  | SigHashAlg sha -> sigHashAlgBytes sha
  | RSA_PSS_SHA256 -> abyte2(0x08z, 0x04z)
  | RSA_PSS_SHA384 -> abyte2(0x08z, 0x05z)
  | RSA_PSS_SHA512 -> abyte2(0x08z, 0x06z)
  | ED25519 -> abyte2(0x08z, 0x07z)
  | ED448 -> abyte2(0x08z, 0x08z)

(** Parsing function for the Signature algorithm *)
val parseSigHashAlg: pinverse_t sigHashAlgBytes
let parseSigHashAlg b =
  let hash,sign = split b 1 in
  match parseSigAlg sign with
  | Correct sign ->
    begin
    match parseHashAlg hash with
    | Correct hash -> Correct(sign, hash)
    | Error z -> Error z
    end
  | Error z -> Error z

val parseSigScheme: pinverse_t sigSchemeBytes
let parseSigScheme b = 
  match cbyte2 b with
  | (0x08z, 0x04z) -> Correct(RSA_PSS_SHA256)
  | (0x08z, 0x05z) -> Correct(RSA_PSS_SHA384)
  | (0x08z, 0x06z) -> Correct(RSA_PSS_SHA512)
  | (0x08z, 0x07z) -> Correct(ED25519)
  | (0x08z, 0x08z) -> Correct(ED448)
  | _ -> (match parseSigHashAlg b with
          | Error p -> Error p 
	  | Correct(s,h) -> Correct(SigHashAlg(s,h)))
    
// TODO: Moving this inside sigHashAlgsBytes gives a `Bound term variable not found` error
// See https://github.com/FStarLang/FStar/issues/533

(** Serializing function for a Signature algorithm list *)
val sigHashAlgsBytes: algs:list sigHashAlg{List.Tot.length algs < 65536/2}
  -> Tot (b:bytes{2 <= length b /\ length b < 65538})
let sigHashAlgsBytes algs =
  let rec sigHashAlgsBytes_aux: b:bytes
    -> algs:list sigHashAlg{b2t (length b + op_Multiply 2 (List.Tot.length algs) < 65536)}
    -> Tot (r:bytes{length r < 65536}) (decreases algs) = fun b algs ->
    match algs with
    | [] -> b
    | alg::algs' ->
      let shb = sigHashAlgBytes alg in
      sigHashAlgsBytes_aux (shb @| b) algs'
  in
  let b = sigHashAlgsBytes_aux empty_bytes algs in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

(** Parsing function for a Signature algorithm list *)
val parseSigHashAlgs: pinverse_t sigHashAlgsBytes
let parseSigHashAlgs b =
  let rec aux: b:bytes -> algs:list sigHashAlg{length b + op_Multiply 2 (List.Tot.length algs) < 65536} -> Tot (result (l:list sigHashAlg{List.Tot.length l < 65536/2})) (decreases (length b)) = fun b algs ->
    if length b > 0 then
      if length b >= 2 then
      let alg,bytes = split b 2 in
      match parseSigHashAlg alg with
      | Correct sha -> aux bytes (sha::algs)
      | Error z     -> Error z
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse sig hash algs")
    else Correct algs in
  match vlparse 2 b with
  | Correct b -> aux b []
  | Error z   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse sig hash algs")


val sigSchemesBytes: algs:list sigScheme{List.Tot.length algs < 65536/2}
  -> Tot (b:bytes{2 <= length b /\ length b < 65538})
let sigSchemesBytes algs =
  let rec sigSchemesBytes_aux: b:bytes
    -> algs:list sigScheme{b2t (length b + op_Multiply 2 (List.Tot.length algs) < 65536)}
    -> Tot (r:bytes{length r < 65536}) (decreases algs) = fun b algs ->
    match algs with
    | [] -> b
    | alg::algs' ->
      let shb = sigSchemeBytes alg in
      sigSchemesBytes_aux (shb @| b) algs'
  in
  let b = sigSchemesBytes_aux empty_bytes algs in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

val parseSigSchemes: pinverse_t sigSchemesBytes
let parseSigSchemes b =
  let rec aux: b:bytes -> algs:list sigScheme{length b + op_Multiply 2 (List.Tot.length algs) < 65536} -> Tot (result (l:list sigScheme{List.Tot.length l < 65536/2})) (decreases (length b)) = fun b algs ->
    if length b > 0 then
      if length b >= 2 then
      let alg,bytes = split b 2 in
      match parseSigScheme alg with
      | Correct sha -> aux bytes (sha::algs)
      | Error z     -> Error z
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse sig hash algs")
    else Correct algs in
  match vlparse 2 b with
  | Correct b -> aux b []
  | Error z   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse sig hash algs")


(** Serializing function for a KeyShareEntry *)
val keyShareEntryBytes: keyShareEntry -> Tot (b:bytes{4 <= length b})
let keyShareEntryBytes (ng, b) =
  let ng_bytes = namedGroupBytes ng in
  ng_bytes @| vlbytes 2 b

(** Parsing function for a KeyShareEntry *)
val parseKeyShareEntry: pinverse_t keyShareEntryBytes
let parseKeyShareEntry b =
  let ng,key_exchange = split b 2 in
  match parseNamedGroup ng with
  | Correct ng ->
    begin
    match vlparse 2 key_exchange with
    | Correct ke -> Correct (ng, ke)
    | Error z    -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry")
    end
  | Error z -> Error z


(** Lemmas for KeyShare entries parsing/serializing inversions *)
val inverse_keyShareEntry: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f keyShareEntryBytes parseKeyShareEntry x)
  [SMTPat (parseKeyShareEntry (keyShareEntryBytes x))]
let inverse_keyShareEntry (ng, x) =
  let b = namedGroupBytes ng @| vlbytes 2 x in
  let b0,b1 = split b 2 in
  let vl,b = split b1 2 in
  vlparse_vlbytes 2 b;
  assert (Seq.equal vl (bytes_of_int 2 (length b)));
  assert (Seq.equal b0 (namedGroupBytes ng));
  assert (Seq.equal b x)

val pinverse_keyShareEntry: x:_ -> Lemma
  (requires (True))
  (ensures lemma_pinverse_f_g Seq.equal keyShareEntryBytes parseKeyShareEntry x)
  [SMTPat (keyShareEntryBytes (Correct?._0 (parseKeyShareEntry x)))]
let pinverse_keyShareEntry x = ()


// Choice: truncate when maximum length is exceeded
(** Serializing function for a list of KeyShareEntry *)
val keyShareEntriesBytes: list keyShareEntry -> Tot (b:bytes{2 <= length b /\ length b < 65538})
let keyShareEntriesBytes kes =
  let rec keyShareEntriesBytes_aux (b:bytes{length b < 65536}) (kes:list keyShareEntry): Tot (b:bytes{length b < 65536}) (decreases kes) =
  match kes with
  | [] -> b
  | ke::kes ->
    let b' = b @| keyShareEntryBytes ke in
    if length b' < 65536 then
      keyShareEntriesBytes_aux b' kes
    else b
  in
  let b = keyShareEntriesBytes_aux empty_bytes kes in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

(** Parsing function for a list KeyShareEntry *)
val parseKeyShareEntries: pinverse_t keyShareEntriesBytes
let parseKeyShareEntries b =
  let rec (aux: b:bytes -> list keyShareEntry -> Tot (result (list keyShareEntry)) (decreases (length b))) = fun b entries ->
    if length b > 0 then
      if length b >= 4 then
	let ng, data = split b 2 in
	match vlsplit 2 data with
	| Correct(kex, bytes) ->
	  begin
	  match parseKeyShareEntry (ng @| vlbytes 2 kex) with
	  | Correct entry -> aux bytes (entries @ [entry])
	  | Error z -> Error z
	  end
	| Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry")
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse key share entries")
    else Correct entries in
  match vlparse 2 b with
  | Correct b -> aux b []
  | Error z   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entries")

(** Serializing function for a ClientKeyShare *)
val clientKeyShareBytes: clientKeyShare -> Tot (b:bytes{ 2 <= length b /\ length b < 65538 })
let clientKeyShareBytes cks = keyShareEntriesBytes cks

(** Parsing function for a ClientKeyShare *)
val parseClientKeyShare: b:bytes{ 2 <= length b /\ length b < 65538 }
  -> Tot (result clientKeyShare)
let parseClientKeyShare b =
  match parseKeyShareEntries b with
  | Correct kes ->
    if List.Tot.length kes < 65536/4
    then Correct kes
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse client key share entries")
  | Error z -> Error z

(** Serializing function for a ServerKeyShare *)
val serverKeyShareBytes: serverKeyShare -> Tot (b:bytes{ 4 <= length b })
let serverKeyShareBytes sks = keyShareEntryBytes sks

(** Parsing function for a ServerKeyShare *)
val parseServerKeyShare: pinverse_t serverKeyShareBytes
let parseServerKeyShare b = parseKeyShareEntry b

(** Serializing function for a KeyShare *)
val keyShareBytes: keyShare -> Tot bytes
let keyShareBytes = function
  | ClientKeyShare cks -> clientKeyShareBytes cks
  | ServerKeyShare sks -> serverKeyShareBytes sks

(** Parsing function for a KeyShare *)
val parseKeyShare: bool -> bytes -> Tot (result keyShare)
let parseKeyShare is_client b =
  if is_client then
    begin
    if 2 <= length b && length b < 65538 then
      begin
      match parseClientKeyShare b with
      | Correct kse -> Correct (ClientKeyShare kse)
      | Error z -> Error z
      end
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share")
    end
  else
    if 4 <= length b then
      begin
      match parseServerKeyShare b with
      | Correct ks -> Correct (ServerKeyShare ks)
      | Error z -> Error z
      end
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share")

(** Serializing function for a PSK Identity *)
val pskIdentityBytes: pskIdentity -> Tot (b:bytes{length b >= 2})
let pskIdentityBytes pski =
  vlbytes 2 pski

(** Parsing function for a PSK Identity *)
val parsePskIdentity: pinverse_t pskIdentityBytes
let parsePskIdentity b =
  match vlparse 2 b with
  | Correct vlb -> Correct vlb
  | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse psk_identity")


// TODO: Choice, truncate when maximum length is exceeded

(** Serializing function for a list of PSK Identity *)
val pskIdentitiesBytes: list pskIdentity -> Tot (b:bytes{2 <= length b /\ length b < 65538})
let pskIdentitiesBytes ids =
  let rec pskIdentitiesBytes_aux (b:bytes{length b < 65536}) (ids:list pskIdentity): Tot (b:bytes{length b < 65536}) (decreases ids) =
  match ids with
  | [] -> b
  | id::ids ->
    let b' = b @| pskIdentityBytes id in
    if length b' < 65536 then
      pskIdentitiesBytes_aux b' ids
    else b
  in
  let b = pskIdentitiesBytes_aux empty_bytes ids in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

(** Parsing function for a list of PSK Identity *)
val parsePskIdentities: pinverse_t pskIdentitiesBytes
let parsePskIdentities b =
  let rec (aux: b:bytes -> list pskIdentity -> Tot (result (list pskIdentity)) (decreases (length b))) = fun b ids ->
    if length b > 0 then
      if length b >= 2 then
	let len, data = split b 2 in
	let len = int_of_bytes len in
	if length b >= len then
	  let pski,bytes = split b len in
	  if length pski >= 2 then
   	    match parsePskIdentity pski with
   	    | Correct id -> aux bytes (id::ids)
   	    | Error z -> Error z
	  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse psk identity length")
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse psk identity length")
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Expected psk identity to be at least 2 bytes long")
    else Correct ids in
  match vlparse 2 b with
  | Correct b -> aux b []
  | Error z   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse psk identities")


(** Serializing function for ClientPreSharedKey *)
val clientPreSharedKeyBytes: clientPreSharedKey -> Tot (b:bytes{ 2 <= length b /\ length b < 65538 })
let clientPreSharedKeyBytes cpsk = pskIdentitiesBytes cpsk

(** Parsing function for ClientPreSharedKey *)
val parseClientPreSharedKey: b:bytes{ 2 <= length b /\ length b < 65538 }
  -> Tot (result clientPreSharedKey)
let parseClientPreSharedKey b =
  match parsePskIdentities b with
  | Correct ids ->
    let l = List.Tot.length ids in
    if 1 <= l && l < 65536/2
    then Correct ids
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse client psk identities")
  | Error z -> Error z

(** Serializing function for ServerPreSharedKey *)
val serverPreSharedKeyBytes: serverPreSharedKey -> Tot (b:bytes{ 2 <= length b })
let serverPreSharedKeyBytes cpsk = pskIdentityBytes cpsk

(** Parsing function for ServerPreSharedKey *)
val parseServerPreSharedKey: pinverse_t serverPreSharedKeyBytes
let parseServerPreSharedKey b = parsePskIdentity b

(** Serializing function for PreSharedKey *)
val preSharedKeyBytes: preSharedKey -> Tot (b:bytes{length b >= 2})
let preSharedKeyBytes = function
  | ClientPreSharedKey cpsk -> clientPreSharedKeyBytes cpsk
  | ServerPreSharedKey spsk -> serverPreSharedKeyBytes spsk

(** Parsing function for PreSharedKey *)
val parsePreSharedKey: pinverse_t preSharedKeyBytes
let parsePreSharedKey b =
  match vlparse 2 b with
  | Correct b' ->
    begin
      match vlparse 2 b with
      | Correct b'' -> // Client case
	begin
	if length b >= 2 && length b < 65538 then
	  begin
	  match parseClientPreSharedKey b with
	  | Correct psks -> Correct (ClientPreSharedKey psks)
	  | Error z -> Error z
	  end
	else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse  psk")
	end
      | Error _ -> // Server case
	begin
	match parseServerPreSharedKey b with
	| Correct psk -> Correct (ServerPreSharedKey psk)
	| Error z -> Error z
	end
    end
  | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse pre shared key")


(* From DHGroup *)
val serialize_dh: DHGroup.params -> DHGroup.share -> Tot bytes
let serialize_dh dhp dh_Y =
  lemma_repr_bytes_values (length (dhp.dh_p));
  lemma_repr_bytes_values (length (dhp.dh_g));
  lemma_repr_bytes_values (length dh_Y);
  let pb  = vlbytes 2 dhp.dh_p in 
  let gb  = vlbytes 2 dhp.dh_g in
  let pkb = vlbytes 2 dh_Y in
  pb @| gb @| pkb

val serialize_dh_public: s:DHGroup.share -> len:nat{len < 65536 /\ length s <= len}
  -> Tot (lbytes len)
let serialize_dh_public dh_Y len =
  let padded_dh_Y = createBytes (len - length dh_Y) 0z @| dh_Y in
  lemma_repr_bytes_values len;
  padded_dh_Y

val parse_dh_public: p:bytes{2 <= length p} -> Tot (result DHGroup.share)
let parse_dh_public p =
  match vlparse 2 p with
  | Correct n -> lemma_repr_bytes_values (length n); Correct n
  | Error z -> Error z

val parse_dh_partial: bytes -> Tot (result (DHGroup.key * bytes))
let parse_dh_partial payload = 
  if length payload >= 2 then
    match vlsplit 2 payload with
    | Error(z) -> Error(z)
    | Correct(p, payload) ->
      if length payload >= 2 then
        match vlsplit 2 payload with
        | Error(z) -> Error(z)
        | Correct(g, payload) ->
          if length payload >= 2 then
            match vlsplit 2 payload with
            | Error(z) -> Error(z)
            | Correct(gy, rem) ->
              if length gy <= length p then
                let dhp = {dh_p = p; dh_g = g; dh_q = None; safe_prime = false} in
                let dhk = {dh_params = dhp; dh_public = gy; dh_private = None} in
                lemma_repr_bytes_values (length p);
                lemma_repr_bytes_values (length g);
                Correct (dhk,rem)
              else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
          else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


(* From ECGroup *)
val parse_curve: bytes -> Tot (option ECGroup.params)
let parse_curve b =
  if length b = 3 then
    let (ty, id) = split b 1 in
    if cbyte ty = 3z then
      match cbyte2 id with
      | (0z, 23z) -> Some (ECGroup.params_of_group ECC_P256)
      | (0z, 24z) -> Some (ECGroup.params_of_group ECC_P384)
      | (0z, 25z) -> Some (ECGroup.params_of_group ECC_P521)
      | _ -> None
    else None
  else None

val curve_id: ECGroup.params -> Tot (lbytes 2)
let curve_id p =
  abyte2 (match p.curve with
  | ECC_P256 -> (0z, 23z)
  | ECC_P384 -> (0z, 24z)
  | ECC_P521 -> (0z, 25z))

val parse_ec_point: ECGroup.params -> bytes -> Tot (option ECGroup.share)
let parse_ec_point p b =
  let clen = ec_bytelen p.curve in 
  if length b = (op_Multiply 2 clen) + 1 then
    let (et, ecxy) = split b 1 in
    match cbyte et with
    | 4z ->
      let (x,y) = split ecxy clen in
      let e = {ecx = x; ecy = y;} in
      if CoreCrypto.ec_is_on_curve p e then Some e else None
    |_ -> None
  else None

val parse_ec_partial: bytes -> Tot (TLSError.result ( ECGroup.key * bytes ))
let parse_ec_partial payload = 
    if length payload >= 7 then
      let (curve, point) = split payload 3 in
      match parse_curve curve with
      | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Unsupported curve")
      | Some(ecp) ->
        match vlsplit 1 point with
        | Error(z) -> Error(z)
        | Correct(rawpoint, rem) ->
           match parse_ec_point ecp rawpoint with
           | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ("Invalid EC point received:"^(Platform.Bytes.print_bytes rawpoint)))
           | Some p -> Correct ({ec_params = ecp; ec_point = p; ec_priv = None},rem)
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

(* Assumes uncompressed point format for now (04||ecx||ecy) *) 
val serialize_ec_point: p:ECGroup.params 
  -> e:ECGroup.share{length e.ecx = ec_bytelen p.curve /\ length e.ecy = ec_bytelen p.curve}
  -> Tot (b:bytes{length b = FStar.Mul.(2 * ec_bytelen p.curve) + 1})
let serialize_ec_point p e =
  let pc = abyte 4z in
  let x = pc @| e.ecx @| e.ecy in
  x

val serialize_ec: p:ECGroup.params
  -> e:ECGroup.share{length e.ecx = ec_bytelen p.curve /\ length e.ecy = ec_bytelen p.curve}
  -> Tot (b:bytes{length b = op_Multiply 2 (ec_bytelen p.curve) + 5})
let serialize_ec ecp ecdh_Y =
  let ty = abyte 3z in
  let id = curve_id ecp in
  let e = serialize_ec_point ecp ecdh_Y in
  lemma_repr_bytes_values (length e);
  let ve = vlbytes 1 e in
  ty @| id @| ve


(* KB: older more general code below 
let getParams (c : ec_curve) : ec_params = 
    let rawcurve : ec_prime = match c with
    | ECC_P256 ->
        {
            ecp_prime = "115792089210356248762697446949407573530086143415290314195533631308867097853951";
            ecp_order = "115792089210356248762697446949407573529996955224135760342422259061068512044369";
            ecp_a = "115792089210356248762697446949407573530086143415290314195533631308867097853948"; // p-3
            ecp_b = "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b";
            ecp_gx = "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
            ecp_gy = "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5";
            ecp_bytelen = 32;
            ecp_id = abyte2 (0z, 23z);
        }
    | ECC_P384 ->
        {
            ecp_prime = "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319";
            ecp_order = "39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643";
            ecp_a = "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112316"; // p-3
            ecp_b = "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef";
            ecp_gx = "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7";
            ecp_gy = "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f";
            ecp_bytelen = 48;
            ecp_id = abyte2 (0z, 24z);
        }
    | ECC_P521 ->
        {
            ecp_prime = "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151";
            ecp_order = "6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449";
            ecp_a = "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057148"; // p-3
            ecp_b = "051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00";
            ecp_gx = "0c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66";
            ecp_gy = "11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650";
            ecp_bytelen = 66;
            ecp_id = abyte2 (0z, 25z);
        }
    in { curve = EC_PRIME rawcurve; point_compression = false; }
*)

(* From CommonDH *)
// Serialize in KeyExchange message format
val serialize: CommonDH.key -> Tot bytes
let serialize k = 
  match k with
  | CommonDH.FFKey k -> serialize_dh k.dh_params k.dh_public
  | CommonDH.ECKey k -> serialize_ec k.ec_params k.ec_point

val parse_partial: bytes -> bool -> Tot (TLSError.result (CommonDH.key * bytes)) 
let parse_partial p ec = 
  if ec then
    begin
    match parse_ec_partial p with
    | Correct(eck,rem) -> Correct (CommonDH.ECKey eck, rem)
    | Error z -> Error z
    end
  else
    begin
    match parse_dh_partial p with
    | Correct(dhk,rem) -> Correct (CommonDH.FFKey dhk, rem)
    | Error z -> Error z
    end

        
  
// Serialize for keyShare extension
val serialize_raw: CommonDH.key -> Tot bytes
let serialize_raw = function
  | CommonDH.ECKey k -> serialize_ec_point k.ec_params k.ec_point
  | CommonDH.FFKey k -> serialize_dh_public k.dh_public (length k.dh_params.dh_p)

val parse: CommonDH.params -> bytes -> Tot (option CommonDH.key)
let parse p x =
  match p with
  | CommonDH.ECP p -> 
    begin
    match parse_ec_point p x with 
    | Some eck -> Some (CommonDH.ECKey ({ec_params=p; ec_point=eck; ec_priv=None;})) 
    | None -> None
    end
  | CommonDH.FFP p ->
    if length x = length p.dh_p then
      Some (CommonDH.FFKey ({dh_params = p; dh_public = x; dh_private = None;}))
    else None

(* From Cert *)
(* ------------------------------------------------------------------------ *)

abstract val certificateListBytes: chain -> Tot bytes
let rec certificateListBytes l =
  match l with
  | [] -> empty_bytes
  | c::r -> 
    lemma_repr_bytes_values (length c);
    (vlbytes 3 c) @| (certificateListBytes r)

val certificateListBytes_is_injective: c1:chain -> c2:chain ->
  Lemma (Seq.equal (certificateListBytes c1) (certificateListBytes c2) ==> c1 == c2)
let rec certificateListBytes_is_injective c1 c2 =
  match c1, c2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if certificateListBytes c1 = certificateListBytes c2 then
      begin
      lemma_repr_bytes_values (length hd); lemma_repr_bytes_values (length hd');
      cut(Seq.equal ((vlbytes 3 hd) @| (certificateListBytes tl)) ((vlbytes 3 hd') @| (certificateListBytes tl')));
      lemma_repr_bytes_values (length hd);
      lemma_repr_bytes_values (length hd');
      cut(Seq.equal (Seq.slice (vlbytes 3 hd) 0 3) (Seq.slice (certificateListBytes c1) 0 3));
      cut(Seq.equal (Seq.slice (vlbytes 3 hd') 0 3) (Seq.slice (certificateListBytes c1) 0 3));
      vlbytes_length_lemma 3 hd hd';
      lemma_append_inj (vlbytes 3 hd) (certificateListBytes tl) (vlbytes 3 hd') (certificateListBytes tl');
      lemma_vlbytes_inj 3 hd hd';
      certificateListBytes_is_injective tl tl'
      end
  | [], hd::tl ->
    begin
    cut (length (certificateListBytes c1) = 0);
    lemma_repr_bytes_values (length hd);
    cut (Seq.equal (certificateListBytes c2) ((vlbytes 3 hd) @| (certificateListBytes tl)));
    lemma_vlbytes_len 3 hd
    end
  | hd::tl, [] ->
    begin
    cut (length (certificateListBytes c2) = 0);
    lemma_repr_bytes_values (length hd);
    cut (Seq.equal (certificateListBytes c1) ((vlbytes 3 hd) @| (certificateListBytes tl)));
    lemma_vlbytes_len 3 hd
    end

abstract val parseCertificateList: b:bytes -> Tot (result chain) (decreases (length b))
let rec parseCertificateList b =
  if length b >= 3 then
    match vlsplit 3 b with
    | Correct (c,r) ->
      cut (repr_bytes (length c) <= 3);
      let rl = parseCertificateList r in
      begin
      match rl with
      | Correct x -> (lemma_repr_bytes_values (length c); Correct (c::x))
      | e -> e
      end
    | _ -> Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")
  else if length b = 0 then Correct []
  else Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")

val lemma_parseCertificateList_length: b:bytes -> 
  Lemma (ensures (match parseCertificateList b with
		  | Correct ces -> length (certificateListBytes ces) = length b
		  | _ -> True))
	(decreases (length b))
let rec lemma_parseCertificateList_length b = 
  match parseCertificateList b with
  | Correct [] -> ()
  | Correct (hd::tl) ->
    begin
    cut(length b >= 3);
    match vlsplit 3 b with
    | Correct (c, r) -> lemma_parseCertificateList_length r
    | _ -> ()
    end
  | Error _ -> ()

