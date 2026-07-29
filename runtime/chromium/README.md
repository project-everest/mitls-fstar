# Chromium client integration

This directory contains the browser-facing asynchronous adapter for the verified
TLS 1.3 client engine.

```text
Chromium net::SSLClientSocket
  -> Chromium StreamSocket / CertVerifier bridge
  -> mitls::chromium::Tls13ClientSocket
  -> runtime/tls13_client_engine.h
  -> extracted TLS13.Impl.Client.Engine
```

`Tls13ClientSocket` is intentionally independent of Chromium headers. Its
`StreamSocket` and `ServerAuthenticator` interfaces isolate the two browser APIs
that are trusted by the verified engine: transport I/O and server
authentication. This keeps the state machine buildable and testable in this
repository while leaving only a mechanical `net::` wrapper in Chromium.

## Demo

Run:

```sh
make -j$(nproc) test-chromium-client-demo
```

The test performs a real TLS 1.3 HTTP/1.1 request against a local OpenSSL server.
It covers:

- Chromium's synchronous-or-`ERR_IO_PENDING` completion convention;
- one pending application read and one pending write concurrently;
- partial seven-byte TCP reads and writes;
- retained and resubmitted ciphertext suffixes;
- asynchronous certificate-chain verification;
- CertificateVerify verification with the authenticated leaf key;
- queued plaintext delivery and peer `close_notify`.

The demo uses the supported verified profile: TLS 1.3, X25519,
`TLS_CHACHA20_POLY1305_SHA256`, RSA-PSS-RSAE-SHA256 server authentication, and
HTTP/1.1. It does not claim browser TLS feature parity.

## Chromium `net::` wrapper

As of Chromium main in July 2026, `SSLConnectJob::DoSSLConnect()` constructs the
TLS socket through the virtual
`ClientSocketFactory::CreateSSLClientSocket()` method. A demo integration does
not need to modify `SSLClientContext::CreateSSLClientSocket()`.

Add a `VerifiedTlsClientSocket : public net::SSLClientSocket` and a delegating
`ClientSocketFactory`:

1. `VerifiedTlsClientSocket` owns `Tls13ClientSocket`.
2. Its transport bridge forwards `Read`, `Write`, `Disconnect`, addresses,
   socket tags, byte counts, and `NetLog()` to the already-connected
   `net::StreamSocket`. It retains `IOBuffer` references until callbacks run.
3. Its authentication bridge converts the copied DER entries with
   `X509Certificate::CreateFromDERCertChain()`, then calls
   `SSLClientContext::cert_verifier()->Verify()`. It retains the
   `CertVerifier::Request`, `CertVerifyResult`, and verified certificate.
4. After successful chain verification, the bridge extracts the leaf
   SubjectPublicKeyInfo DER and returns it from
   `authenticated_public_key_der()`. CertificateVerify is checked with
   BoringSSL using the engine-provided scheme, input, and signature.
5. `Connect`, `Read`, `Write`, and `Disconnect` delegate to the portable
   adapter, translating `kIoPending` to `net::ERR_IO_PENDING` and other results
   to `net::Error`.
6. `GetSSLInfo()` returns the verified and unverified certificate chains,
   `cert_status`, public-key hashes, TLS 1.3, ciphersuite `0x1303`, X25519 group
   `29`, the captured peer signature scheme, and `HANDSHAKE_FULL`.
7. `GetNegotiatedProtocol()` returns `kProtoUnknown` for the current profile:
   no ALPN extension is sent, so Chromium falls back to HTTP/1.1. HTTP/2 must
   remain disabled until verified ALPN support is added.
8. `GetECHRetryConfigs()` and `GetServerTrustAnchorIDs()` return empty vectors;
   `ExportKeyingMaterial()` returns `ERR_NOT_IMPLEMENTED`; early data, ECH,
   client authentication, session resumption, and ALPS remain disabled.
9. Override `ClientSocketFactory::CreateSSLClientSocket()` to return the
   verified socket for the demo profile and delegate all other factory methods
   to `ClientSocketFactory::GetDefaultFactory()`.
10. Install that factory in
    `HttpNetworkSessionContext::client_socket_factory`.

The relevant Chromium source surfaces are:

- `net/socket/ssl_connect_job.cc`
- `net/socket/client_socket_factory.h`
- `net/socket/ssl_client_socket.h`
- `net/socket/stream_socket.h`
- `net/socket/socket.h`
- `net/cert/cert_verifier.h`
- `net/cert/cert_verify_result.h`
- `net/ssl/ssl_info.h`
- `net/http/http_network_session.h`

## Audit boundary

The portable adapter does not implement TLS protocol transitions. It schedules
verified engine calls, retains caller-owned I/O buffers, handles partial
transport operations, and translates completion results.

The Chromium authentication bridge is an explicit TCB:

- successful chain completion attests that Chromium verified the exact copied
  DER chain for the configured hostname and browser trust policy;
- successful CertificateVerify completion attests that BoringSSL verified the
  exact copied input and signature with that authenticated leaf key;
- rejection destroys the engine and closes the transport without advancing the
  verified TLS state.

The portable adapter's public certificate chain and peer signature scheme are
the inputs needed to populate Chromium's `SSLInfo`.
