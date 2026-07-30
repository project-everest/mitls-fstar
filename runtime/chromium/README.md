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

## Chromium browser build

The checked integration is pinned to Chromium revision
`5e4202e0d22c4abf7400880edfd8553d063159df`. Given a shallow checkout at
`../chromium/src` and `depot_tools` at `../depot_tools`, run:

```sh
make -j$(nproc) chromium-net
make -j$(nproc) chromium-browser
make -j$(nproc) test-chromium-browser
```

Override `CHROMIUM_SRC`, `DEPOT_TOOLS`, or `CHROMIUM_OUT` when using other
locations. `chromium-install-provider` builds the static verified provider,
copies it and the portable adapter into `third_party/mitls`, and installs the
repository-owned overlay in `runtime/chromium/chromium_src`.

The overlay adds `VerifiedMiTlsClientSocket : net::SSLClientSocket` and selects
it from Chromium's default `ClientSocketFactory` only when
`--use-verified-mitls` is present. Selection is fail-closed: a provider failure
is returned to Chromium and never falls back to `SSLClientSocketImpl`. The
installer also forwards the opt-in switch to Chromium utility processes, where
the out-of-process Network Service creates client sockets.

The wrapper:

1. owns `Tls13ClientSocket` and retains Chromium `IOBuffer` references until
   asynchronous operations complete;
2. forwards transport operations, addresses, socket tags, and `NetLog()` to the
   already-connected `net::StreamSocket`;
3. converts the exact copied DER chain with
   `X509Certificate::CreateFromDERCertChain()` and invokes Chromium's
   `CertVerifier`;
4. extracts the authenticated leaf SubjectPublicKeyInfo and checks the exact
   engine-provided CertificateVerify input and signature with Chromium's
   BoringSSL RSA-PSS verifier;
5. populates `SSLInfo` with both certificate chains, certificate status,
   public-key hashes, TLS 1.3, ciphersuite `0x1303`, X25519 group `29`, the peer
   signature scheme, and `HANDSHAKE_FULL`; and
6. reports no ALPN, ECH retry config, Trust Anchor IDs, early data, resumption,
   client authentication, ALPS, or exporter support.

`test-chromium-browser` launches the actual `chrome` binary in headless mode
against the controlled OpenSSL HTTP/1.1 endpoint. It requires both the returned
page body and the factory's provider-selection diagnostic, so a BoringSSL
fallback cannot satisfy the smoke test. The smoke disables Chromium's
non-official-build field-trial configuration and TLS experiments outside this
provider's profile. It uses Chromium's explicit certificate-error override for
the local test CA; the bridge still invokes `CertVerifier` and verifies the
server's CertificateVerify signature.

## Transferable Linux bundle

Build and test the Linux x86_64 demonstration archive:

```sh
make -j$(nproc) chromium-demo-bundle
make -j$(nproc) test-chromium-demo-bundle
```

The archive is written to
`_extract/mitls-chromium-demo-linux-x86_64.tar.gz`. Transfer it to a compatible
Linux x86_64 machine, then run:

```sh
tar xzf mitls-chromium-demo-linux-x86_64.tar.gz
cd mitls-chromium-demo-linux-x86_64
./run-demo.sh --headless
./run-demo.sh
```

The headless invocation is a self-test that requires both the expected HTTPS
DOM and the verified-provider selection diagnostic. The visible invocation
opens the same page in a browser window. The bundle records source revisions,
SHA-256 checksums, and build-host dynamic dependencies and checks destination
dependencies before launch.

The browser provider is statically linked into `chrome`; no miTLS shared
library is required. The archive still relies on compatible Linux system
libraries, including glibc and the libraries reported by `check-deps.sh`. It
uses `--no-sandbox`, because a transferable archive cannot install Chromium's
setuid sandbox with root ownership. This bundle is therefore only for the
controlled localhost demonstration. The included certificate private key is
public test material and must not be reused.

The relevant Chromium source surfaces are:

- `net/socket/ssl_connect_job.cc`
- `net/socket/client_socket_factory.h`
- `net/socket/ssl_client_socket.h`
- `net/socket/stream_socket.h`
- `net/socket/socket.h`
- `content/browser/service_host/utility_process_host.cc`
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
