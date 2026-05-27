# Verified TLS 1.3 Client - agentic-tls

Formally verified TLS 1.3 client implementation in Pulse/F*, extracted to C.

## Project Status

✅ **Verification Complete**: All 40+ F*/Pulse modules verify  
✅ **Extraction Complete**: Clean extraction to C (~160 KB across 11 files)  
✅ **Compilation Complete**: All extracted C code compiles without errors  
✅ **End-to-End Test**: Working TLS 1.3 client demonstration

## Quick Start

```sh
# Initial setup
git submodule update --init --depth 1 third_party/hacl-star
./setup.sh

# Verify all F* modules
make verify

# Extract to C
make extract-bundle

# Build and run end-to-end test
make test/tls_client
./test/tls_client example.com 443 ca.pem
```

## Public API

The extracted C code provides a clean 5-function API (see `_extract/bundle/TLS13.h`):

```c
connection client_new(uint8_t *hostname, size_t len, config *cfg);
void client_free(connection c);
bool client_connect(connection c, TLS13_IO_channel ch);
size_t client_write(connection c, TLS13_IO_channel ch, uint8_t *buf, size_t len);
size_t client_read(connection c, TLS13_IO_channel ch, uint8_t *out, size_t max_len);
```

Complete example in `test/tls_client.c`.

## Architecture

The implementation uses a **layered ghost log specification**:

1. **Raw Byte Log** - Monotonic ghost sequence of bytes sent/received on network
2. **Message Log** - Parse of raw bytes into TLS messages (send = serialize, receive = parse)
3. **State Machine** - TLS 1.3 handshake protocol related to message log
4. **Application Log** - Projection of TLS messages to application-level data

All layers are ghost state tied together through the connection invariant, with only the application log exposed in the top-level API specification.

## Repository Structure

- **src/spec/** - Pure F* specifications (TLS 1.3 protocol, crypto)
- **src/impl/** - Pulse implementations (handshake, record layer, connection)
- **_extract/bundle/** - Generated C code (~160 KB, 11 files)
- **c_stubs/** - Unverified backend (I/O, certificate validation, crypto FFI)
- **test/** - End-to-end TLS 1.3 client test
- **third_party/hacl-star/** - HACL* verified crypto library (C snapshot)

## Reference material and dependencies

- RFC reference text is cached locally with `scripts/fetch-rfcs.sh` into `third_party/rfc/`, which is gitignored.
- HACL* is pinned as a Git submodule under `third_party/hacl-star`, but only its checked-in C snapshot under `dist/gcc-compatible` is in scope for this project.
- OpenSSL is a system dependency. Use `scripts/check-openssl.sh` to confirm the `openssl` executable, headers, and libraries are available.

Initial setup:

```sh
git submodule update --init --depth 1 third_party/hacl-star
scripts/fetch-rfcs.sh
scripts/check-openssl.sh
```

Do not try to reverify HACL* or depend on HACL* F* specs as part of this project. The TLS development uses local pure F* specs for the needed crypto behavior and trusted Pulse `.fsti` contracts around calls into the HACL* C snapshot.

During bootstrapping, the checked-in Makefile can be run with the system toolchain:

```sh
make verify FSTAR_EXE=/home/nswamy/.local/bin/fstar.exe KRML_EXE=/home/nswamy/.local/bin/krml
```

After `./setup.sh`, plain `make verify` uses the repository-local toolchain in `tools/FStar`.

Run all current checks with:

```sh
make test
```

The `make test` target also runs `test-extract-smoke`, mock binding tests for
the extracted handshake and connection drivers, extracted wrapper tests for
handshake and connection, and extracted key-schedule and record-layer binding
tests against the HACL* C snapshot. These checks verify small
extraction-safe F* modules, translate verified Pulse/F* code through KaRaMeL,
compile the generated C, and exercise the generated code through explicit
trusted C ABIs.

Run the controlled OpenSSL interop smoke with:

```sh
make test-openssl-echo
```

That target starts the local TLS 1.3/X25519/`TLS_CHACHA20_POLY1305_SHA256`
echo server, runs a scoped HACL*/wire/OpenSSL C backend that sends this
repository's serialized ClientHello, validates OpenSSL's DER leaf certificate
against the generated test CA, verifies CertificateVerify and server Finished
against the transcript, sends client Finished, and checks exact echoed
application data across multiple client records. Its primary client path is the
extracted connection wrapper route, which also routes key-schedule derivation,
Finished verify-data, record seal/open, and record framing through extracted
verified code before reaching the remaining trusted byte backend. The wrapper
path rejects the same server under the wrong test CA, and the target retains the
`openssl s_client` short and
multi-record payload smoke as a server-side compatibility check. Replacing the
remaining trusted byte parser, X.509, crypto, and I/O backend pieces is still a
later milestone.
