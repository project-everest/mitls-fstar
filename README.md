# agentic-tls

Verified TLS 1.3 client implementation experiment in Pulse/F*, extracted to C.

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
the extracted handshake and connection drivers, and an extracted key-schedule
binding test against the HACL* C snapshot. These checks verify small
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
application data across multiple client records. It runs both the direct C probe
and the extracted verified connection-plus-handshake driver path over that
backend, checks that both reject the same server under the wrong test CA, and
retains the `openssl s_client` short and multi-record payload smoke as a server-side
compatibility check. Replacing the temporary trusted C connection backend with
extracted verified byte-level connection code is still a later milestone.
