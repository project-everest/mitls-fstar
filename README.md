# agentic-tls

Experimental TLS 1.3 client implementation in F*/Pulse, extracted to C. The
current codebase has a working scoped client path and an in-progress
functional-correctness proof being redesigned around a buffer-oriented verified
core.

## Read next

- `TLS_OUTLINE.md` - concise task statement and proof requirements.
- `TLS_DESIGN_AND_IMPL.md` - canonical TLS design, proof plan, TCB, extraction notes, and validation workflow.
- `calc_sample/CALC_DESIGN_AND_IMPL.md` - canonical calc-sample methodology reference.

## Scope

The TLS proof target is the supported client profile: TLS 1.3, X25519,
`TLS_CHACHA20_POLY1305_SHA256`, basic 1-RTT handshakes, and application data.
PSK, 0-RTT, resumption, client authentication, and key update are out of scope
for the current plan.

## Setup

```sh
git submodule update --init --depth 1 third_party/hacl-star
./setup.sh
scripts/fetch-rfcs.sh
scripts/check-openssl.sh
```

`./setup.sh` installs the repository-local F*/KaRaMeL toolchain under
`tools/FStar`. You can also override `FSTAR_EXE` and `KRML_EXE` when invoking
`make`.

## Validation

```sh
make verify          # verify all F*/Pulse modules
make extract-bundle  # extract current C artifacts
make test            # local C binding and extraction smoke tests
make test-openssl-echo
```

`make test-openssl-echo` runs the controlled local OpenSSL TLS 1.3 echo interop
scenario. The main test sources live in `test/`, with component and binding
tests in `test/unit/`.

For the methodology reference:

```sh
cd calc_sample
make verify
make check-admits
make test-c
```
