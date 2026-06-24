# agentic-tls

Experimental TLS 1.3 client implementation in F*/Pulse, extracted to C. 


## Read next

- `calc_sample/CALC_DESIGN_AND_IMPL.md` - canonical calc-sample methodology reference.
- `TLS_OUTLINE.md` - concise task statement and proof requirements.
- `TLS_DESIGN_AND_IMPL.md` - canonical TLS design, proof plan, TCB, extraction notes, and validation workflow.

A proof of a TLS server is in progress and its design is currently in

- `TLS_SERVER_DESIGN_AND_IMPL.md` - TLS design extended to server with a key derivation agreement theorem

## Scope

The TLS proof target is the supported client profile: TLS 1.3, X25519,
`TLS_CHACHA20_POLY1305_SHA256`, basic 1-RTT handshakes, and application data.
PSK, 0-RTT, resumption, client authentication, and key update are out of scope
for the current plan.

## Setup

### Dev container (recommended)

A `.devcontainer/` is provided. Opening the repository in a dev container (VS Code
"Reopen in Container", or `devcontainer up`) builds a minimal image and runs
`./setup.sh` automatically, producing a ready-to-build environment. To exercise
the whole pipeline (QuackyDucky generation → F* verification → KaRaMeL extraction
→ OpenSSL interop) from a clean checkout:

```sh
.devcontainer/test-full-path.sh
```

### Manual setup

```sh
./setup.sh
```

`./setup.sh` builds the EverParse toolchain (QuackyDucky + LowParse + the
F*/KaRaMeL binaries it vendors) from the pinned fork/commit into
`tools/everparse` (gitignored), then initializes the HACL* submodule and fetches
the RFC and OpenSSL dependencies. No separate F* installation is required; the
`make` toolchain is derived from `EVERPARSE_HOME` (default `tools/everparse`).

Environment overrides: `EVERPARSE_HOME`, `EVERPARSE_REPO`, `EVERPARSE_BRANCH`,
`EVERPARSE_COMMIT`, `JOBS`, or point `FSTAR_EXE`/`KRML_EXE`/`QD_EXE` at a
different toolchain when invoking `make`.

## Validation

```sh
make parsers         # QuackyDucky: regenerate, verify, and extract the TLS wire
                     #   parsers/serializers from tls.qd.rfc (generated/)
make verify          # verify all F*/Pulse modules
make extract-tls13-bundle  # extract the unified client/server driver bundle
make test            # verify, check echo stubs, and run OpenSSL echo interop
```

The QuackyDucky pipeline can also be driven stage by stage with
`make regen-generated`, `make verify-generated`, and `make extract-generated`.

`make test-openssl-echo` runs the controlled local OpenSSL TLS 1.3 echo interop
scenario. The main test sources live in `test/` and `test/unit/`.

For the methodology reference:

```sh
cd calc_sample
make verify
make check-admits
make test-c
```
