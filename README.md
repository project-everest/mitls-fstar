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
