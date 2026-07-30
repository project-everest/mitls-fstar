# Verified miTLS Chromium demo

This Linux x86_64 bundle contains a custom Chromium browser with the verified
miTLS TLS 1.3 client linked into its Network Service and a small OpenSSL HTTPS
server for the controlled demonstration.

Run the automated headless demonstration:

```sh
./run-demo.sh --headless
```

Launch a visible browser:

```sh
./run-demo.sh
```

The scripts start the bundled server on an automatically selected localhost
port and launch this bundle's Chromium binary with `--use-verified-mitls`.
Success requires the page to contain `verified chromium demo` and Chromium's
diagnostics to report that the verified miTLS provider was selected.

This is a narrow demonstration profile: TLS 1.3, X25519,
TLS_CHACHA20_POLY1305_SHA256, RSA-PSS-RSAE-SHA256, and HTTP/1.1 without ALPN.
Unsupported TLS features fail closed rather than falling back to Chromium's
default provider.

The bundle relies on compatible Linux system libraries. Run `./check-deps.sh`
to diagnose missing dependencies; the build host's dependency list is recorded
in `SYSTEM_LIBRARIES.txt`. A visible run also requires a graphical Linux
desktop. The demo uses `--no-sandbox` because an archive cannot install
Chromium's setuid sandbox with the required root ownership. Run it only against
the bundled localhost server in a controlled environment.

`server/leaf.key` is a public, test-only private key. Never reuse it outside
this demonstration.

Verify the archive contents after extraction with:

```sh
sha256sum --check SHA256SUMS
```

Exact source revisions are recorded in `BUILD_INFO`.
