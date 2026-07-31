# Verified ATLAS Chromium demo

This Linux x86_64 bundle contains a custom Chromium browser with the verified
ATLAS TLS 1.3 client linked into its Network Service and a small OpenSSL HTTPS
server for the controlled demonstration.

Run the automated headless demonstration:

```sh
./run-demo.sh --headless
```

Launch a visible browser:

```sh
./run-demo.sh
```

Browse a public HTTPS origin with normal DNS and certificate enforcement:

```sh
./launch-chrome.sh --public https://www.google.com/
./launch-chrome.sh --public https://www.microsoft.com/
```

The scripts start the bundled server on an automatically selected localhost
port and launch this bundle's Chromium binary with `--use-atlas`.
Success requires the page to contain `verified chromium demo` and Chromium's
diagnostics to report that the ATLAS provider was selected.
The controlled localhost mode forces software rendering and prevents DNS
resolution for non-localhost names, avoiding destination-specific GPU drivers
and unrelated browser background connections.
The HTTPS server tolerates Chromium's speculative TLS preconnections and keeps
listening until the navigation sends the real HTTP request.
Public mode removes the localhost DNS block and does not ignore certificate
errors. Unsupported TLS profiles fail closed; some third-party subresources may
therefore fail even when the requested top-level page renders.

This is a narrow demonstration profile: TLS 1.3, X25519,
TLS_CHACHA20_POLY1305_SHA256, RSA-PSS-RSAE-SHA256, and HTTP/1.1 without ALPN.
Unsupported TLS features fail closed rather than falling back to Chromium's
default provider.

The bundle relies on compatible Linux system libraries. Run `./check-deps.sh`
to diagnose missing dependencies; the build host's dependency list is recorded
in `SYSTEM_LIBRARIES.txt`. A visible run also requires a graphical Linux
desktop. The demo uses `--no-sandbox` because an archive cannot install
Chromium's setuid sandbox with the required root ownership. Run it only against
trusted sites in a controlled environment.

If a run fails, `run-demo.sh` retains its temporary directory and prints its
location. That directory contains `chromium.log`, `server.log`, and
`netlog.json` for diagnosis. Set `ATLAS_DEMO_KEEP_ARTIFACTS=1` to retain these
files after a successful run as well.

A logging-enabled bundle can capture verified handshake and record-layer
metadata:

```sh
./run-demo.sh --headless --trace atlas-trace.jsonl
./launch-chrome.sh --public --trace atlas-trace.jsonl https://www.google.com/
./analyze-atlas-trace.py atlas-trace.jsonl --timeline
```

Trace records contain event tags, lengths, sequence numbers, status tags, and
connection/process/thread correlation only. They do not contain secrets,
plaintext, certificates, or payload bytes.

`server/leaf.key` is a public, test-only private key. Never reuse it outside
this demonstration.

Verify the archive contents after extraction with:

```sh
sha256sum --check SHA256SUMS
```

Exact source revisions are recorded in `BUILD_INFO`.
