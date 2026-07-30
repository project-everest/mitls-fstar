# http_sample — Roadmap toward a real-world HTTP/1.1 implementation

This sample is a **formally verified vertical slice** of HTTP/1.1: a client and a
server, with the wire codec (request line, response head, Content-Length and
chunked body framing) proved correct in F*/Pulse and exercised end-to-end,
including a real-`curl` interop test.

It is intentionally *narrow but sound*: one happy path proved to a high bar,
rather than a broad-but-unverified implementation. This document tracks what is
still missing to interoperate with arbitrary real-world HTTP/1.1 peers.

## What exists today

- **Methods:** `GET` only.
- **Request send/parse:** origin-form request line (`GET <target> HTTP/1.1`),
  headers-tolerant receive-side parse (Host / `Connection: close` recognised;
  other headers skipped).
- **Response send/parse:** status line + `Content-Length` head; general status
  code (100–999).
- **Body framing:** `Content-Length` (fixed-width, 8 ASCII digits) and
  **chunked** transfer (fixed- and variable-width hex chunk sizes, multi-chunk
  reassembly).
- **Drivers:** verified client and server loops; real-`curl` interop test.

## Gaps

### A. Interop blockers (real peers fail today)

- **Methods:** only `GET`. No `POST`/`PUT`/`DELETE`/`HEAD`/`OPTIONS`, and no
  **request bodies** at all (no `Content-Length` or chunked *upload* on the
  send/receive side).
- **Headers are opaque:** skipped/whitelisted rather than parsed into a general
  `(name, value)` list. No header map, case-insensitive lookup, or arbitrary
  header emit.
- **`Content-Length` width.** The client already *parses* variable-width
  `Content-Length` (`Content-Length: 25`) — the `parse_dec_at` scanner is
  proved to compute the clamped `W.dec_dec_var` of the maximal decimal run
  (functional spec, not just memory-safe). The *server* now also *emits* the
  RFC-canonical variable-width Content-Length via the verified leaf
  `http_emit_response_var` (proved equal to `ser_response_var`) and driver
  `http_server_run_length_var`; the fixed-width `00000025` emitter is retained
  alongside. Threading the parsed-value spec up to `http_get` remains a
  follow-up.
- **No response routing / status selection:** the server always emits a fixed
  `200`. No method/target dispatch, no `Date`/`Server` headers.
- **Narrow body delimitation:** relies on `Connection: close` / exact framing.
  No persistent connections / keep-alive, pipelining, bodyless responses
  (`HEAD`, `204`, `304`), or read-until-close bodies.

### B. Security / robustness (mandatory for real-world use)

- **Request-smuggling defense:** must reject conflicting `Content-Length` +
  `Transfer-Encoding`, duplicate `Content-Length`, and malformed chunk sizes.
- **Limits & timeouts:** header/line size caps, slow-loris / read timeouts,
  connection concurrency (currently a single blocking accept loop).
- **Header injection / obs-fold / whitespace** handling, and proper
  `400`/`431`/`501`/`505` error responses instead of silent accept-or-drop.

### C. Breadth (later)

- Chunk **extensions** and **trailer** headers.
- `Expect: 100-continue` flow (status `100` is referenced but not implemented).
- Content/transfer codings (gzip/deflate).
- Request-target forms: query strings, percent-encoding, absolute-form (proxy),
  authority-form (`CONNECT`), asterisk-form (`OPTIONS`).
- HTTP/1.0 fallback; HTTP/2 / HTTP/3.
- **HTTP-over-TLS** integration (this lives in `agentic-tls`).

## Priority

1. **General header parser/emitter** — a `(name, value)` list model; unblocks
   almost everything else.
2. **Variable-width `Content-Length`** parse + emit.
3. **`POST` + request bodies** (`Content-Length` and chunked upload).
4. **Smuggling / limit defenses + error responses.**
5. **Keep-alive / persistent connections**, then **TLS**.

Items 1–2 are the highest leverage: they turn this from "talks to itself and
`curl` on one path" into "interoperates with arbitrary HTTP/1.1 peers."

## Status

- [~] 2. Variable-width `Content-Length` — **in progress**: verified spec codec
      (`W.dec_dec_var` / `ser_response_var` round-trip) DONE; client `parse_dec_at`
      now has a functional spec tying the parsed value to `W.dec_dec_var` DONE;
      canonical variable-width *emit* + threading the value spec to `http_get`
      remain.
- [x] 1. General header parser/emitter (**parse side complete**): verified
      single field-line model (`HTTP.Wire.Header`: `parse_field` / `ser_field`
      round-trip) + extractable parser leaf `http_parse_header_field`
      (`HTTP.Impl.Codec.Header`, functional tie to `parse_field`); driver layer
      in `HTTP.Impl.Loop.Header` — `http_count_headers`, `http_find_header`
      (name→value slice), `http_header_dec` (find + verified `parse_dec_at`,
      Content-Length via the header model), and `http_parse_headers` (enumerate
      the whole block into `(name_off,name_len,val_off,val_len)` record arrays).
      Exercised by `verified/header_parse_test.c`. *Emit side* (building header
      blocks from records) and porting the Transfer-Encoding/Host receive scan
      onto the iterator remain as follow-ups.
- [x] 3. `POST` + request bodies
      *Method-aware request-line parse:* spec `parse_request_line_m`
      (`HTTP.Wire.Length`) returns `Some (method, target)` for any method; the
      verified leaf `http_parse_request_line` (`HTTP.Impl.Codec.RequestLine`)
      recovers the method + target slices with a full round-trip tie, driven by
      `http_method_eq` (`HTTP.Impl.Loop.Request`) and exercised by
      `verified/request_line_test.c` (POST/GET/DELETE/PUT/OPTIONS/HEAD + rejects).
      *Server side (end-to-end):* a real `curl -d` POST is dispatched by the
      verified method parser, its `Content-Length` is recovered by the verified
      header decoder, and the body is echoed back (see `interop/` `make test-post`).
      *Client POST emitter:* verified byte-exact emitter `http_emit_request_post`
      (`HTTP.Impl.Codec.RequestPost`) proved equal to spec `ser_request_post`
      (`"POST " target " HTTP/1.1\r\nContent-Length: " <var-width digits> "\r\n\r\n"`),
      driven by `http_build_post_head` (`HTTP.Impl.Loop.RequestPost`) and
      exercised byte-exactly by `verified/request_post_test.c` (len 5/0/255/1000000).
- [x] 4. Smuggling / limit defenses + error responses — **DONE**:
      verified request-smuggling guard + verified request-line/method validation
      DONE. `http_request_framing_ok` (`HTTP.Impl.Loop.Header`) rejects a request
      whose header block carries a `Content-Length` alongside a
      `Transfer-Encoding`, or more than one `Content-Length` line (RFC 7230
      §3.3.3 CL.TE / duplicate-CL vectors), built on a verified name-filtered
      header-line counter `http_count_header_named` (case-insensitive).
      `http_request_line_ok` + `http_method_known` (`HTTP.Impl.Loop.Request`)
      validate the request line and classify the method against the eight
      standard tokens (GET/HEAD/POST/PUT/DELETE/CONNECT/OPTIONS/TRACE);
      `http_method_allowed` narrows that to the methods this server implements
      (GET/HEAD/POST). `http_header_limits_ok` (`HTTP.Impl.Loop.Header`) caps the
      header-line count and per-line length (DoS defense). A `Transfer-Encoding:
      chunked` upload is decoded by the VERIFIED variable-width chunk decoder
      `http_decode_chunks_var`, which rejects a malformed chunk-size line; the
      interop server answers verified `400` for a bad chunk and echoes the
      decoded body in a verified `200` for a well-formed one. A per-connection
      read timeout (`SO_RCVTIMEO`, slow-loris defense) drops a client that stalls
      before completing the request head with a verified `408`. The interop
      server answers verified `400` (malformed line, smuggling, or bad chunk),
      `405` (unsupported method), `408` (read timeout), `411` (POST without a
      length), `413` (body over cap), `431` (header fields too large), `501`
      (unrecognized method), all via `http_emit_response`. Exercised by
      `verified/framing_test.c`, `verified/method_test.c`,
      `verified/limits_test.c` (`make framing-test`, `make method-test`, `make
      limits-test`) and interop probes (`make test-smuggle`, `make test-method`,
      `make test-limits`, `make test-errors`, `make test-chunked`, `make
      test-timeout`).
- [x] 5. Keep-alive / persistent connections; TLS — **DONE**:
      persistent connections DONE. `http_connection_close`
      (`HTTP.Impl.Loop.Header`) is a verified detector that finds the first
      `Connection` header (case-insensitive, via `http_find_header`) and reports
      whether its field-value carries the `close` connection-option token
      (case-insensitive substring, via `ci_eq_at`), returning `false` — i.e.
      keep-alive — when no `Connection` header is present (HTTP/1.1 default, RFC
      7230 §6.1). The interop server now serves successive requests over a single
      TCP connection in an inner keep-alive loop, creating ONE transport per
      connection and closing it exactly once — when the client closes it, sends a
      verified `Connection: close`, an error occurs, or a read times out.
      Exercised by `verified/connclose_test.c` (`make connclose-test`) and the
      interop probe `make test-keepalive` (two GETs over one connection →
      `200 200`; a `Connection: close` GET → `200` then closed).
      TLS DONE: the interop server carries the SAME verified HTTP leaves over a
      pluggable transport (`io_t`) that is either a plaintext Common.TCP channel
      or an OpenSSL TLS session — the transport is unverified glue, exactly like
      the Common.TCP channel. Setting `HTTP_TLS_CERT` + `HTTP_TLS_KEY` makes the
      server terminate TLS (TLS 1.2+), so the verified server is reachable
      identically over `http://` and `https://`. Exercised by `make test-tls`
      (self-signed cert; `curl -k` GET → `200` + fixed body and POST → `200` +
      echoed body over HTTPS, with the verified parser status asserted).
- [x] 6. **State-machine refinement** — connect the executable layer to the
      protocol spec. Until item 5 the sample had two verified layers that never
      met: the `HTTP.Wire.*` codecs + `HTTP.Impl.*` Pulse loops that the C server
      actually runs, and `HTTP.Protocol.Length`, a `Common.StateMachine` /
      `Common.FileTransfer` model verified in isolation. Nothing tied the running
      bytes to the model.

      Slice 1 DONE — the pure ghost-log refinement core, in the style of
      `TFTP.Impl.Server.Log` / `YModem.Impl.Server.Log`:

        * `HTTP.Impl.Server.Log` refines the Content-Length **response sender**
          against `http_server_wfsm`. It defines the ghost log a running server
          carries (bytes received, bytes written, claimed abstract state), the
          single-step relation `hs_step_rel` and its RTC closure
          `hs_state_ahead_preorder` (proved to be a legal monotonic-reference
          preorder: closed under `CPI.state_ahead` and `histories_ahead`), the
          reachable-trace invariant `server_trace_ok`, and per-operation advance
          lemmas (start / send / complete / abort).

        * `HTTP.Impl.Client.Log` does the same for the **body receiver** against
          `http_client_wfsm`.

      Two structural theorems make the HTTP endpoints simpler than TFTP/YMODEM:
      the sender is *input-free* (`lemma_server_trace_no_wire_inputs` — every
      `WireEvent` step is `False`) and the receiver is *output-free*
      (`lemma_client_trace_no_wire_outputs`). Each therefore discharges one half
      of `WFSM.valid_byte_trace` outright; the receiver satisfies the other half
      through the datagram disjunct, since a body segment is not a strong-prefix
      parser and `HTTP.Wire.Length` carries no stream-laws instance.

      Capstones (all machine-checked, no `admit`/`assume`):

        * `lemma_server_sent_bytes_are_body` — the bytes the server actually
          wrote to the socket are *exactly* `ft_concat` of the abstract delivered
          blocks; and `lemma_server_completed_sent_is_file` — on `FT_Completed`
          they are exactly the file being served (no truncation, padding or
          duplication).
        * `lemma_client_received_bytes_are_file` / `lemma_client_completed_len` —
          the dual for the receiver: the bytes read off the socket are exactly
          the reassembly, and completion implies at least the declared
          Content-Length was read.
        * `lemma_end_to_end_transfer` — the two independently-verified endpoints
          **compose**: if the sender ran to completion and the receiver consumed
          exactly the bytes the sender produced, the file the receiver
          reconstitutes IS the file the sender was serving.

      **Slice 2 (done)** — the Pulse `Common.ProtocolImplementation`
      `protocol_implementation` instances:

        * `HTTP.Impl.Server.CanonicalProtocol.http_server_protocol_implementation`
        * `HTTP.Impl.Client.CanonicalProtocol.http_client_protocol_implementation`

      Each allocates a monotonic ghost reference over
      `hs_state_ahead_preorder` / `hc_state_ahead_preorder`, folds
      `server_trace_ok` / `client_trace_ok` into `pi_invariant`, and discharges
      all five obligations of the class (`pi_invariant_valid`,
      `pi_take_snapshot`, `pi_recall_snapshot`, `pi_process_network`,
      `pi_process_local`) with no `admit`/`assume`.

      Notable, and stronger than the TFTP/YMODEM analogues:

        * The **sender's** `pi_process_network` is a *total, unconditional*
          `IllegalTransition` no-op. That is not a shortcut: `http_server_step`
          maps every `SM.WireEvent` to `False`, so the response sender provably
          cannot be advanced by any wire input, and the no-progress disjunct of
          `network_error_refines_state_machine` is the only sound answer for any
          bytes whatsoever (`Log.lemma_network_noop`).
        * The **receiver's** `pi_process_network` consumes exactly one
          `Msg_body` datagram, with `consumed_by_parse` supplied by
          `lemma_parse_body_exact`: a `body_ok` buffer parses to `Msg_body` of
          itself with an *empty* residual, so the entire input is consumed. The
          `body_ok` test (a body may not start with `'G'` or `'H'`) is performed
          at run time, which is precisely what keeps a body segment unambiguous
          against a request line or a status line on the wire.
        * Because `hss_pending` / `hcs_received` are ghost, the concrete state
          each handle carries is minimal but sufficient: the server's local frame
          threads a `hslf_more` bit ("segments remain") and the client's handle
          keeps a single *remaining-bytes* counter, each tied to the abstract
          state by the invariant. That is what lets the concrete status flag stay
          in lock-step with `ft_status` across every transition.

      Both modules are verified but deliberately **not** extracted: a
      `protocol_implementation` dictionary is not Low-star, and
      `extract_loops.sh` drives an explicit module list, so the generated C is
      unchanged.

## Demo drivers

Two programs make the verified stack directly demonstrable. Neither contains any
HTTP logic of its own: they do argument parsing, socket setup and printing, and
hand every wire byte to the extracted Pulse code.

* **Server — `interop/http_server.c`.** An origin server whose request parse and
  response emission both run through verified extracted code.

      make -C interop build-progs
      cd /tmp/demo && .../_extract/http_server 18080 index.html

  Then open `http://127.0.0.1:18080/` in a browser. It speaks keep-alive,
  honours `Connection: close`, enforces the verified smuggling / size / method
  guards, echoes `POST` bodies (Content-Length *and* chunked), and serves TLS
  when `HTTP_TLS_CERT` / `HTTP_TLS_KEY` are set. Note for demos: it binds
  **0.0.0.0**, serves **one fixed file for every path**, and sends no
  `Content-Type` (browsers MIME-sniff).

* **Client — `verified/vcurl.c`.** A "mini curl" over the verified GET client.

      make vcurl
      _extract/vcurl http://example.com/     # body to stdout
      _extract/vcurl -i http://127.0.0.1:18080/   # head + body
      _extract/vcurl -H http://example.com/       # head only
      make vcurl-demo VCURL_URL=http://example.com/

  `http_get` emits the request head, reads to EOF, parses the status line and
  recovers the body framing; `http_get_body_chunked_var` reassembles chunked
  bodies with minimal-width hex sizes. https is out of scope on this side — use
  the server's TLS mode to demo that direction.

  `verified/get_live_test.c` (`make get-live-test`) remains the CI-guarded
  pass/fail smoke test of the same path against `example.com`; it prints a
  one-line verdict and SKIPs cleanly without network egress.


## Verified TLS termination (HTTPS with no OpenSSL on the server path)

`http_server` has a third transport backend that terminates TLS with the
repository's **verified** TLS 1.3 server (`src/impl/TLS13.Impl.Server.*`, driven
through `runtime/tls13_server_driver.h`) instead of OpenSSL.  With it, the whole
server path -- record layer *and* HTTP/1.1 codec -- is extracted Pulse code.

    make http-sample-vtls-server     # builds http_sample/_extract/http_server_vtls
    make test-http-sample-vtls       # end-to-end: verified HTTP over verified TLS

    HTTP_TLS_BACKEND=verified \
    HTTP_TLS_CERT=test/certs/leaf.der \
    HTTP_TLS_KEY=test/certs/leaf.key \
      http_sample/_extract/http_server_vtls 18443 index.html

Implementation notes:

* The backend is compiled in only under `-DHTTP_VERIFIED_TLS`, so the ordinary
  `make -C interop build-progs` binary is unchanged and does not depend on the
  TLS13 bundle.  `HTTP_TLS_BACKEND` selects `openssl` (default) or `verified`.
* The `io_t` transport seam in `http_server.c` already isolated reads/writes, so
  only `io_read` / `io_write` / `io_close` and the accept path changed.  The
  verified driver returns one record's plaintext at a time, so `io_read` parks
  the remainder and hands the HTTP readers a byte stream.
* The verified driver owns its own listener (`tls13_server_config_new` binds and
  listens), so the plaintext `socket`/`bind`/`listen` path is skipped.
* `HTTP_TLS_CERT` must be the leaf certificate in **DER** form for this backend
  (the verified X.509 path consumes DER); `HTTP_TLS_KEY` stays a PEM key.
* The HTTP translation units are compiled separately from the TLS13 bundle: they
  are extracted against the *variadic* `Common.TCP` stub declarations, which
  clash with the bundle's strict `Common_TCP.h`.

### Client profile the verified server accepts (measured)

The verified server implements the repository's first profile only.  Probing it
with `openssl s_client` shows the ClientHello must satisfy **all** of:

| Requirement | Browsers / curl |
| --- | --- |
| `cipher_suites` == exactly `TLS_CHACHA20_POLY1305_SHA256` | offer 3+ suites |
| `signature_algorithms` == exactly `rsa_pss_rsae_sha256` | offer ~10 |
| TLS 1.3-only ClientHello (no TLS 1.2 legacy suites) | offer TLS 1.2 |
| middlebox-compatibility mode **off** (empty `legacy_session_id`, no dummy CCS) | always on, not switchable |

`supported_groups` is tolerant -- a default multi-group list works as long as the
X25519 key share is offered.

**Consequence: browsers and curl cannot connect to the verified backend today.**
That is why OpenSSL remains the default backend and why the demo browser story
still uses it.  `interop/vtls_client.c` is a small OpenSSL probe that clears
`SSL_OP_ENABLE_MIDDLEBOX_COMPAT` and pins the profile; it is what
`make test-http-sample-vtls` drives.

Closing the gap for browsers would need, in rough order of effort: middlebox
compatibility mode (echo the client's `legacy_session_id`, tolerate/emit the
dummy `ChangeCipherSpec`), cipher-suite and signature-algorithm *selection* from
an offered list rather than exact match, and tolerating TLS 1.2 legacy suites in
the ClientHello.  AES-GCM suites and HelloRetryRequest would follow.
