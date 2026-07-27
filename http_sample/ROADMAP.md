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
- [~] 4. Smuggling / limit defenses + error responses — **in progress**:
      verified request-smuggling guard + verified request-line/method validation
      DONE. `http_request_framing_ok` (`HTTP.Impl.Loop.Header`) rejects a request
      whose header block carries a `Content-Length` alongside a
      `Transfer-Encoding`, or more than one `Content-Length` line (RFC 7230
      §3.3.3 CL.TE / duplicate-CL vectors), built on a verified name-filtered
      header-line counter `http_count_header_named` (case-insensitive).
      `http_request_line_ok` + `http_method_known` (`HTTP.Impl.Loop.Request`)
      validate the request line and classify the method against the eight
      standard tokens (GET/HEAD/POST/PUT/DELETE/CONNECT/OPTIONS/TRACE). The
      interop server answers verified `400` (malformed line or smuggling), `501`
      (unsupported method), all via `http_emit_response`. Exercised by
      `verified/framing_test.c` + `verified/method_test.c` (`make framing-test`,
      `make method-test`) and interop probes (`make test-smuggle`, `make
      test-method`; the latter uses `curl -X FROBNICATE` → 501 and a raw
      malformed line → 400, GET → 200 control). *Remaining:* limits/timeouts
      (line/header size caps, read timeouts), malformed-chunk-size rejection, and
      the other error responses (`405`/`411`/`413`/`431`/`505`).
- [ ] 5. Keep-alive / persistent connections; TLS
