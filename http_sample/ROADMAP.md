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
  `Content-Length` (`Content-Length: 25`) — the `parse_dec_at` scanner is now
  proved to compute the clamped `W.dec_dec_var` of the maximal decimal run
  (functional spec, not just memory-safe). The *server* still emits fixed-width
  (`00000025`), which real peers accept; a canonical variable-width emitter and
  threading the parsed-value spec up to `http_get` remain follow-ups.
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
- [ ] 1. General header parser/emitter
- [ ] 3. `POST` + request bodies
- [ ] 4. Smuggling / limit defenses + error responses
- [ ] 5. Keep-alive / persistent connections; TLS
