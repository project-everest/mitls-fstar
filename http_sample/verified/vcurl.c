/*
 * vcurl.c — a "mini curl" demo driven end-to-end by the *verified* HTTP/1.1
 * client extracted from Pulse.
 *
 * Usage:
 *     vcurl [-i] [-H] <url>
 *     vcurl [-i] [-H] <host> [port] [path]
 *
 *     -i   also print the response head (like `curl -i`)
 *     -H   print ONLY the head, not the body (like `curl -I`, but still a GET)
 *
 * Examples:
 *     vcurl http://example.com/
 *     vcurl -i example.com 80 /
 *     vcurl http://127.0.0.1:18080/
 *
 * Everything on the HTTP wire is produced and consumed by verified code:
 *
 *   - `http_get` (HTTP.Impl.Client.Loop.Get) emits the request head with the
 *     verified emitter -- "GET <target> HTTP/1.1\r\nHost: <host>\r\n
 *     Connection: close\r\n\r\n" -- reads the response to EOF, parses the
 *     status line with the verified status-line parser, and recovers the body
 *     framing (Content-Length vs. chunked) with the verified header decoder.
 *   - `http_get_body_chunked_var` (HTTP.Impl.Codec.Chunked.Stream) reassembles
 *     a chunked body, parsing the minimal-width hex chunk sizes real servers
 *     emit.
 *
 * This program only does argument parsing, socket setup (via the same
 * Common.TCP stub the verified code is specified against) and printing; it does
 * not touch the HTTP bytes itself.  TLS / https is out of scope -- use the
 * verified server's TLS mode for that side of the demo.
 *
 * Exit status: 0 if the exchange succeeded and any chunked body decoded,
 * 1 on a protocol/decode failure, 2 on usage or connection failure.
 */

#include "HTTP_Verified.h"
#include "common_tcp_karamel.h"
#include "karamel_option_compat.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

/* Common_TCP_connect_tcp is defined in the hand-written c_stubs and linked in,
   but its option-return type and prototype are not published in a header
   (the option struct is emitted inside the .c).  Re-declare them here matching
   the stub's ABI (tag 0 = None, 1 = Some; see karamel_option_compat.h). */
typedef struct FStar_Pervasives_Native_option__Common_TCP_channel_s {
  uint8_t tag;
  Common_TCP_channel v;
} FStar_Pervasives_Native_option__Common_TCP_channel;

FStar_Pervasives_Native_option__Common_TCP_channel Common_TCP_connect_tcp(
    uint8_t *hostname, size_t hostname_len, uint16_t port);

static void usage(const char *prog) {
  fprintf(stderr,
    "usage: %s [-i] [-H] <url>\n"
    "       %s [-i] [-H] <host> [port] [path]\n"
    "\n"
    "  -i   also print the response head\n"
    "  -H   print only the response head\n"
    "\n"
    "examples:\n"
    "  %s http://example.com/\n"
    "  %s -i example.com 80 /\n",
    prog, prog, prog, prog);
}

/* Split "http://host[:port][/path]" (the scheme is optional) into its parts.
   Returns 0 on success.  `host` points into `url`; `host_len` bounds it. */
static int split_url(const char *url,
                     const char **host, size_t *host_len,
                     uint16_t *port, const char **path) {
  const char *p = url;
  if (strncmp(p, "http://", 7) == 0) {
    p += 7;
  } else if (strncmp(p, "https://", 8) == 0) {
    fprintf(stderr, "vcurl: https is out of scope for this demo client\n");
    return -1;
  }
  if (*p == '\0') return -1;

  const char *hstart = p;
  while (*p && *p != ':' && *p != '/') p++;
  *host = hstart;
  *host_len = (size_t)(p - hstart);
  if (*host_len == 0) return -1;

  if (*p == ':') {
    p++;
    long v = strtol(p, (char **)&p, 10);
    if (v <= 0 || v > 65535) return -1;
    *port = (uint16_t)v;
  }
  *path = (*p == '/') ? p : "/";
  return 0;
}

int main(int argc, char **argv) {
  signal(SIGPIPE, SIG_IGN);

  int show_head = 0, head_only = 0;
  int a = 1;
  for (; a < argc && argv[a][0] == '-' && argv[a][1] != '\0'; a++) {
    if      (strcmp(argv[a], "-i") == 0) show_head = 1;
    else if (strcmp(argv[a], "-H") == 0) { head_only = 1; show_head = 1; }
    else if (strcmp(argv[a], "--help") == 0) { usage(argv[0]); return 0; }
    else { usage(argv[0]); return 2; }
  }
  if (a >= argc) { usage(argv[0]); return 2; }

  const char *host_s = NULL;
  size_t      host_len = 0;
  uint16_t    port = 80;
  const char *path_s = "/";

  if (argc - a == 1) {
    if (split_url(argv[a], &host_s, &host_len, &port, &path_s) != 0) {
      usage(argv[0]);
      return 2;
    }
  } else {
    host_s = argv[a];
    host_len = strlen(host_s);
    if (argc - a >= 2) {
      long v = atol(argv[a + 1]);
      if (v <= 0 || v > 65535) { usage(argv[0]); return 2; }
      port = (uint16_t)v;
    }
    if (argc - a >= 3) path_s = argv[a + 2];
  }
  size_t target_len = strlen(path_s);
  if (host_len == 0 || target_len == 0) { usage(argv[0]); return 2; }

  fprintf(stderr, "vcurl: GET http://%.*s:%u%s  (request + parse by VERIFIED code)\n",
          (int)host_len, host_s, port, path_s);

  FStar_Pervasives_Native_option__Common_TCP_channel c =
    Common_TCP_connect_tcp((uint8_t *)host_s, host_len, port);
  if (c.tag != FStar_Pervasives_Native_Some) {
    fprintf(stderr, "vcurl: could not connect to %.*s:%u\n",
            (int)host_len, host_s, port);
    return 2;
  }
  Common_TCP_channel ch = c.v;

  /* Request head size the verified emitter will write:
       "GET " + target + " HTTP/1.1\r\n" + "Host: " + host + "\r\nConnection: close\r\n\r\n" */
  size_t reqlen = 4 + target_len + 17 + host_len + 23;
  uint8_t *reqbuf = malloc(reqlen);

  size_t cap = 1u << 22;               /* 4 MiB response cap */
  uint8_t *buf = malloc(cap);
  size_t tmpcap = 16384;
  uint8_t *tmp = malloc(tmpcap);
  if (!reqbuf || !buf || !tmp) {
    fprintf(stderr, "vcurl: out of memory\n");
    free(reqbuf); free(buf); free(tmp);
    Common_TCP_close(ch);
    return 2;
  }

  size_t   rlen    = 0;
  uint16_t code    = 0;
  bool     chunked = false;
  bool     has_cl  = false;
  uint32_t cl      = 0;
  size_t   headlen = 0;

  bool ok = http_get(ch, (uint8_t *)path_s, target_len,
                     (uint8_t *)host_s, host_len,
                     reqbuf, buf, cap, tmp, tmpcap,
                     &rlen, &code, &chunked, &has_cl, &cl, &headlen);

  Common_TCP_close(ch);

  if (!ok) {
    fprintf(stderr, "vcurl: the verified client rejected the response "
                    "(read %zu byte(s); malformed status line or framing?)\n", rlen);
    free(reqbuf); free(buf); free(tmp);
    return 1;
  }

  if (show_head) {
    fwrite(buf, 1, headlen, stdout);
    fflush(stdout);
  }

  int rc = 0;
  if (!head_only) {
    size_t body_off = headlen, body_len = (headlen <= rlen) ? rlen - headlen : 0;
    if (chunked) {
      /* Reassemble with the verified variable-width chunked decoder. */
      uint8_t *raw = malloc(cap);
      uint8_t *out = malloc(cap);
      size_t decoded = 0;
      if (!raw || !out) {
        fprintf(stderr, "vcurl: out of memory decoding chunked body\n");
        rc = 1;
      } else if (!http_get_body_chunked_var(buf, headlen, rlen, raw, cap, out, cap, &decoded)) {
        fprintf(stderr, "vcurl: the verified chunked decoder rejected the body\n");
        rc = 1;
      } else {
        fwrite(out, 1, decoded, stdout);
        body_len = decoded;
      }
      free(raw); free(out);
    } else {
      /* Content-Length (or read-to-EOF): the body is the tail of the buffer. */
      if (has_cl && (size_t)cl < body_len) body_len = (size_t)cl;
      fwrite(buf + body_off, 1, body_len, stdout);
    }
    fflush(stdout);
    fprintf(stderr, "vcurl: HTTP %u, %s, %zu byte(s) of body\n",
            code,
            chunked ? "chunked (verified decode)"
                    : (has_cl ? "Content-Length" : "read-to-EOF"),
            body_len);
  } else {
    fflush(stdout);
    fprintf(stderr, "vcurl: HTTP %u, head %zu byte(s)\n", code, headlen);
  }

  free(reqbuf); free(buf); free(tmp);
  return rc;
}
