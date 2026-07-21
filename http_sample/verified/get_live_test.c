/*
 * get_live_test.c — OPTIONAL live smoke test of the *verified* HTTP/1.1 GET
 * client `http_get` against a real origin server over port 80.
 *
 * It connects to example.com:80 with the real Common_TCP_connect_tcp, then runs
 * the extracted verified `http_get` to emit
 *   "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n",
 * read the whole response to EOF, and parse the response head.  On a successful
 * exchange we print the status code and body framing.
 *
 * GUARDED FOR CI: if the connection cannot be established (no network egress),
 * the test prints SKIP and exits 0, so environments without outbound access
 * still pass.  This is NOT part of the default `make vloop-tests` aggregate;
 * run it explicitly with `make get-live-test`.  TLS / port 443 is out of scope.
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

int main(void) {
  signal(SIGPIPE, SIG_IGN);

  uint8_t host[] = { 'e','x','a','m','p','l','e','.','c','o','m' };
  size_t host_len = 11;

  FStar_Pervasives_Native_option__Common_TCP_channel c =
    Common_TCP_connect_tcp(host, host_len, 80);
  if (c.tag != FStar_Pervasives_Native_Some) {
    printf("live GET: could not connect to example.com:80 (no egress?) => SKIP\n");
    return 0;
  }
  Common_TCP_channel ch = c.v;

  uint8_t target[] = { '/' };
  size_t target_len = 1;

  size_t reqlen = 4 + target_len + 17 + host_len + 23;
  uint8_t *reqbuf = malloc(reqlen);

  size_t cap = 1u << 20;               /* 1 MiB response cap */
  uint8_t *buf = malloc(cap);
  size_t tmpcap = 16384;
  uint8_t *tmp = malloc(tmpcap);
  if (!reqbuf || !buf || !tmp) { free(reqbuf); free(buf); free(tmp); return 1; }

  size_t   rlen    = 0;
  uint16_t code    = 0;
  bool     chunked = false;
  bool     has_cl  = false;
  uint32_t cl      = 0;
  size_t   headlen = 0;

  bool ok = http_get(ch, target, target_len, host, host_len,
                     reqbuf, buf, cap, tmp, tmpcap,
                     &rlen, &code, &chunked, &has_cl, &cl, &headlen);

  Common_TCP_close(ch);

  size_t body_len = (ok && headlen <= rlen) ? (rlen - headlen) : 0;

  /* A live origin server should return a well-formed status line; a 2xx/3xx
     status code proves the verified request/parse round trip worked. */
  int pass = ok && code >= 200 && code < 400;

  printf("live GET http://example.com/ : ok=%d code=%u chunked=%d has_cl=%d cl=%u rlen=%zu headlen=%zu body=%zu byte(s) => %s\n",
         ok, code, chunked, has_cl, cl, rlen, headlen, body_len,
         pass ? "PASS" : "FAIL");

  free(reqbuf); free(buf); free(tmp);
  return pass ? 0 : 1;
}
