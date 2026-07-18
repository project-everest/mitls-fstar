/*
 * vloop_test.c — end-to-end test of the *verified* HTTP/1.1 chunked send loop.
 *
 * Exercises the extracted, verified F-star/Pulse driver `http_server_run`
 * (HTTP.Impl.Server.Loop) from HTTP_Verified.c.  It connects the verified
 * sender to a plain-C chunked receiver over a SOCK_STREAM socketpair, transfers
 * a file body through the verified codec (`http_emit_chunk` +
 * `http_emit_empty_chunk`) as one HTTP chunk plus the RFC last-chunk
 * terminator, and checks that the receiver reconstructed the original bytes.
 *
 * WHY SOCK_STREAM (vs TFTP's SOCK_DGRAM): HTTP chunked framing is
 * self-delimiting — each chunk carries its own `hex4(size)` length prefix — so
 * the byte stream needs no datagram boundaries.  A SOCK_STREAM socketpair is the
 * faithful transport (HTTP runs over TCP).
 *
 * The framing + codec on the SENDER side is the verified, extracted code in
 * HTTP_Verified.c.  The RECEIVER is an ordinary C chunk parser (the analog of a
 * browser / curl) — this vertical slice proves the verified sender produces
 * wire bytes that a conforming chunked receiver decodes back to the file.
 */

#include "HTTP_Verified.h"
#include "common_tcp_karamel.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <signal.h>
#include <unistd.h>

#define HTTP_BLOCK 65535   /* max payload of a single chunk (block-size cap) */

/* Read exactly n bytes from fd (loops over short reads); returns 0 on success. */
static int read_exact(int fd, uint8_t *buf, size_t n) {
  size_t got = 0;
  while (got < n) {
    ssize_t r = read(fd, buf + got, n - got);
    if (r <= 0) return -1;
    got += (size_t)r;
  }
  return 0;
}

/* Decode one uppercase/lowercase hex digit, or -1. */
static int unhex(uint8_t c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: vloop_test <file>\n");
    return 2;
  }

  /* Read the whole input file (must fit one chunk: <= 65535 bytes). */
  FILE *in = fopen(argv[1], "rb");
  if (!in) { perror("fopen"); return 1; }
  fseek(in, 0, SEEK_END);
  long flen_l = ftell(in);
  rewind(in);
  if (flen_l < 0) { fclose(in); return 1; }
  size_t flen = (size_t)flen_l;
  if (flen > HTTP_BLOCK) {
    fprintf(stderr, "file too large for the single-chunk slice (>%d bytes)\n", HTTP_BLOCK);
    fclose(in); return 1;
  }
  uint8_t *infile = malloc(flen ? flen : 1);
  if (!infile) { fclose(in); return 1; }
  if (flen > 0 && fread(infile, 1, flen, in) != flen) { fclose(in); free(infile); return 1; }
  fclose(in);

  signal(SIGPIPE, SIG_IGN);

  /* SOCK_STREAM: HTTP runs over TCP; chunks are self-delimiting on the stream. */
  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) { perror("socketpair"); free(infile); return 1; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); free(infile); return 1; }

  if (pid == 0) {
    /* ── child: the VERIFIED sender ─────────────────────────────────────── */
    close(sv[1]);
    Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[0]);
    uint8_t *scratch = malloc(8 + flen);            /* one data chunk: 8 + payload */
    uint8_t *term    = malloc(8);                   /* the empty last-chunk */
    /* http_server_run frames the file as one chunk + terminator, sends both,
       and closes the channel — all verified. */
    http_server_run(ch, infile, flen, scratch, term);
    free(scratch); free(term); free(infile);
    _exit(0);
  }

  /* ── parent: an ordinary C chunked receiver ───────────────────────────── */
  close(sv[0]);
  int rfd = sv[1];

  uint8_t *outbuf = malloc(flen ? flen : 1);
  size_t   nbytes = 0;
  int      ok     = 1;

  for (;;) {
    uint8_t hdr[6];                                 /* hex4 + CRLF */
    if (read_exact(rfd, hdr, 6) != 0) { ok = 0; break; }
    int h0 = unhex(hdr[0]), h1 = unhex(hdr[1]), h2 = unhex(hdr[2]), h3 = unhex(hdr[3]);
    if (h0 < 0 || h1 < 0 || h2 < 0 || h3 < 0 || hdr[4] != '\r' || hdr[5] != '\n') { ok = 0; break; }
    size_t sz = (size_t)((h0 << 12) | (h1 << 8) | (h2 << 4) | h3);
    if (sz == 0) {
      /* last chunk: consume the trailing CRLF and stop */
      uint8_t crlf[2];
      if (read_exact(rfd, crlf, 2) != 0 || crlf[0] != '\r' || crlf[1] != '\n') ok = 0;
      break;
    }
    if (nbytes + sz > flen) { ok = 0; break; }      /* more than the file: malformed */
    if (read_exact(rfd, outbuf + nbytes, sz) != 0) { ok = 0; break; }
    nbytes += sz;
    uint8_t crlf[2];                                /* chunk-data trailing CRLF */
    if (read_exact(rfd, crlf, 2) != 0 || crlf[0] != '\r' || crlf[1] != '\n') { ok = 0; break; }
  }

  int status = 0;
  waitpid(pid, &status, 0);

  ok = ok && (nbytes == flen) && (flen == 0 || memcmp(outbuf, infile, flen) == 0);
  printf("verified-loop transfer: sent %zu byte(s) as 1 chunk; receiver decoded %zu byte(s); content %s\n",
         flen, nbytes, ok ? "MATCH" : "DIFFER");

  free(outbuf); free(infile);
  return ok ? 0 : 1;
}
