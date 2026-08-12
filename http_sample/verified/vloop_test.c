/*
 * vloop_test.c — end-to-end test of the *verified* HTTP/1.1 chunked loop,
 * verified sender ↔ verified receiver.
 *
 * Exercises the extracted, verified F-star/Pulse drivers `http_server_run`
 * (HTTP.Impl.Server.Loop) and `http_client_run` (HTTP.Impl.Client.Loop) from
 * HTTP_Verified.c.  It connects the verified sender to the verified receiver
 * over a SOCK_STREAM socketpair, transfers a file body through the verified
 * codec (`http_emit_chunk` + `http_emit_empty_chunk` on the send side,
 * `http_peek_chunk_size` + `http_recv_chunk` on the receive side) as one HTTP
 * chunk plus the RFC last-chunk terminator, and checks that the receiver
 * reconstructed the original bytes.
 *
 * WHY SOCK_STREAM (vs TFTP's SOCK_DGRAM): HTTP chunked framing is
 * self-delimiting — each chunk carries its own `hex4(size)` length prefix — so
 * the byte stream needs no datagram boundaries.  A SOCK_STREAM socketpair is the
 * faithful transport (HTTP runs over TCP).
 *
 * Both peers are verified, extracted code in HTTP_Verified.c.  The single-chunk
 * slice passes the agreed body length `flen` to both peers (mirroring how TFTP's
 * harness shares nblocks/flen); the sender emits exactly one chunk of that
 * length plus the terminator, and the receiver reads that one chunk.
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

  /* ── parent: the VERIFIED receiver ────────────────────────────────────── */
  close(sv[0]);
  Common_TCP_channel rch = Common_TCP_channel_of_fd(sv[1]);

  uint8_t *hdr    = malloc(6);                     /* hex4 + CRLF */
  uint8_t *body   = malloc(flen + 2);              /* payload + trailing CRLF */
  uint8_t *outbuf = malloc(flen ? flen : 1);
  if (!hdr || !body || !outbuf) { free(infile); return 1; }

  /* http_client_run reads the chunk header, peeks its size, checks it equals
     the agreed flen, reads the body, validates framing, and writes the decoded
     payload into outbuf — all verified. */
  bool vok = http_client_run(rch, hdr, body, outbuf, flen);
  Common_TCP_close(rch);

  int status = 0;
  waitpid(pid, &status, 0);

  int ok = vok && (flen == 0 || memcmp(outbuf, infile, flen) == 0);
  printf("verified-loop transfer: sent %zu byte(s) as 1 chunk; verified receiver decoded %zu byte(s); content %s\n",
         flen, ok ? flen : (size_t)0, ok ? "MATCH" : "DIFFER");

  free(hdr); free(body); free(outbuf); free(infile);
  return ok ? 0 : 1;
}
