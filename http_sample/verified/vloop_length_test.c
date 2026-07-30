/*
 * vloop_length_test.c — end-to-end test of the *verified* HTTP/1.1
 * Content-Length delimited body loop, verified sender <-> verified receiver.
 *
 * Exercises the extracted, verified F-star/Pulse drivers
 * `http_server_run_length` (HTTP.Impl.Server.Loop.Length) and
 * `http_client_run_length` (HTTP.Impl.Client.Loop.Length) from HTTP_Verified.c.
 * It connects the verified sender to the verified receiver over a SOCK_STREAM
 * socketpair and transfers a file body as a raw Content-Length delimited
 * segment (no on-wire framing around the payload — its length is agreed out of
 * band, exactly as TFTP's DATA payload length is).  The receiver reconstructs
 * the bytes through the verified `http_recv_body` codec leaf, which also checks
 * `body_ok` (first byte is neither 'G' nor 'H') so the segment can never be
 * confused with a request/response line.
 *
 * The input must be `body_ok`; the Makefile drives it with body_ok payloads.
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

#define HTTP_MAX (100u * 1000u * 1000u - 1u)   /* Content-Length < 10^8 */

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: vloop_length_test <file>\n");
    return 2;
  }

  FILE *in = fopen(argv[1], "rb");
  if (!in) { perror("fopen"); return 1; }
  fseek(in, 0, SEEK_END);
  long flen_l = ftell(in);
  rewind(in);
  if (flen_l < 0) { fclose(in); return 1; }
  size_t flen = (size_t)flen_l;
  if (flen > HTTP_MAX) {
    fprintf(stderr, "file too large for a Content-Length body (>%u bytes)\n", HTTP_MAX);
    fclose(in); return 1;
  }
  uint8_t *infile = malloc(flen ? flen : 1);
  if (!infile) { fclose(in); return 1; }
  if (flen > 0 && fread(infile, 1, flen, in) != flen) { fclose(in); free(infile); return 1; }
  fclose(in);

  signal(SIGPIPE, SIG_IGN);

  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) { perror("socketpair"); free(infile); return 1; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); free(infile); return 1; }

  if (pid == 0) {
    /* ── child: the VERIFIED sender ─────────────────────────────────────── */
    close(sv[1]);
    Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[0]);
    uint8_t *scratch = malloc(flen ? flen : 1);     /* stages the body segment */
    /* http_server_run_length frames the body through http_emit_body and sends
       it, then closes the channel — all verified. */
    http_server_run_length(ch, infile, flen, scratch);
    free(scratch); free(infile);
    _exit(0);
  }

  /* ── parent: the VERIFIED receiver ────────────────────────────────────── */
  close(sv[0]);
  Common_TCP_channel rch = Common_TCP_channel_of_fd(sv[1]);

  uint8_t *body   = malloc(flen ? flen : 1);        /* raw payload off the wire */
  uint8_t *outbuf = malloc(flen ? flen : 1);
  if (!body || !outbuf) { free(infile); return 1; }

  /* http_client_run_length reads the agreed flen body bytes and decodes them
     through http_recv_body, returning body_ok — all verified. */
  bool vok = http_client_run_length(rch, body, outbuf, flen);
  Common_TCP_close(rch);

  int status = 0;
  waitpid(pid, &status, 0);

  int ok = vok && (flen == 0 || memcmp(outbuf, infile, flen) == 0);
  printf("verified-length transfer: sent %zu byte(s) as a Content-Length body; verified receiver decoded %zu byte(s); content %s\n",
         flen, ok ? flen : (size_t)0, ok ? "MATCH" : "DIFFER");

  free(body); free(outbuf); free(infile);
  return ok ? 0 : 1;
}
