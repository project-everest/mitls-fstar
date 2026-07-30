/*
 * vloop_length_full_test.c -- end-to-end test of the *verified* HTTP/1.1
 * Content-Length delimited HEAD+BODY exchange, verified sender <-> verified
 * receiver.
 *
 * Unlike vloop_length_test.c (which transfers only the raw body, the length
 * agreed out of band), this exercises a full response exchange: the verified
 * sender http_server_run_length_full first emits the 43-byte response head
 * (status code + Content-Length) through the verified codec leaf
 * http_emit_response, then sends the body; the verified receiver
 * http_client_run_length_full reads the head, parses it through the verified
 * http_recv_response leaf to LEARN the Content-Length, checks it matches the
 * agreed buffer size, then reads and decodes the body through http_recv_body.
 *
 * On success the recovered status code and body bytes are checked against the
 * originals.  The input must be body_ok; the Makefile drives it with body_ok
 * payloads.
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
#define STATUS   200u                          /* response status code   */
#define HEAD_LEN 43u                           /* response head is 43 bytes */

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: vloop_length_full_test <file>\n");
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
    /* -- child: the VERIFIED sender -------------------------------------- */
    close(sv[1]);
    Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[0]);
    uint8_t *headbuf = malloc(HEAD_LEN);           /* stages the response head */
    uint8_t *scratch = malloc(flen ? flen : 1);    /* stages the body segment  */
    /* http_server_run_length_full emits head(STATUS,flen) via http_emit_response,
       sends it, then frames+sends the body and closes -- all verified. */
    http_server_run_length_full(ch, (uint16_t)STATUS, infile, flen, headbuf, scratch);
    free(headbuf); free(scratch); free(infile);
    _exit(0);
  }

  /* -- parent: the VERIFIED receiver ------------------------------------- */
  close(sv[0]);
  Common_TCP_channel rch = Common_TCP_channel_of_fd(sv[1]);

  uint8_t *headbuf = malloc(HEAD_LEN);
  uint8_t *body    = malloc(flen ? flen : 1);       /* raw payload off the wire */
  uint8_t *outbuf  = malloc(flen ? flen : 1);
  uint16_t rcode   = 0;
  uint32_t rlen    = 0;
  if (!headbuf || !body || !outbuf) { free(infile); return 1; }

  /* http_client_run_length_full reads+parses the head to recover (rcode,rlen),
     checks rlen == flen, then reads+decodes the body -- all verified. */
  bool vok = http_client_run_length_full(rch, headbuf, &rcode, &rlen, body, outbuf, flen);
  Common_TCP_close(rch);

  int status = 0;
  waitpid(pid, &status, 0);

  int ok = vok
        && (rcode == STATUS)
        && ((size_t)rlen == flen)
        && (flen == 0 || memcmp(outbuf, infile, flen) == 0);
  printf("verified-length full exchange: sent status %u + %zu byte(s); verified receiver parsed status %u, len %u; content %s\n",
         STATUS, flen, (unsigned)rcode, (unsigned)rlen, ok ? "MATCH" : "DIFFER");

  free(headbuf); free(body); free(outbuf); free(infile);
  return ok ? 0 : 1;
}
