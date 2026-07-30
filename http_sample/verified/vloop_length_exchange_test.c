/*
 * vloop_length_exchange_test.c -- end-to-end test of the *verified* HTTP/1.1
 * Content-Length request/response ROUND TRIP, verified client <-> verified
 * server, bidirectional over a single SOCK_STREAM socketpair.
 *
 * The verified client http_client_exchange_length emits a
 * "GET <target> HTTP/1.1\r\n\r\n" request head (http_emit_request), sends it,
 * then receives+parses the response head (http_recv_response) to learn the
 * Content-Length and reads+decodes the body (http_recv_body).
 *
 * The verified server http_server_exchange_length reads+parses the request head
 * (http_recv_request) to recover the request target, then emits the response
 * head (http_emit_response) + body and closes.
 *
 * This drives EVERY Content-Length codec leaf (emit_request/recv_request,
 * emit_response/recv_response, emit_body/recv_body) in one bidirectional
 * exchange.  On success the server recovers the exact target and the client
 * recovers the exact status + body.  The body must be body_ok; the Makefile
 * drives it with body_ok payloads.
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

#define HTTP_MAX (100u * 1000u * 1000u - 1u)   /* Content-Length < 10^8   */
#define STATUS   200u                          /* response status code    */
#define HEAD_LEN 43u                           /* response head is 43 bytes */

static const char TARGET[] = "/index.html";    /* space-free request target */

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: vloop_length_exchange_test <file>\n");
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

  size_t target_len = strlen(TARGET);          /* 11 */
  size_t reqlen     = 4 + target_len + 13;      /* "GET " + target + " HTTP/1.1\r\n\r\n" */

  signal(SIGPIPE, SIG_IGN);

  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) { perror("socketpair"); free(infile); return 1; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); free(infile); return 1; }

  if (pid == 0) {
    /* -- child: the VERIFIED server ------------------------------------- */
    close(sv[1]);
    Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[0]);
    uint8_t *reqbuf  = malloc(reqlen);            /* stages the request head  */
    uint8_t *headbuf = malloc(HEAD_LEN);          /* stages the response head */
    uint8_t *scratch = malloc(flen ? flen : 1);   /* stages the response body */
    size_t   tlen    = 0;
    /* reads+parses the request, then sends the response head+body -- verified. */
    bool okr = http_server_exchange_length(ch, reqbuf, reqlen, &tlen,
                                           (uint16_t)STATUS, infile, flen, headbuf, scratch);
    /* server recovered the request target correctly? */
    int server_ok = okr
                 && (tlen == target_len)
                 && (memcmp(reqbuf + 4, TARGET, target_len) == 0);
    free(reqbuf); free(headbuf); free(scratch); free(infile);
    _exit(server_ok ? 0 : 3);
  }

  /* -- parent: the VERIFIED client --------------------------------------- */
  close(sv[0]);
  Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[1]);

  uint8_t *target  = malloc(target_len ? target_len : 1);
  memcpy(target, TARGET, target_len);
  uint8_t *reqbuf  = malloc(reqlen);
  uint8_t *headbuf = malloc(HEAD_LEN);
  uint8_t *body    = malloc(flen ? flen : 1);
  uint8_t *outbuf  = malloc(flen ? flen : 1);
  uint16_t rcode   = 0;
  uint32_t rlen    = 0;
  if (!target || !reqbuf || !headbuf || !body || !outbuf) { free(infile); return 1; }

  /* emits the request, then reads+parses the response head+body -- verified. */
  bool vok = http_client_exchange_length(ch, target, target_len, reqbuf,
                                         headbuf, &rcode, &rlen, body, outbuf, flen);

  int status = 0;
  waitpid(pid, &status, 0);
  int server_ok = WIFEXITED(status) && WEXITSTATUS(status) == 0;

  int client_ok = vok
               && (rcode == STATUS)
               && ((size_t)rlen == flen)
               && (flen == 0 || memcmp(outbuf, infile, flen) == 0);
  int ok = client_ok && server_ok;
  printf("verified-length exchange: client GET %s -> server parsed target %s; "
         "server 200 + %zu byte(s) -> client parsed status %u, len %u; round trip %s\n",
         TARGET, server_ok ? "OK" : "FAIL", flen,
         (unsigned)rcode, (unsigned)rlen, ok ? "MATCH" : "DIFFER");

  free(target); free(reqbuf); free(headbuf); free(body); free(outbuf); free(infile);
  return ok ? 0 : 1;
}
