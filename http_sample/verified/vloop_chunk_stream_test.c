/*
 * vloop_chunk_stream_test.c -- end-to-end test of the *verified* HTTP/1.1
 * chunked streaming transfer, verified sender <-> verified receiver over a
 * SOCK_STREAM socketpair.
 *
 * The input file is split into <= 65535-byte chunks and encoded into one
 * chunked stream using the verified emitters http_emit_chunk /
 * http_emit_empty_chunk.  The child runs the verified
 * http_server_send_stream (write the whole encoded stream, then close); the
 * parent runs the verified http_client_recv_stream (read the agreed
 * `enclen`-byte stream, then reassemble it with http_decode_chunks).  On
 * success the reassembled body must equal the original file byte-for-byte.
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

#define CHUNK_MAX 65535u

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: vloop_chunk_stream_test <file>\n");
    return 2;
  }

  FILE *in = fopen(argv[1], "rb");
  if (!in) { perror("fopen"); return 1; }
  fseek(in, 0, SEEK_END);
  long flen_l = ftell(in);
  rewind(in);
  if (flen_l < 0) { fclose(in); return 1; }
  size_t flen = (size_t)flen_l;
  uint8_t *infile = malloc(flen ? flen : 1);
  if (!infile) { fclose(in); return 1; }
  if (flen > 0 && fread(infile, 1, flen, in) != flen) { fclose(in); free(infile); return 1; }
  fclose(in);

  /* Number of data chunks (at least one, even for an empty body). */
  size_t nchunks = (flen + CHUNK_MAX - 1) / CHUNK_MAX;
  if (nchunks == 0) nchunks = 1;

  /* Encoded size: each chunk is 8 + payload bytes, plus the 8-byte terminator. */
  size_t enclen = flen + 8 * nchunks + 8;
  uint8_t *stream = malloc(enclen);
  if (!stream) { free(infile); return 1; }

  size_t spos = 0, bpos = 0;
  for (size_t c = 0; c < nchunks; c++) {
    size_t n = flen - bpos;
    if (n > CHUNK_MAX) n = CHUNK_MAX;
    http_emit_chunk(infile + bpos, n, stream + spos);   /* verified emitter */
    spos += 8 + n;
    bpos += n;
  }
  http_emit_empty_chunk(stream + spos);                 /* verified terminator */
  spos += 8;

  signal(SIGPIPE, SIG_IGN);

  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) {
    perror("socketpair"); free(infile); free(stream); return 1;
  }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); free(infile); free(stream); return 1; }

  if (pid == 0) {
    /* -- child: the VERIFIED sender -------------------------------------- */
    close(sv[1]);
    Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[0]);
    /* http_server_send_stream writes the whole encoded stream then closes. */
    http_server_send_stream(ch, stream, enclen);
    free(stream); free(infile);
    _exit(0);
  }

  /* -- parent: the VERIFIED receiver ------------------------------------- */
  close(sv[0]);
  Common_TCP_channel rch = Common_TCP_channel_of_fd(sv[1]);

  uint8_t *inbuf  = malloc(enclen);            /* stages the encoded stream */
  uint8_t *outbuf = malloc(flen ? flen : 1);   /* reassembled body          */
  size_t   off    = 0;
  if (!inbuf || !outbuf) { free(infile); free(stream); return 1; }

  /* http_client_recv_stream reads enclen bytes then reassembles -- verified. */
  bool vok = http_client_recv_stream(rch, inbuf, enclen, outbuf, flen, &off);

  int status = 0;
  waitpid(pid, &status, 0);

  int ok = vok
        && (off == flen)
        && (flen == 0 || memcmp(outbuf, infile, flen) == 0);
  printf("verified chunked stream: sent %zu byte(s) in %zu chunk(s) (%zu encoded); "
         "verified receiver reassembled %zu byte(s); content %s\n",
         flen, nchunks, enclen, off, ok ? "MATCH" : "DIFFER");

  free(inbuf); free(outbuf); free(infile); free(stream);
  return ok ? 0 : 1;
}
