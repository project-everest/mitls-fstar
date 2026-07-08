/*
 * ymodem_sb.c — unverified YMODEM sender wrapper (an `sb filename`-style program).
 *
 * This is the interoperability wrapper for the *sender* side.  It speaks the
 * YMODEM protocol over stdin/stdout (as lrzsz's `sb` does over a serial line),
 * and delegates the per-packet work — building the 133-byte header and data
 * packets (block number, complement, 128-byte payload, CRC-16) — to the
 * extracted (currently skeleton) functions `ymodem_server_emit_header` and
 * `ymodem_server_emit_block` from YModem.Impl.Server.
 *
 * `ymodem_server_emit_header` / `ymodem_server_emit_block` are the executable
 * *leaf* operations of the sender state-machine implementation: they are the
 * packet-framing steps invoked by `pi_process_local` of the YMODEM server
 * `protocol_implementation` instance
 * `YModem.Impl.Server.CanonicalProtocol.ymodem_server_protocol_implementation`
 * (the header block for the `YmodemStart` event, the data blocks for
 * `YmodemSendBlock`).  That instance (the verified refinement witness) is not
 * itself Low* — like every type-class dictionary it holds separation-logic and
 * ghost fields — so it is verified but not extracted; the leaf functions it
 * drives are what lower to C and what this wrapper links against.
 *
 * Like `sb filename` with no other command-line options, it takes exactly one
 * argument: the path of the file to send.
 *
 * This wrapper is UNVERIFIED C.  It is written to compile and to exercise the
 * extracted ABI; because the extracted implementation is currently a skeleton
 * (admit ()), it is not meant to be run.
 */

#include "YModem_Impl_Server.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define YM_SOH   0x01u
#define YM_EOT   0x04u
#define YM_ACK   0x06u
#define YM_NAK   0x15u
#define YM_CAN   0x18u
#define YM_CRC_C 0x43u

#define YM_PKT_LEN  133
#define YM_DATA_LEN 128
#define YM_PAD_BYTE 0x1Au /* CTRL-Z: pads the final short data block */

static int read_full(int fd, uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = read(fd, buf + off, len - off);
    if (n < 0) {
      if (errno == EINTR) continue;
      return -1;
    }
    if (n == 0) return -1;
    off += (size_t)n;
  }
  return 0;
}

static int write_full(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, buf + off, len - off);
    if (n < 0) {
      if (errno == EINTR) continue;
      return -1;
    }
    if (n == 0) return -1;
    off += (size_t)n;
  }
  return 0;
}

static int read_byte(int fd) {
  uint8_t b;
  if (read_full(fd, &b, 1) != 0) return -1;
  return (int)b;
}

/* Wait for a specific control byte from the receiver (skipping others). */
static int wait_for(int fd, uint8_t want) {
  for (;;) {
    int b = read_byte(fd);
    if (b < 0) return -1;
    if (b == (int)YM_CAN) return -1;
    if (b == (int)want) return 0;
  }
}

/* The basename of a path (the receiver stores under this name). */
static const char *base_name(const char *path) {
  const char *slash = strrchr(path, '/');
  return slash ? slash + 1 : path;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: ymodem_sb filename\n");
    return 2;
  }

  const char *path = argv[1];
  const char *name = base_name(path);

  FILE *in = fopen(path, "rb");
  if (in == NULL) {
    fprintf(stderr, "ymodem_sb: cannot open %s\n", path);
    return 1;
  }

  if (fseek(in, 0, SEEK_END) != 0) { fclose(in); return 1; }
  long size = ftell(in);
  if (size < 0) { fclose(in); return 1; }
  rewind(in);

  uint8_t packet[YM_PKT_LEN];
  uint8_t chunk[YM_DATA_LEN];

  /* The receiver opens with 'C' (CRC mode) or NAK. */
  if (wait_for(STDIN_FILENO, YM_CRC_C) != 0) { fclose(in); return 1; }

  /* Header block 0: file name + declared length, built by the extracted core. */
  ymodem_server_emit_header((uint8_t *)name, strlen(name),
                            (uint32_t)size, packet);
  if (write_full(STDOUT_FILENO, packet, YM_PKT_LEN) != 0) { fclose(in); return 1; }
  if (wait_for(STDIN_FILENO, YM_ACK) != 0) { fclose(in); return 1; }
  if (wait_for(STDIN_FILENO, YM_CRC_C) != 0) { fclose(in); return 1; }

  /* Data blocks 1, 2, ..., padding the final short block. */
  uint8_t blk = 1;
  for (;;) {
    size_t n = fread(chunk, 1, YM_DATA_LEN, in);
    if (n == 0) break;
    if (n < YM_DATA_LEN) {
      memset(chunk + n, YM_PAD_BYTE, YM_DATA_LEN - n);
    }
    ymodem_server_emit_block(blk, chunk, packet);
    if (write_full(STDOUT_FILENO, packet, YM_PKT_LEN) != 0) { fclose(in); return 1; }
    if (wait_for(STDIN_FILENO, YM_ACK) != 0) { fclose(in); return 1; }
    blk++;
  }

  /* End of file, then the terminating null header block (empty name). */
  {
    uint8_t eot = (uint8_t)YM_EOT;
    if (write_full(STDOUT_FILENO, &eot, 1) != 0) { fclose(in); return 1; }
  }
  if (wait_for(STDIN_FILENO, YM_ACK) != 0) { fclose(in); return 1; }

  ymodem_server_emit_header((uint8_t *)"", 0, 0, packet);
  if (write_full(STDOUT_FILENO, packet, YM_PKT_LEN) != 0) { fclose(in); return 1; }
  wait_for(STDIN_FILENO, YM_ACK);

  fclose(in);
  return 0;
}
