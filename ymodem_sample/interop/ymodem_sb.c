/*
 * ymodem_sb.c — unverified YMODEM sender wrapper (an `sb filename`-style program).
 *
 * This is the interoperability wrapper for the *sender* side.  It speaks the
 * YMODEM protocol over stdin/stdout (as lrzsz's `sb` does over a serial line),
 * and delegates the per-packet framing — building the 133-byte data packet
 * (SOH | block number | complement | 128-byte payload | CRC-16) — to the
 * extracted, verified leaf `ymodem_emit_data_block` from YModem.Impl.Codec.  The
 * YMODEM header is simply block 0 whose 128-byte payload carries the file name
 * and declared length; this wrapper formats that payload and calls
 * `ymodem_emit_data_block 0 header out`.
 *
 * `ymodem_emit_data_block` is the executable *leaf* codec of the sender side: its
 * post-condition proves `out` holds the LowParse serialization (via the
 * `ymodem_message` union) of a `Body_soh body` whose 128-byte payload is exactly
 * the input chunk.  It is verified against the QuackyDucky wire format; only this
 * leaf lowers to C, and this wrapper links against it.  The control frames
 * (EOT/ACK/NAK/CAN/'C') are single literal bytes, written/compared directly here.
 *
 * Like `sb filename` with no other command-line options, it takes exactly one
 * argument: the path of the file to send.
 *
 * This wrapper is UNVERIFIED C.  It orchestrates the verified leaf over the
 * YMODEM handshake; it is written to compile and interoperate with lrzsz.
 *
 * End-of-session handshake (interoperable with lrzsz `rb`, per the Forsberg
 * X/YMODEM reference, Chuck Forsberg 1988):
 *   - After the last data block, the sender transmits EOT and waits for an ACK,
 *     re-sending EOT up to ten times until it is acknowledged ("the sending
 *     program shall send EOT up to ten times until it receives an ACK").
 *   - The end of the batch is a terminating null header block (block 0 with an
 *     empty pathname), "acknowledged the same as other pathname blocks" — i.e.
 *     it too is solicited by a 'C' from the receiver, so the sender waits for
 *     that 'C' before transmitting it (exactly as it waited for the first 'C'
 *     before the first header block).  Sending the null block *without* waiting
 *     for that 'C' races the receiver's input purge and deadlocks the session.
 */

#include "YModem_Impl_Codec.h"

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
#define YM_EOT_RETRIES 10 /* resend EOT up to ten times until ACK (XMODEM/YMODEM) */

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

/* Send EOT and wait for the receiver's ACK, re-sending EOT up to YM_EOT_RETRIES
   times if the receiver answers with NAK (or anything that is not an ACK).
   Returns 0 once the EOT is acknowledged, -1 on error / cancel / exhaustion. */
static int send_eot(int rfd, int wfd) {
  for (int attempt = 0; attempt < YM_EOT_RETRIES; attempt++) {
    uint8_t eot = (uint8_t)YM_EOT;
    if (write_full(wfd, &eot, 1) != 0) return -1;
    int b = read_byte(rfd);
    if (b < 0) return -1;
    if (b == (int)YM_ACK) return 0;
    if (b == (int)YM_CAN) return -1;
    /* NAK or any other byte: re-send EOT. */
  }
  return -1;
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

  /* Header block 0: its 128-byte payload carries the NUL-terminated file name
     followed by the file length in ASCII decimal (built here, in the unverified
     wrapper); the verified codec then frames it as block 0. */
  {
    uint8_t header[YM_DATA_LEN];
    memset(header, 0, YM_DATA_LEN);
    size_t nlen = strlen(name);
    if (nlen > YM_DATA_LEN - 16) nlen = YM_DATA_LEN - 16;
    memcpy(header, name, nlen);
    header[nlen] = 0;
    snprintf((char *)(header + nlen + 1), YM_DATA_LEN - nlen - 1, "%ld", size);
    ymodem_emit_data_block(0, header, packet);
  }
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
    ymodem_emit_data_block(blk, chunk, packet);
    if (write_full(STDOUT_FILENO, packet, YM_PKT_LEN) != 0) { fclose(in); return 1; }
    if (wait_for(STDIN_FILENO, YM_ACK) != 0) { fclose(in); return 1; }
    blk++;
  }

  /* End of file: send EOT (retrying until ACK). */
  if (send_eot(STDIN_FILENO, STDOUT_FILENO) != 0) { fclose(in); return 1; }

  /* The receiver now solicits the next file with 'C'; wait for it before
     sending the terminating null header block — exactly as we waited for the
     first 'C' before the first header block.  (Sending it early races the
     receiver's input purge and deadlocks the session.) */
  if (wait_for(STDIN_FILENO, YM_CRC_C) != 0) { fclose(in); return 1; }

  /* Terminating null header block: block 0 with an all-zero 128-byte payload
     (empty name) signals the end of the batch. */
  {
    uint8_t zero_header[YM_DATA_LEN];
    memset(zero_header, 0, YM_DATA_LEN);
    ymodem_emit_data_block(0, zero_header, packet);
  }
  if (write_full(STDOUT_FILENO, packet, YM_PKT_LEN) != 0) { fclose(in); return 1; }
  wait_for(STDIN_FILENO, YM_ACK);

  fclose(in);
  return 0;
}
