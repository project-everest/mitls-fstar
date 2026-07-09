/*
 * ymodem_sb.c — YMODEM sender (`sb filename`-style) whose data-transfer loop is
 * the VERIFIED, extracted Pulse driver loop `ymodem_server_run`.
 *
 * The core send loop — framing and emitting each 128-byte data block through the
 * verified codec (with the correct incrementing block number and a real
 * CRC-16), awaiting each ACK, and closing with the EOT — is the verified
 * F-star/Pulse loop extracted to C in YModem_Verified.c.  This program is the
 * thin, UNVERIFIED glue around it: reading the file, the initial 'C' wait, the
 * YMODEM header block 0 (file name / length), and the end-of-batch terminating
 * null block — all outside the modeled state machine.
 *
 * End-of-batch handshake (interoperable with lrzsz `rb`, per the Forsberg
 * X/YMODEM reference): after the data transfer the sender waits for the
 * receiver's 'C' before transmitting the terminating null header block (sending
 * it early races rb's input purge and deadlocks the session).
 *
 * It speaks YMODEM over stdin (ACK/NAK/'C') / stdout (packets); the verified
 * loop reads and writes through a Common.TCP channel bridging those descriptors.
 */

#include "YModem_Verified.h"
#include "common_tcp_karamel.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>

#define YM_SOH   0x01u
#define YM_EOT   0x04u
#define YM_ACK   0x06u
#define YM_NAK   0x15u
#define YM_CAN   0x18u
#define YM_CRC_C 0x43u

#define YM_PKT_LEN  133
#define YM_DATA_LEN 128
#define YM_PAD_BYTE 0x1Au /* CTRL-Z */
#define FUEL        1000000

static int read_full(int fd, uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = read(fd, buf + off, len - off);
    if (n < 0) { if (errno == EINTR) continue; return -1; }
    if (n == 0) return -1;
    off += (size_t)n;
  }
  return 0;
}

static int write_full(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, buf + off, len - off);
    if (n < 0) { if (errno == EINTR) continue; return -1; }
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

static const char *base_name(const char *path) {
  const char *slash = strrchr(path, '/');
  return slash ? slash + 1 : path;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: ymodem_sb filename\n"); return 2; }
  signal(SIGPIPE, SIG_IGN); /* a late write to a closed peer must not kill us */
  const char *path = argv[1];
  const char *name = base_name(path);

  FILE *in = fopen(path, "rb");
  if (in == NULL) { fprintf(stderr, "ymodem_sb: cannot open %s\n", path); return 1; }
  if (fseek(in, 0, SEEK_END) != 0) { fclose(in); return 1; }
  long size = ftell(in);
  if (size < 0) { fclose(in); return 1; }
  rewind(in);

  /* Read the whole file and pad to a whole number of 128-byte blocks. */
  size_t nblocks = (size == 0) ? 0 : (size_t)((size + YM_DATA_LEN - 1) / YM_DATA_LEN);
  size_t padded = nblocks * YM_DATA_LEN;
  uint8_t *infile = calloc(padded ? padded : 1, 1);
  if (!infile) { fclose(in); return 1; }
  if (size > 0 && fread(infile, 1, (size_t)size, in) != (size_t)size) { fclose(in); free(infile); return 1; }
  fclose(in);
  memset(infile + size, YM_PAD_BYTE, padded - (size_t)size);

  uint8_t packet[YM_PKT_LEN];

  /* The receiver opens with 'C' (CRC mode). */
  if (wait_for(STDIN_FILENO, YM_CRC_C) != 0) { free(infile); return 1; }

  /* ── Header block 0 (impl glue): NUL-terminated name + ASCII length in the
     128-byte payload, framed as block 0 by the verified codec. */
  {
    uint8_t header[YM_DATA_LEN];
    memset(header, 0, YM_DATA_LEN);
    size_t nlen = strlen(name);
    if (nlen > YM_DATA_LEN - 16) nlen = YM_DATA_LEN - 16;
    memcpy(header, name, nlen);
    header[nlen] = 0;
    snprintf((char *)(header + nlen + 1), YM_DATA_LEN - nlen - 1, "%ld", size);
    ymodem_emit_data_block(0, header, packet); /* verified codec */
  }
  if (write_full(STDOUT_FILENO, packet, YM_PKT_LEN) != 0) { free(infile); return 1; }
  if (wait_for(STDIN_FILENO, YM_ACK) != 0) { free(infile); return 1; }
  if (wait_for(STDIN_FILENO, YM_CRC_C) != 0) { free(infile); return 1; }

  /* ── Data transfer: the VERIFIED loop ──────────────────────────────────
     ymodem_server_run frames + emits data blocks 1..N (correct block numbers +
     CRC-16 via the verified codec), awaits each ACK, and sends the EOT. */
  uint8_t *blk  = malloc(YM_DATA_LEN);
  uint8_t *out  = malloc(YM_PKT_LEN);
  uint8_t *ctrl = malloc(1);
  uint8_t *ysnf = malloc(YM_DATA_LEN);
  if (!blk || !out || !ctrl || !ysnf) { free(infile); return 1; }

  uint8_t *i = new_ymodem_server();
  Common_TCP_channel ch = Common_TCP_channel_of_fds(STDIN_FILENO, STDOUT_FILENO);
  ymodem_server_run(i, ch, infile, nblocks, blk, out, ctrl, ysnf, (size_t)FUEL);
  /* NB: keep the channel (fds 0/1) open — the end-of-batch glue below still
     reads/writes them; the channel is closed only at the very end. */

  /* ── End of batch (impl glue): wait for the receiver's 'C' before the
     terminating null header block (the deadlock fix), then send it. */
  if (wait_for(STDIN_FILENO, YM_CRC_C) != 0) { free(infile); free(i); free(blk); free(out); free(ctrl); free(ysnf); return 0; }
  {
    uint8_t zero_header[YM_DATA_LEN];
    memset(zero_header, 0, YM_DATA_LEN);
    ymodem_emit_data_block(0, zero_header, packet);
  }
  write_full(STDOUT_FILENO, packet, YM_PKT_LEN);
  wait_for(STDIN_FILENO, YM_ACK);

  Common_TCP_close(ch);
  free(infile); free(i); free(blk); free(out); free(ctrl); free(ysnf);
  return 0;
}
