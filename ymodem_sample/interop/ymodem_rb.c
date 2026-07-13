/*
 * ymodem_rb.c — YMODEM receiver (`rb`-style) whose data-transfer loop is the
 * VERIFIED, extracted Pulse driver loop `ymodem_client_run`.
 *
 * Unlike the previous wrapper (whose per-packet loop was unverified C), the core
 * receive loop here — framing each incoming message, validating/decoding it via
 * the verified codec, driving the state machine, and emitting each ACK — is the
 * verified F-star/Pulse loop extracted to C in YModem_Verified.c.  This program
 * is the thin, UNVERIFIED glue around it: the YMODEM header block 0 (file name /
 * length), the initial 'C' CRC solicitation, writing the reconstructed bytes to
 * disk, and the end-of-batch null block — all of which live outside the modeled
 * state machine.
 *
 * It speaks YMODEM over stdin (received bytes) / stdout (ACK/NAK/'C'); the
 * verified loop reads and writes through a Common.TCP channel bridging those two
 * descriptors.
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

static int write_byte(int fd, uint8_t b) {
  while (write(fd, &b, 1) < 0) { if (errno == EINTR) continue; return -1; }
  return 0;
}

static int read_byte(int fd) {
  uint8_t b;
  if (read_full(fd, &b, 1) != 0) return -1;
  return (int)b;
}

/* Read one 133-byte SOH packet: the caller has already consumed the SOH lead
   byte, so read the remaining 132 into packet[1..]. */
static int read_soh_rest(int fd, uint8_t *packet) {
  packet[0] = YM_SOH;
  return read_full(fd, packet + 1, YM_PKT_LEN - 1);
}

int main(void) {
  uint8_t packet[YM_PKT_LEN];
  uint8_t data[YM_DATA_LEN];
  char    filename[YM_DATA_LEN + 1];
  uint32_t file_len = 0;
  FILE    *out = NULL;

  signal(SIGPIPE, SIG_IGN); /* a late write to a closed peer must not kill us */
  /* Kick off a CRC-mode transfer. */
  if (write_byte(STDOUT_FILENO, YM_CRC_C) != 0) return 1;

  /* ── Header block 0 (impl glue: not part of the state machine) ──────────
     Wait for the leading SOH, read the 133-byte header, decode it with the
     verified codec, and pull the NUL-terminated name + ASCII length out of the
     128-byte payload. */
  for (;;) {
    int lead = read_byte(STDIN_FILENO);
    if (lead < 0) return 1;
    if (lead == (int)YM_CAN) return 1;
    if (lead == (int)YM_SOH) break;
    /* stray byte before the header: re-solicit */
    write_byte(STDOUT_FILENO, YM_CRC_C);
  }
  if (read_soh_rest(STDIN_FILENO, packet) != 0) return 1;
  (void)ymodem_recv_data_block(packet, data); /* verified codec: extract the 128-byte payload */

  if (data[0] == 0) {
    /* An immediate empty-name header is an empty batch: acknowledge and stop. */
    write_byte(STDOUT_FILENO, YM_ACK);
    return 0;
  }
  memcpy(filename, data, YM_DATA_LEN);
  filename[YM_DATA_LEN] = '\0';
  size_t name_end = strnlen(filename, sizeof(filename));
  if (name_end + 1 < YM_DATA_LEN) {
    file_len = (uint32_t)strtoul((const char *)(data + name_end + 1), NULL, 10);
  }
  out = fopen(filename, "wb");
  if (out == NULL) { write_byte(STDOUT_FILENO, YM_CAN); return 1; }
  write_byte(STDOUT_FILENO, YM_ACK);
  write_byte(STDOUT_FILENO, YM_CRC_C);

  /* ── Data transfer: the VERIFIED loop ──────────────────────────────────
     ymodem_client_run reads data blocks 1..N and the EOT, validates/decodes
     each with the verified codec, drives the state machine, emits every ACK,
     and reconstructs the padded file into outbuf. */
  size_t   ncap  = (size_t)((file_len + YM_DATA_LEN - 1) / YM_DATA_LEN) * YM_DATA_LEN;
  if (ncap == 0) ncap = YM_DATA_LEN;
  uint8_t *outbuf = calloc(ncap, 1);
  uint8_t *ctrl = malloc(1), *soh = malloc(YM_PKT_LEN), *tail = malloc(YM_PKT_LEN - 1),
          *ack  = malloc(1), *ycnf = malloc(YM_DATA_LEN);
  if (!outbuf || !ctrl || !soh || !tail || !ack || !ycnf) { fclose(out); return 1; }

  uint8_t *i = new_ymodem_client();
  ymodem_client_start(i);
  Common_TCP_channel ch = Common_TCP_channel_of_fds(STDIN_FILENO, STDOUT_FILENO);

  size_t nbytes = ymodem_client_run(i, ch, ctrl, soh, tail, ack, ycnf, outbuf, ncap, (size_t)FUEL);

  /* Persist the reconstructed file, truncated to the declared length (the
     padding of the final block is not part of the file). */
  size_t towrite = (nbytes < (size_t)file_len) ? nbytes : (size_t)file_len;
  if (towrite > 0) fwrite(outbuf, 1, towrite, out);
  fclose(out);

  /* ── End of batch (impl glue): the verified loop stopped after ACKing the
     EOT; solicit and acknowledge the terminating null header block. */
  write_byte(STDOUT_FILENO, YM_CRC_C);
  for (;;) {
    int lead = read_byte(STDIN_FILENO);
    if (lead < 0) break;
    if (lead == (int)YM_EOT) { write_byte(STDOUT_FILENO, YM_ACK); write_byte(STDOUT_FILENO, YM_CRC_C); continue; }
    if (lead == (int)YM_CAN) break;
    if (lead == (int)YM_SOH) {
      if (read_soh_rest(STDIN_FILENO, packet) != 0) break;
      (void)ymodem_recv_data_block(packet, data);
      write_byte(STDOUT_FILENO, YM_ACK); /* the null header block: acknowledge and finish */
      break;
    }
  }

  Common_TCP_close(ch);
  free(i); free(outbuf); free(ctrl); free(soh); free(tail); free(ack); free(ycnf);
  return 0;
}
