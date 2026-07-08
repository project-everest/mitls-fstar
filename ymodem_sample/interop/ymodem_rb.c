/*
 * ymodem_rb.c — unverified YMODEM receiver wrapper (an `rb`-style program).
 *
 * This is the interoperability wrapper for the *receiver* side.  It speaks the
 * YMODEM protocol over stdin/stdout (as lrzsz's `rb` does over a serial line),
 * and delegates the per-packet work — validating a 133-byte packet and
 * extracting its 128-byte payload — to the extracted (currently skeleton)
 * function `ymodem_client_recv_block` from YModem.Impl.Client.
 *
 * `ymodem_client_recv_block` is the executable *leaf* operation of the receiver
 * state-machine implementation: it is the packet-parsing step invoked by
 * `pi_process_network` of the YMODEM client `protocol_implementation` instance
 * `YModem.Impl.Client.CanonicalProtocol.ymodem_client_protocol_implementation`.
 * That instance (the verified refinement witness) is not itself Low* — like
 * every type-class dictionary it holds separation-logic and ghost fields — so it
 * is verified but not extracted; the leaf function it drives is what lowers to C
 * and what this wrapper links against.
 *
 * Like `rb` with no command-line options, it takes no arguments: the file name
 * is taken from the YMODEM header block (block 0), and the file is written to
 * the current directory.
 *
 * This wrapper is UNVERIFIED C.  It is written to compile and to exercise the
 * extracted ABI; because the extracted implementation is currently a skeleton
 * (admit ()), it is not meant to be run.
 */

#include "YModem_Impl_Client.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define YM_SOH   0x01u
#define YM_STX   0x02u
#define YM_EOT   0x04u
#define YM_ACK   0x06u
#define YM_NAK   0x15u
#define YM_CAN   0x18u
#define YM_CRC_C 0x43u /* 'C': request 16-bit CRC mode */

#define YM_PKT_LEN  133 /* SOH | blk | ~blk | data[128] | crc[2] */
#define YM_DATA_LEN 128

/* Read exactly len bytes from fd; returns 0 on success, -1 on EOF/error. */
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

/* Write a single control byte to fd; returns 0 on success, -1 on error. */
static int write_byte(int fd, uint8_t b) {
  while (write(fd, &b, 1) < 0) {
    if (errno == EINTR) continue;
    return -1;
  }
  return 0;
}

/* Read a single byte from fd; returns the byte (0..255) or -1 on EOF/error. */
static int read_byte(int fd) {
  uint8_t b;
  if (read_full(fd, &b, 1) != 0) return -1;
  return (int)b;
}

int main(void) {
  uint8_t packet[YM_PKT_LEN];
  uint8_t data[YM_DATA_LEN];
  char    filename[256];
  uint32_t file_len = 0;
  uint32_t received = 0;
  FILE    *out = NULL;
  int      have_file = 0;

  filename[0] = '\0';

  /* Kick off a CRC-mode transfer. */
  if (write_byte(STDOUT_FILENO, YM_CRC_C) != 0) return 1;

  for (;;) {
    int lead = read_byte(STDIN_FILENO);
    if (lead < 0) break;

    if (lead == (int)YM_EOT) {
      /* End of file: acknowledge and re-arm for the next file (or the
         terminating null header block). */
      write_byte(STDOUT_FILENO, YM_ACK);
      write_byte(STDOUT_FILENO, YM_CRC_C);
      if (out != NULL) {
        fclose(out);
        out = NULL;
      }
      have_file = 0;
      received = 0;
      continue;
    }

    if (lead == (int)YM_CAN) break; /* transfer cancelled */

    if (lead != (int)YM_SOH && lead != (int)YM_STX) {
      /* Unexpected lead byte: ask for a retransmission. */
      write_byte(STDOUT_FILENO, YM_NAK);
      continue;
    }

    /* Read the rest of the (128-byte) packet.  STX/1024-byte packets are not
       handled by this wrapper; treat them as an error. */
    if (lead != (int)YM_SOH) {
      write_byte(STDOUT_FILENO, YM_NAK);
      continue;
    }
    packet[0] = (uint8_t)lead;
    if (read_full(STDIN_FILENO, packet + 1, YM_PKT_LEN - 1) != 0) break;

    /* Delegate validation + payload extraction to the extracted core. */
    uint8_t blk = ymodem_client_recv_block(packet, data);

    if (blk == 0) {
      /* Header block: an empty name marks the end of the batch. */
      if (data[0] == 0) {
        write_byte(STDOUT_FILENO, YM_ACK);
        break;
      }
      memcpy(filename, data, YM_DATA_LEN);
      filename[YM_DATA_LEN] = '\0';
      /* The ASCII file length follows the NUL-terminated name. */
      size_t name_end = strnlen(filename, sizeof(filename));
      file_len = 0;
      if (name_end + 1 < YM_DATA_LEN) {
        file_len = (uint32_t)strtoul((const char *)(data + name_end + 1), NULL, 10);
      }
      received = 0;
      out = fopen(filename, "wb");
      if (out == NULL) {
        write_byte(STDOUT_FILENO, YM_CAN);
        break;
      }
      have_file = 1;
      write_byte(STDOUT_FILENO, YM_ACK);
      write_byte(STDOUT_FILENO, YM_CRC_C);
    } else if (have_file) {
      /* Data block: write only the real (un-padded) bytes, truncating the
         padded final block to the declared length. */
      uint32_t remaining = (file_len > received) ? (file_len - received) : 0;
      uint32_t n = (remaining < YM_DATA_LEN) ? remaining : YM_DATA_LEN;
      if (n > 0) {
        fwrite(data, 1, n, out);
        received += n;
      }
      write_byte(STDOUT_FILENO, YM_ACK);
    } else {
      /* Data block before a header: ignore, request retransmission. */
      write_byte(STDOUT_FILENO, YM_NAK);
    }
  }

  if (out != NULL) fclose(out);
  return 0;
}
