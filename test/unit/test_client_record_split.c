/* Client-side framing matrix: the mirror of test_server_interop_matrix's
 * framing axis, run in the server->client direction.
 *
 * WHY THIS FILE EXISTS.  `test_server_interop_matrix` re-frames the
 * client->server byte stream and records what the verified SERVER does with a
 * ClientHello torn across records.  Nothing measured the symmetric question:
 * what does the VERIFIED CLIENT do when the SERVER's cleartext ServerHello
 * arrives as two records?  The answer was asserted in prose in
 * docs/server-client-parity.md and in the header of
 * test_server_interop_matrix.c -- "there is no cleartext reassembly in the
 * tree for either role" -- but never executed.  This harness executes it, so
 * the client-side half of G3 is a ledger row rather than a claim in a comment
 * that quietly goes stale.  The row was recorded as a GAP, failed loudly when
 * the capability landed, and is now recorded as OK.
 *
 * WHAT IS AND IS NOT COVERED, AND WHY THE CONTROLS MATTER.  A single cell
 * proves little on its own: a harness that broke the connection for any reason
 * at all would report "refused" and, while the row expected refused, would
 * have looked green.  So the ledger below shares one proxy across five cells:
 *
 *   FRAMING_NORMAL        the proxy relays byte for byte.  Expect OK.  This
 *                         cell exists to prove the proxy is transparent, so
 *                         that the behaviour of the split cells is
 *                         attributable to the re-framing and not to the
 *                         harness.
 *
 *   FRAMING_TCP_DRIBBLE   the ServerHello record is delivered in many small
 *                         TCP segments.  Expect OK.  This separates the two
 *                         fragmentations that are easy to conflate: TCP-level
 *                         segmentation, which the client's retained receive
 *                         buffer and NeedMoreInput retry loop already handle,
 *                         from RECORD-level segmentation, which is G3.  Without
 *                         this cell a reader could not tell which of the two
 *                         the split cells are actually measuring.
 *
 *   FRAMING_RECORD_SPLIT  the ServerHello is delivered as TWO handshake
 *                         records.  ACCEPTED as of G3.  The first record is a
 *                         cleartext record that does not parse on its own, so
 *                         the client buffers it
 *                         (`try_buffer_cleartext_handshake_record`); the
 *                         record that completes the message is coalesced with
 *                         the pending bytes and delivered by
 *                         `try_deliver_reassembled_server_hello`, both in
 *                         TLS13.Impl.Client.fst.  This is the client-side
 *                         mirror of `clienthello-across-two-records`.
 *
 *   FRAMING_RECORD_SPLIT3 the same message delivered as THREE TLS records.
 *                         This is not redundant with the two-record cell: two
 *                         records only ever buffer onto an EMPTY pending
 *                         buffer and then deliver, whereas three records make
 *                         the middle one coalesce onto an ALREADY NON-EMPTY
 *                         buffer, which is a distinct branch of the buffering
 *                         step.
 *
 *   FRAMING_RECORD_SPLIT_MANY
 *                         the same message delivered as 8-byte records, so N
 *                         follows from the ServerHello's size rather than from
 *                         the harness.  This cell is NOT about branch coverage
 *                         -- three records already saturate the branch
 *                         structure, and a fourth takes the identical path to
 *                         the third.  It exists because "2 and 3" invites the
 *                         reading that reassembly is special-cased for small N,
 *                         and it is not: `cleartext_handshake_stream` is
 *                         `pending ++ fragment` and NO RECORD COUNTER appears
 *                         anywhere in the step relation, so the only limits are
 *                         the byte cap (`max_pending_cleartext_handshake`,
 *                         32768) and the requirement that each fragment be
 *                         non-empty.  The proxy prints the N it produced rather
 *                         than this comment fixing one, since N is a property
 *                         of the peer's ServerHello and not of the test.
 *
 * WHY THE DELIVERY IS NOT ON THE RECORD-LOCAL PATH.  The record-local
 * ServerHello delivery in TLS13.Impl.Handle.Handshake gates on
 * `can_receive && buffer_empty`, so it deliberately declines to fire while a
 * partial message is pending.  `CN.mark_received_server_hello` itself imposes
 * no such gate, which is exactly what lets the reassembled path take the
 * buffered reading of `received_cleartext_tls_message_raw_buffered` without
 * disturbing the unbuffered one.
 *
 * The client's `protected_handshake_buffering` does NOT cover these cells.  It
 * is confined to the PROTECTED path and to stages at or after ServerHello
 * (`protected_handshake_buffering_stage` = HsServerHelloReceived,
 * HsEncryptedExtensionsReceived, HsCertificateValidated,
 * HsCertificateVerifyVerified).  A ServerHello is cleartext and precedes all
 * of them, so it takes the cleartext path, which is what G3 added.  That
 * cross-record PROTECTED buffering IS exercised, but by the real-world sweep
 * in test/interop (Meta serves its flight in three protected records, with
 * Certificate starting at offset 6 of the first and running past its end) --
 * not by this file.
 *
 * WHY THE SPLIT IS PLACED WHERE IT IS.  Past the 4-byte handshake header, so
 * the receiver has the message's declared length in the first record and can
 * tell the message is truncated rather than malformed; and strictly inside the
 * body, so it lands mid-message.  A ServerHello is one handshake message, so
 * any interior split is exactly the reassembly case under test.  Both records
 * carry content type 22: this is legal TLS 1.3 framing that a conforming peer
 * reassembles, not a protocol violation.  Only the CLEARTEXT ServerHello is
 * re-framed; a protected record is a single AEAD-sealed unit, so splitting its
 * ciphertext would test nothing but the AEAD tag.
 *
 * READING A FAILURE.  If a split cell reports refused where the ledger says
 * ok, cleartext reassembly regressed -- but read the CONTROL cells first: if
 * `passthrough` or `serverhello-tcp-dribble` also reports refused, the harness
 * or the proxy is broken and the split cells say nothing at all.
 *
 * WHAT A REFUSAL ACTUALLY IS.  Each cell connects with
 * `tls13_client_driver_connect_reporting` rather than the plain `_connect`,
 * because a failed connect destroys the driver that carried the verified
 * workflow status, and a bare "refused" cannot distinguish a protocol reason
 * from a dead proxy.  Before G3 the split cell reported "connect: verified
 * protocol step failed" -- the verified state machine rejecting a truncated
 * ServerHello -- and not a TCP error or a timeout.
 */

#include "tls13_client_driver.h"

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

typedef enum {
  FRAMING_NORMAL = 0,
  FRAMING_TCP_DRIBBLE,
  FRAMING_RECORD_SPLIT,
  FRAMING_RECORD_SPLIT3,
  FRAMING_RECORD_SPLIT_MANY,
} framing_mode;

struct case_spec {
  const char *name;
  framing_mode framing;
  bool expect_ok;
  const char *note;
};

static const struct case_spec k_cases[] = {
    {"passthrough", FRAMING_NORMAL, true,
     "control: the proxy relays byte for byte, so the other two cells are "
     "attributable to their re-framing"},
    {"serverhello-tcp-dribble", FRAMING_TCP_DRIBBLE, true,
     "control: TCP-level segmentation of one record, absorbed by the client's "
     "retained receive buffer and NeedMoreInput retry loop"},
    {"serverhello-across-two-records", FRAMING_RECORD_SPLIT, true,
     "G3: the ServerHello is reassembled out of the cleartext buffer -- the "
     "first record is consumed by a ConnCleartextHandshake buffering step "
     "(try_buffer_cleartext_handshake_record) and the second is coalesced "
     "with the pending bytes and delivered "
     "(try_deliver_reassembled_server_hello), both in TLS13.Impl.Client.fst.  "
     "The mirror of clienthello-across-two-records"},
    /* Three records, not two: the middle record is buffered onto an ALREADY
       NON-EMPTY pending buffer, which is the coalescing step that a
       two-record split never reaches.  Mirror of
       clienthello-across-three-records. */
    {"serverhello-across-three-records", FRAMING_RECORD_SPLIT3, true,
     "G3: two buffering steps then a delivery -- the middle record coalesces "
     "onto a non-empty buffer"},
    /* N records, for N determined by the message size rather than by the
       harness.  Three records already SATURATE the branch structure -- a
       fourth record takes the identical path to the third -- so this cell is
       not about coverage.  It exists to demonstrate that the capability is
       genuinely inductive in the pending buffer rather than special-cased for
       small N: `cleartext_handshake_stream` is `pending ++ fragment` and no
       record counter appears anywhere in the step relation, so the only limit
       is the byte cap. */
    {"serverhello-across-many-records", FRAMING_RECORD_SPLIT_MANY, true,
     "G3: the reassembly is inductive, not special-cased -- the ServerHello is "
     "delivered as 8-byte records and every one after the first coalesces onto "
     "a non-empty buffer.  The proxy reports the record count it produced"},
};

#define CASE_COUNT (sizeof k_cases / sizeof k_cases[0])

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return 1;
  }
  if (fseek(f, 0, SEEK_END) != 0 || ftell(f) < 0) {
    perror(path);
    fclose(f);
    return 1;
  }
  long len = ftell(f);
  rewind(f);
  uint8_t *buf = calloc((size_t)len == 0 ? 1u : (size_t)len, sizeof(uint8_t));
  if (buf == NULL || fread(buf, 1u, (size_t)len, f) != (size_t)len) {
    perror(path);
    free(buf);
    fclose(f);
    return 1;
  }
  fclose(f);
  *out = buf;
  *out_len = (size_t)len;
  return 0;
}

static int reserve_loopback_port(uint16_t *port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    perror("socket");
    return -1;
  }
  int one = 1;
  (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(0);
  if (bind(fd, (struct sockaddr *)&addr, sizeof addr) != 0) {
    perror("bind");
    close(fd);
    return -1;
  }
  struct sockaddr_in bound;
  socklen_t bound_len = sizeof bound;
  if (getsockname(fd, (struct sockaddr *)&bound, &bound_len) != 0) {
    perror("getsockname");
    close(fd);
    return -1;
  }
  *port = ntohs(bound.sin_port);
  close(fd);
  return 0;
}

static int connect_loopback(uint16_t port) {
  for (int attempt = 0; attempt < 200; ++attempt) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
      return -1;
    }
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof addr);
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons(port);
    if (connect(fd, (struct sockaddr *)&addr, sizeof addr) == 0) {
      return fd;
    }
    close(fd);
    usleep(20000);
  }
  return -1;
}

static int write_all(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, buf + off, len - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    if (n == 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

static int read_exact(int fd, uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = read(fd, buf + off, len - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    if (n == 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

/* Re-frames the FIRST server->client TLS record -- the ServerHello -- and
   relays everything else, in both directions, byte for byte.  The
   client->server direction is never re-framed: that direction is what
   test_server_interop_matrix already covers. */
static int run_proxy(uint16_t listen_port, uint16_t server_port,
                     framing_mode framing) {
  alarm(60);
  int rc = 1;
  int listen_fd = -1;
  int client_fd = -1;
  int server_fd = -1;
  int one = 1;

  listen_fd = socket(AF_INET, SOCK_STREAM, 0);
  if (listen_fd < 0) {
    perror("proxy socket");
    goto done;
  }
  (void)setsockopt(listen_fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(listen_port);
  if (bind(listen_fd, (struct sockaddr *)&addr, sizeof addr) != 0 ||
      listen(listen_fd, 1) != 0) {
    perror("proxy bind/listen");
    goto done;
  }
  client_fd = accept(listen_fd, NULL, NULL);
  if (client_fd < 0) {
    perror("proxy accept");
    goto done;
  }
  server_fd = connect_loopback(server_port);
  if (server_fd < 0) {
    perror("proxy connect");
    goto done;
  }
  (void)setsockopt(client_fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
  (void)setsockopt(server_fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);

  bool client_open = true;
  bool server_open = true;
  bool first_server_record_done = false;
  while (client_open || server_open) {
    fd_set rfds;
    FD_ZERO(&rfds);
    int maxfd = -1;
    if (client_open) {
      FD_SET(client_fd, &rfds);
      maxfd = client_fd > maxfd ? client_fd : maxfd;
    }
    if (server_open) {
      FD_SET(server_fd, &rfds);
      maxfd = server_fd > maxfd ? server_fd : maxfd;
    }
    struct timeval tv = {.tv_sec = 10, .tv_usec = 0};
    int ready = select(maxfd + 1, &rfds, NULL, NULL, &tv);
    if (ready < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }
    if (ready == 0) {
      break;
    }

    uint8_t buf[8192];
    if (client_open && FD_ISSET(client_fd, &rfds)) {
      ssize_t n = read(client_fd, buf, sizeof buf);
      if (n <= 0) {
        client_open = false;
        shutdown(server_fd, SHUT_WR);
      } else if (write_all(server_fd, buf, (size_t)n) != 0) {
        break;
      }
    }

    if (!server_open || !FD_ISSET(server_fd, &rfds)) {
      continue;
    }

    if (first_server_record_done) {
      ssize_t n = read(server_fd, buf, sizeof buf);
      if (n <= 0) {
        server_open = false;
        shutdown(client_fd, SHUT_WR);
      } else if (write_all(client_fd, buf, (size_t)n) != 0) {
        break;
      }
      continue;
    }

    /* The first record the server sends is the cleartext ServerHello.  Read
       it whole -- header then the declared fragment -- before deciding how to
       hand it on. */
    uint8_t header[5];
    if (read_exact(server_fd, header, sizeof header) != 0) {
      server_open = false;
      shutdown(client_fd, SHUT_WR);
      continue;
    }
    size_t frag_len = ((size_t)header[3] << 8) | (size_t)header[4];
    uint8_t *fragment = malloc(frag_len == 0 ? 1u : frag_len);
    if (fragment == NULL || read_exact(server_fd, fragment, frag_len) != 0) {
      fprintf(stderr, "proxy: short ServerHello fragment\n");
      free(fragment);
      goto done;
    }
    first_server_record_done = true;

    if (framing == FRAMING_RECORD_SPLIT_MANY &&
        header[0] == 22 /* handshake */ && frag_len >= 2) {
      /* One record per 8 bytes.  Nothing here depends on the resulting count:
         the loop just walks the fragment, so N follows from the ServerHello's
         size.  Every record after the first coalesces onto a non-empty
         buffer. */
      size_t off = 0;
      size_t records = 0;
      bool failed = false;
      while (off < frag_len && !failed) {
        size_t chunk = frag_len - off < 8 ? frag_len - off : 8;
        uint8_t part[5];
        memcpy(part, header, 5);
        part[3] = (uint8_t)((chunk >> 8) & 0xffu);
        part[4] = (uint8_t)(chunk & 0xffu);
        failed = write_all(client_fd, part, 5) != 0 ||
                 write_all(client_fd, fragment + off, chunk) != 0;
        off += chunk;
        records++;
        /* Shorter than the 50ms used by the two- and three-record cells,
           because there are many more of them; still long enough that the
           receiver sees each record on its own rather than finding several
           already buffered when it first parses. */
        usleep(10000);
      }
      /* Reported rather than asserted: the point of the cell is that N is
         whatever the message size makes it, so the harness states the N it
         actually produced instead of the test hard-coding one. */
      fprintf(stderr,
              "  proxy: split the %zu-byte ServerHello into %zu records\n",
              frag_len, records);
      if (failed) {
        free(fragment);
        goto done;
      }
    } else if (framing == FRAMING_RECORD_SPLIT3 &&
               header[0] == 22 /* handshake */ && frag_len >= 3) {
      /* THREE records, not two.  Two records only ever exercise buffering
         onto an EMPTY pending buffer followed by delivery; three additionally
         exercise the coalescing buffering step, where the middle record is
         appended to a buffer that is already non-empty and the combined
         stream still does not parse. */
      size_t thirds[3];
      thirds[0] = frag_len / 3;
      if (thirds[0] < 8) {
        thirds[0] = frag_len > 8 ? 8 : 1;
      }
      thirds[1] = (frag_len - thirds[0]) / 2;
      if (thirds[1] == 0) {
        thirds[1] = 1;
      }
      thirds[2] = frag_len - thirds[0] - thirds[1];
      size_t off = 0;
      bool failed = false;
      for (size_t i = 0; i < 3 && !failed; ++i) {
        uint8_t part[5];
        memcpy(part, header, 5);
        part[3] = (uint8_t)((thirds[i] >> 8) & 0xffu);
        part[4] = (uint8_t)(thirds[i] & 0xffu);
        failed = write_all(client_fd, part, 5) != 0 ||
                 write_all(client_fd, fragment + off, thirds[i]) != 0;
        off += thirds[i];
        /* A pause between records so the receiver genuinely sees each one on
           its own and cannot accidentally succeed by having them all buffered
           when it first parses. */
        usleep(50000);
      }
      if (failed) {
        free(fragment);
        goto done;
      }
    } else if (framing == FRAMING_RECORD_SPLIT &&
               header[0] == 22 /* handshake */ && frag_len >= 2) {
      size_t first = frag_len / 2;
      if (first < 8) {
        first = frag_len > 8 ? 8 : frag_len - 1;
      }
      size_t rest = frag_len - first;
      uint8_t head[5];
      uint8_t tail[5];
      memcpy(head, header, 5);
      memcpy(tail, header, 5);
      head[3] = (uint8_t)((first >> 8) & 0xffu);
      head[4] = (uint8_t)(first & 0xffu);
      tail[3] = (uint8_t)((rest >> 8) & 0xffu);
      tail[4] = (uint8_t)(rest & 0xffu);
      if (write_all(client_fd, head, 5) != 0 ||
          write_all(client_fd, fragment, first) != 0) {
        free(fragment);
        goto done;
      }
      /* A pause between the two records, so the receiver genuinely sees the
         first one on its own and cannot accidentally succeed by having both
         in its buffer when it first parses. */
      usleep(50000);
      if (write_all(client_fd, tail, 5) != 0 ||
          write_all(client_fd, fragment + first, rest) != 0) {
        free(fragment);
        goto done;
      }
    } else if (framing == FRAMING_TCP_DRIBBLE) {
      /* One TLS record, many TCP segments: the header byte by byte, then the
         fragment in small chunks, with a pause after each so the receiver's
         read() genuinely returns short. */
      bool failed = false;
      for (size_t i = 0; i < 5 && !failed; ++i) {
        failed = write_all(client_fd, header + i, 1) != 0;
        usleep(2000);
      }
      size_t off = 0;
      while (off < frag_len && !failed) {
        size_t chunk = frag_len - off < 7 ? frag_len - off : 7;
        failed = write_all(client_fd, fragment + off, chunk) != 0;
        off += chunk;
        usleep(2000);
      }
      if (failed) {
        free(fragment);
        goto done;
      }
    } else {
      if (write_all(client_fd, header, 5) != 0 ||
          write_all(client_fd, fragment, frag_len) != 0) {
        free(fragment);
        goto done;
      }
    }
    free(fragment);
  }
  rc = 0;

done:
  if (client_fd >= 0) {
    close(client_fd);
  }
  if (server_fd >= 0) {
    close(server_fd);
  }
  if (listen_fd >= 0) {
    close(listen_fd);
  }
  return rc;
}

/* Returns true when the verified client established the connection through the
   proxy AND completed one application round-trip.  One record each way is
   enough: this harness measures whether the handshake survives the re-framing,
   not how the connection behaves once established -- that is
   test_extracted_client_openssl_echo's job.

   A FRESH echo server is spawned per cell.  test/openssl_echo_server accepts
   exactly one connection and exits, so a single shared server would serve the
   first cell and leave every later cell's proxy reporting ECONNREFUSED -- and
   the split cell would then read as "refused" for a harness reason rather than
   the protocol reason under test.  That is precisely the failure mode the
   controls exist to catch, and it is worth spelling out here because it looks
   like a passing ledger if the controls are ever dropped. */
static bool run_case(const struct case_spec *spec, const char *server_bin,
                     const char *chain_pem, const char *key_pem,
                     const uint8_t *trust_anchor, size_t trust_anchor_len) {
  char port_path[256];
  snprintf(port_path, sizeof port_path,
           "test/.client_record_split.%ld.%s.port", (long)getpid(),
           spec->name);
  (void)unlink(port_path);

  pid_t server_pid = fork();
  if (server_pid < 0) {
    perror("fork");
    return false;
  }
  if (server_pid == 0) {
    int devnull = open("/dev/null", O_WRONLY);
    if (devnull >= 0) {
      (void)dup2(devnull, STDOUT_FILENO);
      (void)dup2(devnull, STDERR_FILENO);
      close(devnull);
    }
    execl(server_bin, server_bin, "0", chain_pem, key_pem, port_path,
          (char *)NULL);
    _exit(127);
  }

  uint16_t server_port = 0;
  for (int attempt = 0; attempt < 200 && server_port == 0; ++attempt) {
    FILE *f = fopen(port_path, "r");
    if (f != NULL) {
      long parsed = 0;
      if (fscanf(f, "%ld", &parsed) == 1 && parsed > 0 && parsed <= 65535) {
        server_port = (uint16_t)parsed;
      }
      fclose(f);
    }
    if (server_port == 0) {
      usleep(50000);
    }
  }
  if (server_port == 0) {
    fprintf(stderr, "%s: OpenSSL echo server did not report a port\n",
            spec->name);
    kill(server_pid, SIGTERM);
    (void)waitpid(server_pid, NULL, 0);
    (void)unlink(port_path);
    return false;
  }

  uint16_t proxy_port = 0;
  if (reserve_loopback_port(&proxy_port) != 0) {
    kill(server_pid, SIGTERM);
    (void)waitpid(server_pid, NULL, 0);
    (void)unlink(port_path);
    return false;
  }

  pid_t proxy_pid = fork();
  if (proxy_pid < 0) {
    perror("fork");
    kill(server_pid, SIGTERM);
    (void)waitpid(server_pid, NULL, 0);
    (void)unlink(port_path);
    return false;
  }
  if (proxy_pid == 0) {
    _exit(run_proxy(proxy_port, server_port, spec->framing) == 0 ? 0 : 1);
  }

  static const uint8_t ping[] = {'p', 'i', 'n', 'g'};
  uint8_t received[TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE] = {0};
  size_t received_len = 0;
  tls13_client_driver *driver = NULL;
  /* `_reporting`, not the plain `_connect`: a failed connect destroys the
     driver that carried the verified workflow status, so without this the
     ledger could not tell a handshake refusal from a TCP failure -- which is
     exactly the distinction the split cell rests on. */
  char connect_error[256] = {0};
  bool ok = tls13_client_driver_connect_reporting(
                &driver, "127.0.0.1", proxy_port, "localhost", trust_anchor,
                trust_anchor_len, 0u, connect_error,
                sizeof connect_error) == 0;
  if (!ok) {
    fprintf(stderr, "  %s: connect refused: %s\n", spec->name,
            connect_error[0] == '\0' ? "(no reason reported)" : connect_error);
  }
  if (ok) {
    ok = tls13_client_driver_send_application_data(driver, ping,
                                                   sizeof ping) == 0 &&
         tls13_client_driver_receive_application_data(
             driver, received, sizeof received, &received_len) == 0 &&
         received_len == sizeof ping &&
         memcmp(received, ping, sizeof ping) == 0;
    if (!ok) {
      fprintf(stderr, "  %s: established, then failed the echo: %s\n",
              spec->name, tls13_client_driver_last_error(driver));
    }
  }
  if (ok) {
    ok = tls13_client_driver_close(driver, true) == 0;
  }
  tls13_client_driver_free(driver);

  kill(proxy_pid, SIGTERM);
  (void)waitpid(proxy_pid, NULL, 0);
  kill(server_pid, SIGTERM);
  (void)waitpid(server_pid, NULL, 0);
  (void)unlink(port_path);
  return ok;
}

int main(int argc, char **argv) {
  if (argc != 5) {
    fprintf(stderr, "usage: %s ECHO_SERVER_BIN CHAIN_PEM KEY_PEM CA_PEM\n",
            argv[0]);
    return 1;
  }
  /* The proxy and server children are torn down with SIGTERM after every cell,
     and either may close on us mid-write; neither should kill the harness. */
  signal(SIGPIPE, SIG_IGN);

  uint8_t *trust_anchor = NULL;
  size_t trust_anchor_len = 0;
  if (read_file(argv[4], &trust_anchor, &trust_anchor_len) != 0) {
    return 1;
  }

  printf("Verified TLS 1.3 client: server->client framing matrix (%zu cells)\n",
         CASE_COUNT);
  printf("%-34s %-8s %-8s %s\n", "CASE", "EXPECT", "ACTUAL", "VERDICT");

  size_t mismatches = 0;
  for (size_t i = 0; i < CASE_COUNT; ++i) {
    const struct case_spec *spec = &k_cases[i];
    bool actual = run_case(spec, argv[1], argv[2], argv[3], trust_anchor,
                           trust_anchor_len);
    bool agrees = actual == spec->expect_ok;
    if (!agrees) {
      mismatches += 1;
    }
    printf("%-34s %-8s %-8s %s\n", spec->name,
           spec->expect_ok ? "ok" : "refused", actual ? "ok" : "refused",
           agrees ? "MATCH" : "*** MISMATCH ***");
    if (!agrees) {
      fprintf(stderr,
              "  %s: expected the client to %s this framing but it %s it.\n"
              "    recorded reason: %s\n",
              spec->name, spec->expect_ok ? "accept" : "refuse",
              actual ? "accepted" : "refused", spec->note);
      if (actual && !spec->expect_ok) {
        fprintf(stderr,
                "    A cell recorded as a gap now SUCCEEDS.  If that is the\n"
                "    intended effect of your change, flip this row to OK in\n"
                "    test/unit/test_client_record_split.c and update\n"
                "    docs/server-client-parity.md in the same commit.\n");
      }
      if (!actual && spec->expect_ok) {
        if (spec->framing == FRAMING_NORMAL ||
            spec->framing == FRAMING_TCP_DRIBBLE) {
          fprintf(stderr,
                  "    This is a CONTROL cell.  Its failure means the harness "
                  "or\n"
                  "    the proxy is broken; the split cells' verdicts cannot "
                  "be\n"
                  "    trusted until this one is green again.\n");
        } else {
          fprintf(stderr,
                  "    Cross-record CLEARTEXT reassembly regressed (G3).  "
                  "Check\n"
                  "    try_buffer_cleartext_handshake_record and\n"
                  "    try_deliver_reassembled_server_hello in\n"
                  "    src/impl/TLS13.Impl.Client.fst -- but only after the\n"
                  "    control cells above are green.\n");
        }
      }
    }
  }

  free(trust_anchor);
  if (mismatches == 0) {
    printf("client framing matrix: all %zu cells match the recorded ledger\n",
           CASE_COUNT);
    return 0;
  }
  fprintf(stderr,
          "client framing matrix: %zu of %zu cells disagree with the ledger\n",
          mismatches, CASE_COUNT);
  return 1;
}
