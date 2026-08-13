/* ATLAS client <-> ATLAS server loopback interop.
 *
 * Every other interop test in this tree pairs one verified endpoint with
 * OpenSSL, and each of those pins OpenSSL to a hand-written configuration.
 * That leaves the one pairing nobody checks: the verified client talking to
 * the verified server.  It is the pairing that regresses first, because the
 * client's offer is the thing that moves -- the top-100 interop push widened
 * the ClientHello to two cipher suites (TLS_CHACHA20_POLY1305_SHA256,
 * TLS_AES_128_GCM_SHA256), two key shares (X25519, secp256r1) and two
 * signature schemes, while the server's selection stayed at one of each.
 *
 * This test is therefore the parity gate: the verified server must accept
 * whatever the verified client currently offers, complete a 1-RTT handshake,
 * and survive application data and KeyUpdates in both directions.  If someone
 * widens the client's offer past what the server can select -- a suite the
 * server does not implement, a key share the server's ClientHello parser
 * rejects, a ClientHello that no longer fits one record -- this test fails
 * even though every OpenSSL-paired test stays green, because those tests
 * describe OpenSSL's offer, not ours.
 *
 * The exchange is deliberately not a single round trip.  Both endpoints
 * rekey, so the server's write path (rotating its own application key), the
 * server's read path (rotating on a peer KeyUpdate), the mandated
 * update_not_requested reply, and the same three on the client are all
 * driven at several epochs.  A one-shot echo would pass with a traffic
 * secret that never iterates.
 */

#include "tls13_client_driver.h"
#include "tls13_server_driver.h"

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

/* Application records exchanged in each direction. */
#define ECHO_ROUNDS 8u

/* Rounds on which each side initiates a KeyUpdate.  Both sides rekey and both
   forms (update_requested / update_not_requested) are used, so the mandated
   reply path is driven on both endpoints. */
#define CLIENT_KEY_UPDATE_ROUNDS 4u
#define SERVER_KEY_UPDATE_ROUNDS 4u

static const uint8_t k_ping[] = {'p', 'i', 'n', 'g'};

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return 1;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    perror("fseek");
    fclose(f);
    return 1;
  }
  long len = ftell(f);
  if (len < 0) {
    perror("ftell");
    fclose(f);
    return 1;
  }
  rewind(f);
  uint8_t *buf = calloc((size_t)len == 0 ? 1u : (size_t)len, sizeof(uint8_t));
  if (buf == NULL) {
    fclose(f);
    return 1;
  }
  if (fread(buf, 1u, (size_t)len, f) != (size_t)len) {
    perror("fread");
    free(buf);
    fclose(f);
    return 1;
  }
  fclose(f);
  *out = buf;
  *out_len = (size_t)len;
  return 0;
}

/* Bind an ephemeral loopback port and release it again, so the two processes
   can agree on a port without a rendezvous file.  Same technique as the
   OpenSSL-paired server test. */
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

static int run_atlas_server(
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key,
    size_t private_key_len) {
  alarm(30);
  tls13_server_driver *server = NULL;
  uint8_t received[TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE] = {0};
  int rc = 1;

  if (tls13_server_driver_accept(
          &server,
          "127.0.0.1",
          port,
          certificate_chain,
          certificate_chain_len,
          private_key,
          private_key_len) != 0) {
    fprintf(stderr, "atlas loopback: verified server failed during accept\n");
    goto done;
  }

  for (unsigned round = 0; round < ECHO_ROUNDS; ++round) {
    size_t received_len = 0;
    if (tls13_server_driver_receive_application_data(
            server, received, sizeof received, &received_len) != 0 ||
        received_len != sizeof k_ping ||
        memcmp(received, k_ping, sizeof k_ping) != 0) {
      fprintf(stderr, "atlas loopback: server receive failed in round %u\n", round);
      goto failed;
    }
    if (tls13_server_driver_send_application_data(server, received, received_len) != 0) {
      fprintf(stderr, "atlas loopback: server send failed in round %u\n", round);
      goto failed;
    }
    /* Server-initiated rekey.  update_not_requested: the client already
       requests updates of its own below, and an extra request here would
       only be answered after the client's next write, which is not the
       shape under test. */
    if (round < SERVER_KEY_UPDATE_ROUNDS &&
        tls13_server_driver_send_key_update(server, false) != 0) {
      fprintf(stderr, "atlas loopback: server key update failed in round %u\n", round);
      goto failed;
    }
  }

  if (tls13_server_driver_close(server, true) != 0) {
    fprintf(stderr, "atlas loopback: server close failed\n");
    goto failed;
  }
  rc = 0;
  goto done;

failed:
  fprintf(stderr, "atlas loopback: verified server: %s\n",
          tls13_server_driver_last_error(server));

done:
  tls13_server_driver_free(server);
  return rc;
}

static int run_atlas_client(
    uint16_t port,
    const uint8_t *trust_anchor,
    size_t trust_anchor_len) {
  alarm(30);
  tls13_client_driver *client = NULL;
  uint8_t received[TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE] = {0};
  char connect_error[256] = {0};
  int rc = 1;

  /* The verified client driver owns its socket: it binds, connects and
     handshakes inside one call, so there is no connected fd to hand it and no
     way to wait for the peer's listen() from out here.  Retry the whole
     connect for a bounded window instead.
     Retrying cannot mask a handshake failure: the server serves exactly one
     connection and then exits, so a genuine rejection leaves nothing listening
     and the next attempt fails immediately -- and the server's own non-zero
     exit status fails the test regardless of what the client concludes. */
  int connect_rc = 1;
  for (unsigned attempt = 0; attempt < 100u; ++attempt) {
    connect_rc = tls13_client_driver_connect_reporting(
        &client, "127.0.0.1", port, "localhost", trust_anchor, trust_anchor_len,
        0u, connect_error, sizeof connect_error);
    if (connect_rc == 0) {
      break;
    }
    usleep(20000);
  }
  if (connect_rc != 0) {
    fprintf(stderr, "atlas loopback: verified client failed to connect: %s\n",
            connect_error[0] == '\0' ? "(no reason reported)" : connect_error);
    return 1;
  }

  for (unsigned round = 0; round < ECHO_ROUNDS; ++round) {
    /* Client-initiated rekey, with update_requested so the verified server
       owes a mandated reply, which in turn rotates the client's read key. */
    if (round < CLIENT_KEY_UPDATE_ROUNDS &&
        tls13_client_driver_send_key_update(client, true) != 0) {
      fprintf(stderr, "atlas loopback: client key update failed in round %u\n", round);
      goto failed;
    }
    if (tls13_client_driver_send_application_data(client, k_ping, sizeof k_ping) != 0) {
      fprintf(stderr, "atlas loopback: client send failed in round %u\n", round);
      goto failed;
    }
    size_t received_len = 0;
    memset(received, 0, sizeof received);
    if (tls13_client_driver_receive_application_data(
            client, received, sizeof received, &received_len) != 0 ||
        received_len != sizeof k_ping ||
        memcmp(received, k_ping, sizeof k_ping) != 0) {
      fprintf(stderr, "atlas loopback: client receive failed in round %u\n", round);
      goto failed;
    }
  }

  if (tls13_client_driver_close(client, true) != 0) {
    fprintf(stderr, "atlas loopback: client close failed\n");
    goto failed;
  }
  rc = 0;
  goto done;

failed:
  fprintf(stderr, "atlas loopback: verified client: %s\n",
          tls13_client_driver_last_error(client));

done:
  tls13_client_driver_free(client);
  return rc;
}

int main(void) {
  uint8_t *certificate_chain = NULL;
  uint8_t *private_key = NULL;
  uint8_t *trust_anchor = NULL;
  size_t certificate_chain_len = 0;
  size_t private_key_len = 0;
  size_t trust_anchor_len = 0;
  uint16_t port = 0;
  int rc = 1;

  if (read_file("test/certs/leaf.der", &certificate_chain, &certificate_chain_len) != 0 ||
      read_file("test/certs/leaf.key", &private_key, &private_key_len) != 0 ||
      read_file("test/certs/ca.pem", &trust_anchor, &trust_anchor_len) != 0 ||
      reserve_loopback_port(&port) != 0) {
    goto done;
  }

  pid_t child = fork();
  if (child < 0) {
    perror("fork");
    goto done;
  }
  if (child == 0) {
    int child_rc = run_atlas_server(
        port, certificate_chain, certificate_chain_len, private_key, private_key_len);
    _exit(child_rc == 0 ? 0 : 1);
  }

  int client_rc = run_atlas_client(port, trust_anchor, trust_anchor_len);
  if (client_rc != 0) {
    /* Do not wait out the server's alarm: if the client gave up, the server is
       blocked on a peer that will never speak again. */
    kill(child, SIGKILL);
  }
  int status = 0;
  if (waitpid(child, &status, 0) < 0) {
    perror("waitpid");
    goto done;
  }
  if (client_rc == 0 && WIFEXITED(status) && WEXITSTATUS(status) == 0) {
    printf("ATLAS client <-> ATLAS server loopback test passed "
           "(%u application records, %u client + %u server KeyUpdates)\n",
           ECHO_ROUNDS, CLIENT_KEY_UPDATE_ROUNDS, SERVER_KEY_UPDATE_ROUNDS);
    rc = 0;
  } else {
    fprintf(stderr, "ATLAS client <-> ATLAS server loopback test failed\n");
  }

done:
  free(certificate_chain);
  free(private_key);
  free(trust_anchor);
  return rc;
}
