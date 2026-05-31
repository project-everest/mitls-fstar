/*
 * TLS 1.3 Client - Main End-to-End Test
 * 
 * This is the main test demonstrating the verified TLS 1.3 client.
 * It connects to a TLS 1.3 server, performs a handshake, sends application
 * data, receives the echo response, and closes the connection.
 *
 * Usage: ./test/tls_client <hostname> <port> <ca_cert_pem>
 * Example: ./test/tls_client localhost 4433 test/certs/ca.pem
 */

#include "tls13_connection_backend.h"
#include "TLS13_Record.h"
#include "TLS13_Connection.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_PAYLOAD_SIZE 40000

static void print_usage(const char *progname) {
    fprintf(stderr, "Usage: %s <hostname> <port> <ca_cert_pem>\n", progname);
    fprintf(stderr, "\n");
    fprintf(stderr, "Example:\n");
    fprintf(stderr, "  %s localhost 4433 test/certs/ca.pem\n", progname);
    fprintf(stderr, "\n");
    fprintf(stderr, "This client:\n");
    fprintf(stderr, "  1. Connects to the TLS 1.3 server at hostname:port\n");
    fprintf(stderr, "  2. Performs TLS 1.3 handshake (verifies server certificate)\n");
    fprintf(stderr, "  3. Sends application data and receives response\n");
    fprintf(stderr, "  4. Demonstrates the verified TLS 1.3 implementation\n");
}

static int parse_port(const char *port_str) {
    char *end = NULL;
    long port = strtol(port_str, &end, 10);
    if (*port_str == '\0' || *end != '\0' || port <= 0 || port > 65535) {
        return -1;
    }
    return (int)port;
}

static void fill_test_payload(uint8_t *payload, size_t len) {
    static const char *pattern = "Verified TLS 1.3 Client Test Payload\n";
    size_t pattern_len = strlen(pattern);
    for (size_t i = 0; i < len; i++) {
        payload[i] = (uint8_t)pattern[i % pattern_len];
    }
}

int main(int argc, char **argv) {
    if (argc != 4) {
        print_usage(argv[0]);
        return 1;
    }

    const char *hostname = argv[1];
    const char *port_str = argv[2];
    const char *ca_pem = argv[3];

    int port = parse_port(port_str);
    if (port < 0) {
        fprintf(stderr, "Invalid port: %s\n", port_str);
        print_usage(argv[0]);
        return 1;
    }

    printf("═══════════════════════════════════════════════════════════════\n");
    printf(" Verified TLS 1.3 Client - End-to-End Test\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Server:      %s:%d\n", hostname, port);
    printf("CA cert:     %s\n", ca_pem);
    printf("\n");

    // Step 1: Create connection
    printf("Step 1: Creating TLS 1.3 connection...\n");
    struct TLS13_Connection_Backend_config_s config = {
        .port = (uint16_t)port,
        .ca_pem_path = ca_pem,
    };
    connection c = client_new((uint8_t *)hostname, strlen(hostname), &config);
    if (c.backend == NULL) {
        fprintf(stderr, "  FAILED: client_new returned NULL\n");
        return 1;
    }
    printf("  ✓ Connection created\n\n");

    // Step 2: Perform handshake
    printf("Step 2: Performing TLS 1.3 handshake...\n");
    printf("  Connecting to %s:%d...\n", hostname, port);
    if (!client_connect(c, NULL)) {
        fprintf(stderr, "  FAILED: TLS 1.3 handshake failed\n");
        client_free(c);
        return 1;
    }
    printf("  ✓ TLS 1.3 handshake complete\n");
    printf("  ✓ Server certificate verified\n");
    printf("  ✓ Application keys installed\n\n");

    // Step 3: Send application data
    printf("Step 3: Testing application data transfer...\n");
    const char *test_message = "Hello from verified TLS 1.3 client!";
    size_t msg_len = strlen(test_message);
    
    uint8_t *send_buf = malloc(msg_len);
    if (!send_buf) {
        fprintf(stderr, "  FAILED: malloc failed\n");
        client_free(c);
        return 1;
    }
    memcpy(send_buf, test_message, msg_len);

    printf("  Sending %zu bytes...\n", msg_len);
    size_t written = client_write(c, NULL, send_buf, msg_len);
    if (written != msg_len) {
        fprintf(stderr, "  FAILED: client_write returned %zu (expected %zu)\n", written, msg_len);
        free(send_buf);
        client_free(c);
        return 1;
    }
    printf("  ✓ Sent %zu bytes\n", written);
    free(send_buf);

    // Step 4: Receive response
    printf("  Receiving response...\n");
    uint8_t *recv_buf = malloc(msg_len);
    if (!recv_buf) {
        fprintf(stderr, "  FAILED: malloc failed\n");
        client_free(c);
        return 1;
    }
    memset(recv_buf, 0, msg_len);
    
    size_t read_total = 0;
    while (read_total < msg_len) {
        size_t to_read = msg_len - read_total;
        size_t n = client_read(c, NULL, recv_buf + read_total, to_read);
        if (n == 0) {
            fprintf(stderr, "  FAILED: client_read returned 0\n");
            free(recv_buf);
            client_free(c);
            return 1;
        }
        read_total += n;
    }
    printf("  ✓ Received %zu bytes\n", read_total);

    // Verify echo
    if (memcmp(test_message, recv_buf, msg_len) != 0) {
        fprintf(stderr, "  FAILED: Echo mismatch\n");
        free(recv_buf);
        client_free(c);
        return 1;
    }
    printf("  ✓ Echo verified\n");
    free(recv_buf);

    printf("\n");

    // Step 5: Free resources
    printf("Step 4: Freeing resources...\n");
    client_free(c);
    printf("  ✓ Resources freed\n\n");

    printf("═══════════════════════════════════════════════════════════════\n");
    printf(" ✓ ALL TESTS PASSED\n");
    printf("═══════════════════════════════════════════════════════════════\n");

    return 0;
}
