/*
 * Test for the bundled TLS13.c/TLS13.h extraction
 * This is a minimal sanity check that the bundle compiles and links
 */

#include "TLS13.h"
#include "tls13_connection_backend.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    
    printf("Bundled TLS13 extraction test\n");
    
    /* Create a simple config */
    struct TLS13_Connection_Backend_config_s cfg_data = {
        .port = 443,
        .ca_pem_path = "test/certs/ca.pem"
    };
    TLS13_Connection_Backend_config cfg = &cfg_data;
    
    /* Create and free a connection */
    uint8_t hostname[] = "localhost";
    connection c = client_new(hostname, sizeof(hostname) - 1, cfg);
    if (c.live == NULL) {
        fprintf(stderr, "Failed to create connection\n");
        return 1;
    }
    
    client_free(c);
    
    printf("Bundle test passed\n");
    return 0;
}
