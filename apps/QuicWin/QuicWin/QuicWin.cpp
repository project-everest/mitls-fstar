#include <windows.h>
#include <stdio.h>
extern "C" {
    #include "..\..\..\libs\ffi\mitlsffi.h"
}

#include <memory.h>
#include <assert.h>
#include <sys/stat.h>
#include <errno.h>
#include <malloc.h>

void dump(unsigned char buffer[], size_t len) {
    int i;
    for (i = 0; i<len; i++) {
        printf("%02x", buffer[i]);
        if (i % 32 == 31 || i == len - 1) printf("\n");
    }
}

void dump(char buffer[], size_t len) {
    dump((unsigned char*)buffer, len);
}

char *quic_result_string(quic_result r) {
    static char *codes[10] = {
        "would_block", "error_local", "error_alert", "client_early_data",
        "client_complete", "client_complete_early_data", "server_accept",
        "server_accept_early_data", "server_complete", "other_error" };
    if (r < 9) return codes[r];
    return codes[9];
}

int main(int argc, char **argv) {
    char *errmsg;
    quic_result rc, rs;

    quic_config config;
    memset(&config, 0, sizeof(config));
    config.is_server = 1;
    config.host_name = "";
    config.qp.max_stream_data = 16000;
    config.qp.max_data = 32000;
    config.qp.max_stream_id = 16;
    config.qp.idle_timeout = 60;
    config.server_ticket.len = 0;
    config.certificate_chain_file = "server-ecdsa.crt";
    config.private_key_file = "server-ecdsa.key";
    config.ca_file = "CAFile.pem";
    config.cipher_suites = NULL; // Use defaults
    config.signature_algorithms = "ECDSA+SHA256";
    config.named_groups = "X25519";
    config.ticket_enc_alg = NULL;
    config.ticket_key = NULL;
    config.ticket_key_len = 0;
    config.enable_0rtt = 1;

    quic_state *server;
    quic_state *client;

    FFI_mitls_init();

    // server writer buffer (cumulative)
    size_t slen = 0;
    size_t smax = 8 * 1024; // too much; we use < 1KB
    char *s_buffer = (char*)malloc(smax);

    // client write buffer (cumulative)
    size_t clen = 0;
    size_t cmax = 8 * 1024; // too much; we use < 1KB
    char *c_buffer = (char*)malloc(cmax);

    // buffer for secrets and tickets
    quic_secret *qs = (quic_secret*)malloc(sizeof(quic_secret));
    quic_ticket *qt = (quic_ticket*)malloc(sizeof(quic_ticket));

    if (argc == 1) {
        // GENERIC HANDSHAKE TEST (NO 0RTT) 

        int client_complete = 0;
        int server_complete = 0;

        printf("server create\n");
        if (!FFI_mitls_quic_create(&server, &config, &errmsg)) {
            printf("quic_create server failed: %s\n", errmsg);
            return -1;
        }
        config.is_server = 0;
        config.host_name = "localhost";

        printf("client create\n");
        if (!FFI_mitls_quic_create(&client, &config, &errmsg)) {
            printf("quic_create client failed: %s\n", errmsg);
            return -1;
        }

        do {
            c_buffer += clen; // assuming miTLS never returns a larger clen
            cmax -= clen;
            clen = cmax;

            printf("client call clen=%4d slen=%4d\n", (int)clen, (int)slen);
            rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
            printf("client done clen=%4d slen=%4d status=%s\n", (int)clen, (int)slen, quic_result_string(rc));
            dump(c_buffer, clen);

            client_complete |= rc == TLS_client_complete || rc == TLS_client_complete_with_early_data;
            if (rc == TLS_error_other || rc == TLS_error_local || rc == TLS_error_alert) {
                printf("Stopping due to error code. Msg: %s\n", errmsg);
                break;
            }

            s_buffer += slen; // assuming miTLS never returns a larger clen
            smax -= slen;
            slen = smax;

            /* clen -= 12; // simulating fragmentation */
            /* printf("server call clen=%4d slen=%4d\n", clen, slen); */
            /* rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg); */
            /* printf("server done clen=%4d slen=%4d rc=%d\n", clen, slen, rc); */
            /* clen += 12; */

            printf("server call clen=%4d slen=%4d\n", (int)clen, (int)slen);
            rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
            printf("sender done clen=%4d slen=%4d status=%s\n", (int)clen, (int)slen, quic_result_string(rs));
            dump(s_buffer, slen);

            server_complete |= rs == TLS_server_complete;
            if (rs == TLS_error_other || rs == TLS_error_local || rs == TLS_error_alert) {
                printf("Stopping due to error code. Msg: %s\n", errmsg);
                break;
            }

        } while (!client_complete || !server_complete);

        memset(qs, 0, sizeof(quic_secret));
        FFI_mitls_quic_get_exporter(server, 0, qs, &errmsg);
        printf("   === Server exporter secret ===\n");
        dump(qs->secret, 64);
        FFI_mitls_quic_get_exporter(client, 0, qs, &errmsg);
        printf("   === Client exporter secret ===\n");
        dump(qs->secret, 64);
        printf("   ==============================\n");
    }

    if (argc == 2) {
        // HANDSHAKE WALKTHROUGH; 0RTT then 1RTT

        printf("\n     INITIAL ECDHE HANDSHAKE (NO EARLY SECRET)\n\n");

        printf("server create\n");
        if (!FFI_mitls_quic_create(&server, &config, &errmsg)) {
            printf("quic_create server failed: %s\n", errmsg);
            return -1;
        }
        config.is_server = 0;
        config.host_name = "localhost";

        printf("client create\n");
        if (!FFI_mitls_quic_create(&client, &config, &errmsg)) {
            printf("quic_create client failed: %s\n", errmsg);
            return -1;
        }

        c_buffer += clen; cmax -= clen; clen = cmax;
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
        assert(rc == TLS_would_block);
        printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), (int)clen, (int)slen);
        printf("ClientHello[%4d] ---->\n\n", (int)clen);

        s_buffer += slen; smax -= slen; slen = smax;
        rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
        assert(rs == TLS_server_accept);
        FFI_mitls_quic_get_exporter(server, 0, qs, &errmsg);
        printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), (int)clen, (int)slen);
        printf("                        secret="); dump(qs->secret, 32);
        printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4d]\n\n", (int)slen);

        c_buffer += clen; cmax -= clen; clen = cmax;
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
        assert(rc == TLS_client_complete);
        FFI_mitls_quic_get_exporter(client, 0, qs, &errmsg);
        printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), (int)clen, (int)slen);
        printf("secret="); dump(qs->secret, 32);
        printf("(Finished) [%4d] ---->\n\n", (int)clen);

        s_buffer += slen; smax -= slen; slen = smax;
        rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
        assert(rs == TLS_server_complete);
        printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), (int)clen, (int)slen);

        // NB we must call the server again to get a ticket
        c_buffer += clen; cmax -= clen; clen = 0;
        s_buffer += slen; smax -= slen; slen = smax;
        rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
        assert(rs == TLS_would_block);
        printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), (int)clen, (int)slen);
        printf("                  <---- {Ticket}[%4d]\n\n", (int)slen);

        clen = cmax;
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
        assert(rc == TLS_would_block);
        printf("client returns clen=%d slen=%d status=%s\n", (int)clen, (int)slen, quic_result_string(rc));

        if (FFI_mitls_quic_get_ticket(client, qt, &errmsg)) {
            printf("new ticket: \n");
            dump(qt->ticket, qt->len);
        } else printf("Failed to get ticket: %s\n", errmsg);

        printf("\n     TICKET-BASED RESUMPTION\n\n");

        FFI_mitls_quic_free(server);
        FFI_mitls_quic_free(client);

        config.is_server = 1;
        config.host_name = "";
        printf("server create\n");
        if (!FFI_mitls_quic_create(&server, &config, &errmsg)) {
            printf("quic_create server failed: %s\n", errmsg);
            return -1;
        }
        config.is_server = 0;
        config.host_name = "localhost";
        config.server_ticket = *qt;

        printf("client create\n");
        if (!FFI_mitls_quic_create(&client, &config, &errmsg)) {
            printf("quic_create client failed: %s\n", errmsg);
            return -1;
        }

        s_buffer += slen; smax -= slen; slen = 0;
        c_buffer += clen; cmax -= clen; clen = cmax;
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
        printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), (int)clen, (int)slen);
        assert(rc == TLS_client_early);
        FFI_mitls_quic_get_exporter(client, 1, qs, &errmsg);
        printf("early secret="); dump(qs->secret, 32);
        printf("ClientHello[%4d] ---->\n\n", (int)clen);

        s_buffer += slen; smax -= slen; slen = smax;
        rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
        assert(rs == TLS_server_accept_with_early_data);
        printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), (int)clen, (int)slen);
        FFI_mitls_quic_get_exporter(server, 1, qs, &errmsg);
        printf("                        early secret="); dump(qs->secret, 32);
        FFI_mitls_quic_get_exporter(server, 0, qs, &errmsg);
        printf("                        secret="); dump(qs->secret, 32);
        printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4d]\n\n", (int)slen);

        c_buffer += clen; cmax -= clen; clen = cmax;
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
        assert(rc == TLS_client_complete_with_early_data);
        FFI_mitls_quic_get_exporter(client, 0, qs, &errmsg);
        printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), (int)clen, (int)slen);
        printf("secret="); dump(qs->secret, 32);
        printf("(Finished) [%4d] ---->\n\n", (int)clen);

        s_buffer += slen; smax -= slen; slen = smax;
        rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
        assert(rs == TLS_server_complete);
        printf("                        server returns clen=%d slen=%d status=%s\n", (int)clen, (int)slen, quic_result_string(rs));

        // NB we must call the server again to get a ticket
        c_buffer += clen; cmax -= clen; clen = 0;
        s_buffer += slen; smax -= slen; slen = smax;
        rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
        assert(rs == TLS_would_block);
        printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), (int)clen, (int)slen);
        printf("                  <---- {Ticket}[%4d]\n\n", (int)slen);

        clen = cmax;
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
        assert(rc == TLS_would_block);
        printf("client returns clen=%d slen=%d status=%s\n", (int)clen, (int)slen, quic_result_string(rc));

        if (FFI_mitls_quic_get_ticket(client, qt, &errmsg)) {
            printf("new ticket:\n");
            dump(qt->ticket, qt->len);
        } else printf("Failed to get ticket: %s\n", errmsg);

    }

    FFI_mitls_quic_free(server);
    FFI_mitls_quic_free(client);

    printf("Ok\n");
    return 0;
}
