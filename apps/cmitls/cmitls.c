#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#if _WIN32 // Windows 32-bit or 64-bit... mingw
#include <winsock2.h>
typedef int socklen_t;
#else
#include <unistd.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <netdb.h>
#include <errno.h>
#include <alloca.h>
#define _alloca alloca
typedef int SOCKET;
#define SOCKET_ERROR (-1)
#define WSAGetLastError() (errno)
#define closesocket(fd) close(fd)
#endif
#include <mitlsffi.h>
#include <mipki.h>

const char *option_hostname;
int option_port;

#define OPTION_LIST \
    STRING_OPTION("-v", version, "sets maximum protocol version to <1.0 | 1.1 | 1.2 | 1.3> (default: 1.3)") \
    STRING_OPTION("-mv", minversion, "sets minimum protocol version to <1.0 | 1.1 | 1.2 | 1.3> (default: 1.2)") \
    BOOL_OPTION("-s", isserver, "run as server instead of client") \
    BOOL_OPTION("-0rtt", 0rtt, "enable early data (server support and client offer)") \
    BOOL_OPTION("-hrr", hrr, "always send a hello retry as a server") \
    STRING_OPTION("-psk", psk, "L:K add an entry in the PSK database at label L with key K (in hex), associtated with the fist current -cipher") \
    STRING_OPTION("-ticket", ticket, "T:K add ticket T in the PSK database with RMS K (in hex), associated with the first current -cipher") \
    STRING_OPTION("-offerpsk", offerpsk, "offer the given PSK identifier(s) (must be loaded first with --psk). Client only.") \
    BOOL_OPTION("-verify", verify, "enforce peer certificate validation") \
    BOOL_OPTION("-noems", noems, "disable extended master secret in TLS <= 1.2 (client only)") \
    STRING_OPTION("-ciphers", ciphers, "colon-separated list of cipher suites; see above for valid values") \
    STRING_OPTION("-sigalgs", sigalgs, "colon-separated list of signature algorithms; see above for valid values") \
    STRING_OPTION("-alpn", alpn, "colon-separated list of application-level protocols") \
    BOOL_OPTION("-quic", quic, "test QUIC API, using the QuicTransportParameters extension") \
    BOOL_OPTION("-reconnect", reconnect, "reconnect at the end of the session, using received ticket (client only)") \
    STRING_OPTION("-groups", groups, "colon-separated list of named groups; see above for valid values") \
    STRING_OPTION("-cert", cert, "PEM file containing certificate chain to send") \
    STRING_OPTION("-key", key, "PEM file containing private key of endpoint certificate in chain") \
    STRING_OPTION("-CAFile", cafile, "set openssl root cert file to <path>")

// Declare global variables representing the options
#define STRING_OPTION(n, var, help) const char *option_##var;
#define BOOL_OPTION(n, var, help)   int option_##var;
OPTION_LIST
#undef STRING_OPTION
#undef BOOL_OPTION

// Fill in a datastructure describing the options
#define STRING_OPTION(n, var, help) { n, &option_##var, NULL, help },
#define BOOL_OPTION(n, var, help)   { n, NULL, &option_##var, help },
struct {
    const char *OptionName;     // name of the option switch
    const char **String;        // place to store the option argument string, or NULL if no argument follows
    int *Boolean;               // if String==NULL, then this is the place to store a boolean '1'
    const char *HelpText;       // help text for the option
} Options[] = {
    OPTION_LIST
    {}
};
#undef STRING_OPTION
#undef BOOL_OPTION

typedef struct {
  SOCKET sockfd;
} callback_context;

// Print the usage text
void PrintUsage(void)
{
    size_t i=0;

    printf("Usage:  cmitls.exe [options] hostname port\n");
    for (i=0; Options[i].OptionName; ++i) {
        printf("  %-10s %s\n", Options[i].OptionName, Options[i].HelpText);
    }
}

const char *hostname_arg;
const char *port_arg;

// Parse one argument, prefixed by "-"
//  Name - the argument name, including the "-"
//  ArgsRemaining - the number of elements in argvRemaining
//  argvRemaining - the remaining arguments
//
// Returns -1 for failure, or 1 or 2, to report the number
// of arguments consumed
int ParseArg(const char *Name, int ArgsRemaining, char **argvRemaining)
{
    size_t i=0;

    for (i=0; Options[i].OptionName; ++i) {
        if (strcmp(Options[i].OptionName, Name) == 0) {
            if (Options[i].String) {
                if (ArgsRemaining) {
                    *(Options[i].String) = argvRemaining[0];
                } else {
                    return -1;
                }
                return 2;
            } else {
                *(Options[i].Boolean) = 1;
                return 1;
            }
        }
    }
    printf("Unknown option: %s\n", Name);
    return -1; // Unknown option
}

// Parse the command line arguments
// Returns -1 for failure, 0 for success
int ParseArgs(int argc, char **argv)
{
    int i = 1;
    int result;

    while (i < argc) {
        if (argv[i][0] == '-') {
            result = ParseArg(argv[i], argc-i-1, &argv[i+1]);
            if (result == -1) {
                return -1;
            }
            i += result;
        } else if (hostname_arg == NULL) {
            hostname_arg = argv[i++];
        } else if (port_arg == NULL) {
            port_arg = argv[i++];
        } else {
            printf("Unknown argument: %s\n", argv[i]);
            return -1;
        }
    }

    if (hostname_arg) {
        option_hostname = hostname_arg;
    } else {
        option_hostname = (option_isserver) ? "0.0.0.0" : "localhost";
    }
    if (port_arg) {
        option_port = atoi(port_arg);
    } else {
        option_port = 443;
    }
    return 0;
}

void dump(const char *buffer, size_t len)
{
  int i;
  for(i=0; i<len; i++) {
    printf("%02x",(unsigned char)buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

const char* pvname(mitls_version pv)
{
  switch(pv)
  {
    case TLS_SSL3: return "SSL 3.0";
    case TLS_1p0: return "TLS 1.0";
    case TLS_1p1: return "TLS 1.1";
    case TLS_1p2: return "TLS 1.2";
    case TLS_1p3: return "TLS 1.3";
  }
  return "(unknown)";
}

mitls_nego_action nego_callback(void *cb_state, mitls_version ver,
  const unsigned char *cexts, size_t cexts_len, mitls_extension **custom_exts,
  size_t *custom_exts_len, unsigned char **cookie, size_t *cookie_len)
{
  printf(" @@@@ Nego callback for %s @@@@\n", pvname(ver));
  printf("Offered extensions:\n");
  dump(cexts, cexts_len);

  unsigned char *qtp = NULL;
  size_t qtp_len;
  if(FFI_mitls_find_custom_extension(0, cexts, cexts_len, (uint16_t)0x1A, &qtp, &qtp_len))
  {
    printf("Transport parameters offered:\n");
    dump(qtp, qtp_len);
  }

  if(option_quic)
  {
    *custom_exts = malloc(sizeof(mitls_extension));
    *custom_exts_len = 1;
    custom_exts[0]->ext_type = (uint16_t)0x1a;
    custom_exts[0]->ext_data = "\x00\x01\x02";
    custom_exts[0]->ext_data_len = 3;
    printf("Adding server transport parameters:\n");
    dump(custom_exts[0]->ext_data, custom_exts[0]->ext_data_len);
  }
  else {
    *custom_exts_len = 0;
    *custom_exts = NULL;
  }

  if(*cookie != NULL) {
    if(*cookie_len) {
      printf("Stateless cookie found, application contents:\n");
      dump(*cookie, *cookie_len);
    } else printf("Empty application contents (stateful HRR).\n");
  } else {
    printf("No application cookie (fist connection).\n");
    // only used when TLS_nego_retry is returned, but it's safe to set anyway
    *cookie = "Hello World";
    *cookie_len = 11;
    if(option_hrr) return TLS_nego_retry;
  }

  printf(" @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n");
  return TLS_nego_accept;
}

void* certificate_select(void *cbs, const unsigned char *sni, size_t sni_len, const mitls_signature_scheme *sigalgs, size_t sigalgs_len, mitls_signature_scheme *selected)
{
  mipki_state *st = (mipki_state*)cbs;
  mipki_chain r = mipki_select_certificate(st, sni, sni_len, sigalgs, sigalgs_len, selected);
  return (void*)r;
}

size_t certificate_format(void *cbs, const void *cert_ptr, unsigned char *buffer)
{
  mipki_state *st = (mipki_state*)cbs;
  mipki_chain chain = (mipki_chain)cert_ptr;
  return mipki_format_chain(st, cert_ptr, buffer, MAX_CHAIN_LEN);
}

size_t certificate_sign(void *cbs, const void *cert_ptr, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, unsigned char *sig)
{
  mipki_state *st = (mipki_state*)cbs;
  size_t ret = MAX_SIGNATURE_LEN;

  printf("======== TO BE SIGNED <%04x>: (%d octets) ========\n", sigalg, (int)tbs_len);
  dump(tbs, tbs_len);
  printf("===================================================\n");

  if(mipki_sign_verify(st, cert_ptr, sigalg, tbs, tbs_len, sig, &ret, MIPKI_SIGN))
    return ret;

  return 0;
}

int certificate_verify(void *cbs, const unsigned char* chain_bytes, size_t chain_len, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, const unsigned char *sig, size_t sig_len)
{
  mipki_state *st = (mipki_state*)cbs;
  mipki_chain chain = mipki_parse_chain(st, chain_bytes, chain_len);

  if(chain == NULL)
  {
    printf("ERROR: failed to parse certificate chain");
    return 0;
  }

  // We don't validate hostname, but could with the callback state
  if(!mipki_validate_chain(st, chain, option_hostname))
  {
    printf("WARNING: chain validation failed, ignoring.\n");
    // return 0;
  }

  size_t slen = sig_len;
  int r = mipki_sign_verify(st, chain, sigalg, tbs, tbs_len, (char*)sig, &slen, MIPKI_VERIFY);
  mipki_free_chain(st, chain);
  return r;
}

int ConfigureQuic(quic_state **pstate)
{
    int erridx, r;
    quic_state *state;
    quic_config quic_cfg;

    // Server PKI configuration: one ECDSA certificate
    mipki_config_entry pki_config[1] = {
      {
        .cert_file = option_cert ? option_cert : "../../data/server-ecdsa.crt",
        .key_file = option_key ? option_key : "../../data/server-ecdsa.key",
        .is_universal = 1 // ignore SNI
      }
    };

    mipki_state *pki = mipki_init(pki_config, 1, NULL, &erridx);
    mitls_cert_cb cert_callbacks =
      {
        .select = certificate_select,
        .format = certificate_format,
        .sign = certificate_sign,
        .verify = certificate_verify
      };

    if(!pki)
    {
      printf("Failed to initialize PKI library: errid=%d\n", erridx);
      return 1;
    }

    if(!mipki_add_root_file_or_path(pki, option_cafile ? option_cafile : "../../data/CAFile.pem"))
    {
      printf("Failed to add CAFile\n");
      return 1;
    }

    *pstate = NULL;
    if (!option_quic) {
        printf("Call Configure() instead of ConfigureQuic(), for TLS connections.\n");
        return 4;
    }

    mitls_extension client_qtp[1] = {
      { // QUIC transport parameters (client)
        .ext_type = (uint16_t)0x1A,
        .ext_data = "\xff\xff\x00\x05\x0a\x0b\x0c\x0d\x0e\x00",
        .ext_data_len = 9
      }
    };

    memset(&quic_cfg, 0, sizeof(quic_cfg));
    quic_cfg.is_server = (option_isserver) ? 1 : 0;
    quic_cfg.cipher_suites = option_ciphers;
    quic_cfg.cert_callbacks = &cert_callbacks;
    quic_cfg.nego_callback = &nego_callback;
    quic_cfg.signature_algorithms = option_sigalgs;
    quic_cfg.named_groups = option_groups;
    quic_cfg.enable_0rtt = (option_0rtt) ? 1 : 0;
    quic_cfg.exts = client_qtp;
    quic_cfg.exts_count = 1;

    if (option_isserver) {
        quic_cfg.ticket_enc_alg = NULL;
        quic_cfg.ticket_key = NULL;
        quic_cfg.ticket_key_len = 0;
    } else { // client
        quic_cfg.host_name = option_hostname;
    }

    r = FFI_mitls_quic_create(&state, &quic_cfg);
    if (r == 0) {
        printf("FFI_mitls_quic_create() failed.\n");
        return 2;
    }
    *pstate = state;
    return 0;
}

int Configure(mitls_state **pstate)
{
    char *out_msg;
    mitls_state *state;
    int r, erridx;

    *pstate = NULL;

    // Server PKI configuration: one ECDSA certificate
    mipki_config_entry pki_config[1] = {
      {
        .cert_file = option_cert ? option_cert : "../../data/server-ecdsa.crt",
        .key_file = option_key ? option_key : "../../data/server-ecdsa.key",
        .is_universal = 1 // ignore SNI
      }
    };

    mipki_state *pki = mipki_init(pki_config, 1, NULL, &erridx);
    mitls_cert_cb cert_callbacks =
      {
        .select = certificate_select,
        .format = certificate_format,
        .sign = certificate_sign,
        .verify = certificate_verify
      };

    if(!mipki_add_root_file_or_path(pki, option_cafile ? option_cafile : "../../data/CAFile.pem")) {
      printf("Failed to set CAFile\n");
      return 1;
    }

    if (option_quic) {
        printf("Call ConfigureQuic() instead of Configure(), for QUIC connections.\n");
        return 4;
    }

    r = FFI_mitls_configure(&state, option_version, option_hostname);
    if(r) r = FFI_mitls_configure_cert_callbacks(state, pki, &cert_callbacks);

    if (r == 0) {
        printf("FFI_mitls_configure(%s,%s) failed.\n", option_version, option_hostname);
        return 2;
    }

    if (option_ciphers) {
        r = FFI_mitls_configure_cipher_suites(state, option_ciphers);
        if (r == 0) {
            printf("FFI_mitls_configure_cipher_suites(%s) failed.\n", option_ciphers);
            return 2;
        }
    }
    if (option_sigalgs) {
        r = FFI_mitls_configure_signature_algorithms(state, option_sigalgs);
        if (r == 0) {
            printf("FFI_mitls_configure_signature_algorithms(%s) failed.\n", option_sigalgs);
            return 2;
        }
    }
    if (option_groups) {
        r = FFI_mitls_configure_named_groups(state, option_groups);
        if (r == 0) {
            printf("FFI_mitls_configure_named_groups(%s) failed.\n", option_groups);
            return 2;
        }
    }

    if (option_0rtt) {
        r = FFI_mitls_configure_early_data(state, 1024*16);
        if (r == 0) {
            printf("FFI_mitls_configure_early_data(1024*16) failed.\n");
            return 2;
        }
    }

    if (option_psk) {
        printf("-psk is not yet implemented in cmitls\n");
        return 2;
    }

    if (option_ticket) {
        printf("-ticket is not yet implemented in cmitls\n");
        return 2;
    }

    if (option_offerpsk) {
        printf("-offerpsk is not yet implemented in cmitls\n");
        return 2;
    }

    if (option_alpn) {
        r = FFI_mitls_configure_alpn(state, option_alpn);
        if (r == 0) {
            printf("FFI_mitls_configure_alpn(%s) failed.\n", option_alpn);
            return 2;
        }
    }

    r = FFI_mitls_configure_nego_callback(state, NULL, nego_callback);
    if(!r) {
      printf("FFI_mitls_configure_nego_callback(%p)\n", nego_callback);
      return 2;
    }

    *pstate = state;
    return 0;
}

// Callback from miTLS, when it is ready to send a message via the socket
int SendCallback(void *pv, const unsigned char *buffer, size_t buffer_size)
{
    callback_context *ctx = (callback_context*)pv;
    ssize_t r;

    r = send(ctx->sockfd, buffer, buffer_size, 0);
    if (r != buffer_size) {
        printf("Error %d returned from socket send()\n", WSAGetLastError());
    }
    return (int)r;
}

// Callback from miTLS, when it is ready to receive a message via the socket
int RecvCallback(void* pv, unsigned char *buffer, size_t buffer_size)
{
    callback_context *ctx = (callback_context*)pv;
    ssize_t r;

    r = recv(ctx->sockfd, buffer, buffer_size, 0);
    if (r != buffer_size) {
        printf("Error %d returned from socket recv()\n", WSAGetLastError());
    }
    return (int)r;
}

#define MAX_RECEIVED_REQUEST_LENGTH  (65536) // 64kb
int SingleServer(mitls_state *state, SOCKET clientfd)
{
    callback_context ctx;
    char *out_msg;
    unsigned char *db;
    size_t db_length;
    int r;
    size_t payload_length;
    char *payload;

    const char ctext[] = "You are connected to miTLS*!\r\n"
                         "This is the request you sent:\r\n\r\n";
    const char cpayload[] = "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:%d\r\n"
                            "Content-Type: text/plain; charset=utf-8\r\n\r\n";

    ctx.sockfd = clientfd;
    r = FFI_mitls_accept_connected(&ctx, SendCallback, RecvCallback, state);
    if (r == 0) {
        printf("FFI_mitls_accept_connected() failed\n");
        return 1;
    }
    db = FFI_mitls_receive(state, &db_length);
    if (db == NULL) {
        printf("FFI_mitls_receive() failed\n");
        return 1;
    }
    printf("Received data:\n");
    puts((const char *)db);

    // Truncate overly long client requests
    if (db_length > MAX_RECEIVED_REQUEST_LENGTH) {
        db_length = MAX_RECEIVED_REQUEST_LENGTH;
    }

    // Determine the payload length.  This length is the maximum... the actual
    // length may be a few bytes less due to differing db_length-to-string conversions.
    // +5 for the number of characters needed to render text for the max db_length of 65536.
    payload_length=sizeof(ctext) + sizeof(cpayload) + db_length + 5;
    payload = (char*)_alloca(payload_length);
    sprintf(payload, cpayload, (int)(sizeof(ctext)+db_length-1) /* not counting the '\0' at the end of ctext */);
    strcat(payload, ctext);
    strncat(payload, (const char*)db, db_length);

    FFI_mitls_free_packet(state, db);
    r = FFI_mitls_send(state, payload, strlen(payload));
    if (r == 0) {
        printf("FFI_mitls_send() failed\n");
        return 1;
    }
    FFI_mitls_close(state);
    return 0;
}

int TestServer()
{
    SOCKET sockfd;
    struct hostent *host;
    struct sockaddr_in addr;
    mitls_state *state;

    printf("===============================================\n Starting test TLS server...\n");

    host = gethostbyname(option_hostname);
    if (host == NULL) {
        printf("Failed gethostbyname(%s) %d\n", option_hostname, WSAGetLastError());
        return 1;
    }
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    memcpy(&addr.sin_addr.s_addr, host->h_addr, host->h_length);
    addr.sin_port = htons(option_port);

    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) {
        printf("Failed socket open: %d\n", WSAGetLastError());
        return 1;
    }
    if (bind(sockfd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        printf("Failed bind() %d\n", WSAGetLastError());
        closesocket(sockfd);
        return 1;
    }
    if (listen(sockfd, 128) < 0) {
        printf("Failed listen() %d\n", WSAGetLastError());
        closesocket(sockfd);
        return 1;
    }
    while (1) {
        SOCKET clientsockfd;
        socklen_t len = sizeof(addr);

        clientsockfd = accept(sockfd, (struct sockaddr*)&addr, &len);
        if (clientsockfd == SOCKET_ERROR) {
            printf("Failed accept() %d\n", WSAGetLastError());
            closesocket(sockfd);
            return 1;
        }
        if (Configure(&state) != 0) {
            return 1;
        }
        if (SingleServer(state, clientsockfd)) {
            return 1;
        }
        closesocket(clientsockfd);
    }
    return 0;
}

typedef int (*quic_result_check)(quic_result r);

// auxiliary reading loop (brittle when using TCP)
void quic_recv_until(quic_state *state, SOCKET fd, quic_result_check check)
{
    quic_result r;
    char inbuf[8192];
    size_t inbufsize;
    char outbuf[8192];
    size_t outbufsize;
    int sockresult;

    inbufsize = 0;
    do {
        r = FFI_mitls_quic_process(state, inbuf, &inbufsize, outbuf, &outbufsize);
        switch (r) {
        case TLS_would_block: printf("would block\n"); break;
        case TLS_error_local: printf("fatal error\n"); break;
        case TLS_error_alert: printf("received fatal alert\n"); break;
        case TLS_client_early: printf("client offers early data\n"); break;
        case TLS_client_complete: printf("client completes {secret1}; the server is ignoring early data\n"); break;
        case TLS_client_complete_with_early_data: printf("client offers early data {secret0}"); break;
        case TLS_server_accept: printf("server accepts X early data\n"); break;
        case TLS_server_accept_with_early_data: printf("server accepts with early data {secret0; secret1}\n"); break;
        case TLS_server_complete: printf("server completes\n"); break;
        case TLS_error_other: printf("other miTLS error\n"); break;
        default: printf("Unknown return %d from FFI_mitls_quic_process\n", r); return;
        }
        if (outbufsize) {
            sockresult = send(fd, outbuf, (int)outbufsize, 0);
            if (sockresult != outbufsize) {
                printf("Socket send failed\n");
                return;
            }
        }
        if (inbufsize) {
            sockresult = recv(fd, inbuf, inbufsize, 0);
            if (sockresult != inbufsize) {
                printf("Socket recv failed\n");
                return;
            }
        }
    } while ((*check)(r));
}

void print_bytes(const void *buf, size_t len)
{
    const unsigned char *b = (const unsigned char*)buf;

    for (size_t i=0; i<len; ++i) {
        printf("%2.2x ", b[i]);
    }
}

// Indexed by quic_hash enum
const char *hash_names[] =
{
    "MD5", "SHA1", "SHA224", "SHA256", "SHA384", "SHA512"
};

// Indexed by quic_aead enum
const char *aead_names[] =
{
    "AES_128_GCM", "AES_256_GCM", "CHACHA20_POLY1305"
};

void print_secret(quic_secret *s)
{
    printf("{%s %s ", hash_names[s->hash], aead_names[s->ae]);
    print_bytes(s->secret, sizeof(s->secret));
    printf("}");
}

void quic_dump(quic_state *state)
{
    printf("OK\n");
    quic_secret secret0;
    quic_secret secret1;
    int ret0;
    int ret1;

    ret0 = FFI_mitls_quic_get_exporter(state, 0, &secret0);
    ret1 = FFI_mitls_quic_get_exporter(state, 1, &secret1);

    if (ret0) {
        printf("early secret: ");
        print_secret(&secret0);
        printf("\n");
    }
    if (ret1) {
        printf("main secret: ");
        print_secret(&secret1);
        printf("\n");
    }
    // bugbug: dump get_parameters of state for Client and Server  via FFI_mitls_quic_get_parameters()
}

int check_client_complete(quic_result r)
{
    if (r == TLS_client_complete || r == TLS_client_complete_with_early_data) {
        return 1;
    }
    return 0;
}

int check_is_ticketed(quic_result r)
{
    // bugbug: implement
    return 1;
}

int check_server_complete(quic_result r)
{
    if (r == TLS_server_complete) {
        return 1;
    }
    return 0;
}

int check_true(quic_result r)
{
    return 1;
}

int TestQuicClient(void)
{
    quic_state *state;
    SOCKET sockfd;
    struct hostent *peer;
    struct sockaddr_in addr;
    int r;

    printf("CLIENT\n");

    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) {
        printf("Failed socket open: %s\n", strerror(errno));
        return 1;
    }
    peer = gethostbyname(option_hostname);
    if (peer == NULL) {
        printf("Failed gethostbyname %s\n", strerror(errno));
        return 1;
    }
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    memcpy(&addr.sin_addr.s_addr, peer->h_addr, peer->h_length);
    addr.sin_port = htons(option_port);

    if (connect(sockfd, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
        printf("Failed connect %s\n", strerror(errno));
        return 1;
    }

    r = ConfigureQuic(&state);
    if (r != 0) {
        return 1;
    }

    quic_recv_until(state, sockfd, check_client_complete);
    quic_recv_until(state, sockfd, check_is_ticketed);
    quic_dump(state);

    return 0;
}

#define MAX_RECEIVED_REQUEST_LENGTH  (65536) // 64kb
int SingleQuicServer(quic_state *state, SOCKET clientfd)
{
    // brittle, as we need to write the ticket without blocking on TCP read.
    quic_recv_until(state, clientfd, check_server_complete);
    quic_recv_until(state, clientfd, check_true);
    quic_dump(state);

    FFI_mitls_quic_free(state);
    return 0;
}

int TestQuicServer(void)
{
    SOCKET sockfd;
    struct hostent *host;
    struct sockaddr_in addr;
    quic_state *state;

    printf("SERVER\n");

    host = gethostbyname(option_hostname);
    if (host == NULL) {
        printf("Failed gethostbyname(%s) %d\n", option_hostname, WSAGetLastError());
        return 1;
    }
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    memcpy(&addr.sin_addr.s_addr, host->h_addr, host->h_length);
    addr.sin_port = htons(option_port);

    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) {
        printf("Failed socket open: %d\n", WSAGetLastError());
        return 1;
    }
    if (bind(sockfd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        printf("Failed bind() %d\n", WSAGetLastError());
        closesocket(sockfd);
        return 1;
    }
    if (listen(sockfd, 128) < 0) {
        printf("Failed listen() %d\n", WSAGetLastError());
        closesocket(sockfd);
        return 1;
    }
    while (1) {
        SOCKET clientsockfd;
        socklen_t len = sizeof(addr);

        clientsockfd = accept(sockfd, (struct sockaddr*)&addr, &len);
        if (clientsockfd == SOCKET_ERROR) {
            printf("Failed accept() %d\n", WSAGetLastError());
            closesocket(sockfd);
            return 1;
        }
        if (ConfigureQuic(&state) != 0) {
            return 1;
        }
        if (SingleQuicServer(state, clientsockfd)) {
            return 1;
        }
        closesocket(clientsockfd);
    }
    return 0;
}

int TestClient(void)
{
    mitls_state *state;
    SOCKET sockfd;
    struct hostent *peer;
    struct sockaddr_in addr;
    int requestlength;
    ssize_t r;
    callback_context ctx;
    char *out_msg;
    char request[512];
    void *response;
    size_t response_length;

    printf("===============================================\n");
    printf("Starting test client...\n");

    const char request_template[] = "GET / HTTP/1.1\r\nHost: %s\r\n\r\n";
    if (sizeof(request_template) + strlen(option_hostname) >= sizeof(request)) {
        // Host name is too long
        printf("Host name is too long.\n");
        return 1;
    }
    requestlength = sprintf(request, request_template, option_hostname);

    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) {
        printf("Failed socket open: %s\n", strerror(errno));
        return 1;
    }
    peer = gethostbyname(option_hostname);
    if (peer == NULL) {
        printf("Failed gethostbyname %s\n", strerror(errno));
        return 1;
    }
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    memcpy(&addr.sin_addr.s_addr, peer->h_addr, peer->h_length);
    addr.sin_port = htons(option_port);

    if (connect(sockfd, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
        printf("Failed connect %s\n", strerror(errno));
        return 1;
    }

    r = Configure(&state);
    if (r != 0) {
        return 1;
    }

    ctx.sockfd = sockfd;
    r = FFI_mitls_connect(&ctx, SendCallback, RecvCallback, state);
    if (r == 0) {
        printf("FFI_mitls_connect() failed\n");
        return 1;
    }

    printf("Read OK, sending HTTP request...\n");
    r = FFI_mitls_send(state, request, requestlength);
    if (r == 0) {
        printf("FFI_mitls_send() failed\n");
        closesocket(sockfd);
        return 1;
    }

    response = FFI_mitls_receive(state, &response_length);
    if (response == NULL) {
        printf("FFI_mitls_receive() failed\n");
        closesocket(sockfd);
        return 1;
    }
    printf("Received data:\n");
    puts((const char *)response);
    FFI_mitls_free_packet(state, response);

    printf("Closing connection, irrespective of the response\n");
    FFI_mitls_close(state);
    closesocket(sockfd);

    return 0;
}

int main(int argc, char **argv)
{
    int r;

    printf("cmitls.exe ===================\n");

#if _WIN32
{
    WSADATA wsaData;
    r = WSAStartup(MAKEWORD(2,2), &wsaData);
    if (r != 0) {
        printf("WSAStartup failed: %d\n", r);
        return 2;
    }
}
#endif

    option_version = "1.3";
    if (ParseArgs(argc, argv) != 0) {
        PrintUsage();
        return 1;
    }

    if (option_minversion) {
        if (strcmp(option_minversion, option_version)) {
            printf("Warning: -mv is not supported via FFI yet.  Ignored.\n");
        }
    }

    printf("cmitls.exe calling FFI_mitls_init\n");
    r = FFI_mitls_init();
    if (r == 0) {
        printf("FFI_mitls_init() failed!\n");
        return 2;
    }

    printf("cmitls.exe about to act as client or server\n");
    if (option_isserver) {
        if (option_quic) {
            r = TestQuicServer();
        } else {
            r = TestServer();
        }
    } else {
        if (option_quic) {
            r = TestQuicClient();
        } else {
            r = TestClient();
        }
    }
    FFI_mitls_cleanup();

    return r;
}
