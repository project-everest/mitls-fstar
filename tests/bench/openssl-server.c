/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <unistd.h>
#include <sys/time.h>

#include <openssl/bio.h>
#include <openssl/ssl.h>
#include <openssl/err.h>

#define ECHO_NO_EVENT_LIB 1

#include "echo-memory.h"
#include "echo-ssl.h"
#include "echo-log.h"
#include "echo-net.h"

#ifndef WIN32
# define closesocket close
#endif

/* -------------------------------------------------------------------- */
#define TOSEND (64 * 1024u * 1024u)

/* -------------------------------------------------------------------- */
typedef struct sockaddr sockaddr_t;
typedef struct sockaddr_in in4_t;

/* -------------------------------------------------------------------- */
static void e_error(const char *message)
    __attribute__((noreturn));

static void e_error(const char *message) { /* Should move to WSAError under winsocks... */
    elog(LOG_FATAL, "%s: %s", message, strerror(errno));
    exit(EXIT_FAILURE);
}

static void i_error(const char *message)
    __attribute__((noreturn));

static void i_error(const char *message) {
    elog(LOG_FATAL, "%s", message);
    exit(EXIT_FAILURE);
}

static void s_error(unsigned long e, const char *message)
    __attribute__((noreturn));

static void s_error(unsigned long e, const char *message) {
    elog(LOG_FATAL, "%s: %s", message, ERR_error_string(e, NULL));
    exit(EXIT_FAILURE);
}

/* -------------------------------------------------------------------- */
static const int zero = 0;
static const int one  = 1;

int listener(void) {
    int   servfd = -1;
    in4_t sockname;
    in4_t peername;

    if ((servfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        e_error("socket(AF_INET, SOCK_STREAM)");

    memset(&sockname, 0, sizeof(in4_t));
    sockname.sin_family = AF_INET;
    sockname.sin_addr   = (struct in_addr) { .s_addr = INADDR_ANY };
    sockname.sin_port   = htons(5000);

    setsockopt(servfd, SOL_SOCKET, SO_REUSEADDR, (void*) &one, sizeof(one));

    if (bind(servfd, (sockaddr_t*) &sockname, sizeof(in4_t)) < 0)
        e_error("cannot bind socket");
    if (listen(servfd, 5) < 0)
        e_error("cannot set socket in listening mode");

    memset(&peername, 0, sizeof(in4_t));

    return servfd;
}
/* -------------------------------------------------------------------- */
#define BUFSIZE (1024u * 1024u)

void server(int servfd, SSL_CTX *sslctx) {
    socklen_t peerlen = sizeof(in4_t);
    in4_t     peername;
    int       client;
    int       rr;
    uint8_t  *buffer = NULL;

    SSL *ssl = NULL;

    buffer = xmalloc(BUFSIZE);

    while (1) {
        memset(&peername, 0, sizeof(peername));
        if ((client = accept(servfd, (sockaddr_t*) &peername, &peerlen)) < 0)
            e_error("accepting client");
    
        {   int ival = 128 * 1024;
            int oval = 128 * 1024;
            setsockopt(client, SOL_SOCKET, SO_RCVBUF, (void*) &ival, sizeof(ival));
            setsockopt(client, SOL_SOCKET, SO_SNDBUF, (void*) &oval, sizeof(oval));
        }

        if ((ssl = SSL_new(sslctx)) == NULL)
            i_error("cannot SSL server side SSL context");
    
        (void) SSL_set_fd(ssl, client);
        if ((rr = SSL_accept(ssl)) <= 0)
            s_error(ERR_get_error(), "SSL accept failed");
    
        while ((rr = SSL_read(ssl, buffer, BUFSIZE)) > 0) {}
    
        if (rr == 0) {
            int sslerr = SSL_get_error(ssl, rr);
    
            if (sslerr == SSL_ERROR_ZERO_RETURN) {
                if (!(SSL_get_shutdown(ssl) & SSL_RECEIVED_SHUTDOWN))
                    s_error(ERR_get_error(), "short-read in server");
            }
        } else
            s_error(ERR_get_error(), "read error in server");
    
        (void) SSL_shutdown(ssl);
        SSL_free(ssl);
        closesocket(client);
    }
}

/* -------------------------------------------------------------------- */
int main(void) {
    struct echossl_s options;
    int fd;
    SSL_CTX *sslctx = NULL;

#ifdef WIN32
    WSADATA WSAData;
#endif

    initialize_log4c();

#ifdef WIN32
    if (WSAStartup(MAKEWORD(2, 2), &WSAData) != 0) {
        elog(LOG_FATAL, "cannot initialize winsocks");
        return EXIT_FAILURE;
    }
#endif

    options.ciphers = xstrdup("ALL:NULL");
    options.sname   = getenv("CERTNAME");
    options.cname   = NULL;
    options.pki     = getenv("PKI");
    options.tlsver  = TLS_1p2;

    if (options.pki == NULL)
        i_error("no PKI directory given");
    options.pki = xstrdup(options.pki);

    if (options.sname == NULL)
        i_error("no cert-name given");
    options.sname = xstrdup(options.sname);

    (void) SSL_library_init();

    fd = listener();

    if ((sslctx = evssl_init(&options, 1)) == NULL)
        i_error("cannot initialize SSL context");
    (void) SSL_CTX_set_mode(sslctx, SSL_MODE_AUTO_RETRY);
    (void) SSL_CTX_set_session_cache_mode(sslctx, SSL_SESS_CACHE_OFF);
    server(fd, sslctx);

    (void) closesocket(fd);

#ifdef WIN32
    (void) WSACleanup();
#endif

    return EXIT_SUCCESS;
}
