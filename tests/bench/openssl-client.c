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
# define closesocket    close
# define GET_SOCKET_ERROR() (errno)
#else
# define GET_SOCKET_ERROR() (WSAGetLastError())
#endif

/* -------------------------------------------------------------------- */
#define TOSEND (128 * 1024u * 1024u)

/* -------------------------------------------------------------------- */
typedef struct sockaddr sockaddr_t;
typedef struct sockaddr_in in4_t;

/* -------------------------------------------------------------------- */
static void e_error(const char *message)
    __attribute__((noreturn));

static void e_error(const char *message) {
    elog(LOG_FATAL, "%s: %s", message, strerror(errno));
    exit(EXIT_FAILURE);
}

static void sock_error(const char *message)
    __attribute__((noreturn));

static void sock_error(const char *message) {
    elog(LOG_FATAL, "%s: %s", message, strerror(GET_SOCKET_ERROR()));
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
static uint8_t udata[1024 * 1024];

static void udata_initialize(void) {
    int    fd = -1;
    size_t position = 0;

#ifdef WIN32
#define URANDOM "urandom"
#else
#define URANDOM "/dev/urandom"
#endif

    if ((fd = open(URANDOM, O_RDONLY)) < 0)
        e_error("open(" URANDOM ")");
    while (position < sizeof(udata)) {
#ifdef WIN32
        (void) lseek(fd, 0, SEEK_SET);
#endif

        errno = 0;

        ssize_t rr = read(fd, &udata[position], sizeof(udata) - position);

        if (rr <= 0)
            e_error("reading from /dev/urandom");
        position += rr;
    }

    (void) close(fd);
}

/* -------------------------------------------------------------------- */
typedef struct ciphername {
    char *fullname;
    char *osslname;
} ciphername_t;

static const ciphername_t ciphernames[] = {
  { "TLS_RSA_WITH_NULL_MD5"              , "NULL-MD5"               },
  { "TLS_RSA_WITH_NULL_SHA"              , "NULL-SHA"               },
  { "TLS_RSA_WITH_NULL_SHA256"           , "NULL-SHA256"            },
  { "TLS_RSA_WITH_RC4_128_MD5"           , "RC4-MD5"                },
  { "TLS_RSA_WITH_RC4_128_SHA"           , "RC4-SHA"                },
  { "TLS_RSA_WITH_3DES_EDE_CBC_SHA"      , "DES-CBC3-SHA"           },
  { "TLS_RSA_WITH_AES_128_CBC_SHA"       , "AES128-SHA"             },
  { "TLS_RSA_WITH_AES_128_CBC_SHA256"    , "AES128-SHA256"          },
  { "TLS_RSA_WITH_AES_256_CBC_SHA"       , "AES256-SHA"             },
  { "TLS_RSA_WITH_AES_256_CBC_SHA256"    , "AES256-SHA256"          },
  { "TLS_DH_anon_WITH_3DES_EDE_CBC_SHA"  , "ADH-DES-CBC3-SHA"       },
  { "TLS_DH_anon_WITH_AES_128_CBC_SHA"   , "ADH-AES128-SHA"         },
  { "TLS_DH_anon_WITH_AES_128_CBC_SHA256", "ADH-AES128-SHA256"      },
  { "TLS_DH_anon_WITH_AES_256_CBC_SHA"   , "ADH-AES256-SHA"         },
  { "TLS_DH_anon_WITH_AES_256_CBC_SHA256", "ADH-AES256-SHA256"      },
  { "TLS_DH_anon_WITH_RC4_128_MD5"       , "ADH-RC4-MD5"            },
  { "TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA"  , "EDH-DSS-DES-CBC3-SHA"   },
  { "TLS_DHE_DSS_WITH_AES_128_CBC_SHA"   , "DHE-DSS-AES128-SHA"     },
  { "TLS_DHE_DSS_WITH_AES_128_CBC_SHA256", "DHE-DSS-AES128-SHA256"  },
  { "TLS_DHE_DSS_WITH_AES_256_CBC_SHA"   , "DHE-DSS-AES256-SHA"     },
  { "TLS_DHE_DSS_WITH_AES_256_CBC_SHA256", "DHE-DSS-AES256-SHA256"  },
  { "TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA"  , "EDH-RSA-DES-CBC3-SHA"   },
  { "TLS_DHE_RSA_WITH_AES_128_CBC_SHA"   , "DHE-RSA-AES128-SHA"     },
  { "TLS_DHE_RSA_WITH_AES_128_CBC_SHA256", "DHE-RSA-AES128-SHA256"  },
  { "TLS_DHE_RSA_WITH_AES_256_CBC_SHA"   , "DHE-RSA-AES256-SHA"     },
  { "TLS_DHE_RSA_WITH_AES_256_CBC_SHA256", "DHE-RSA-AES256-SHA256"  },

  { NULL, NULL},
};

static const char* get_ossl_cs(const char *csname) {
    const ciphername_t *p;

    for (p = &ciphernames[0]; p->fullname != NULL; ++p) {
        if (strcmp(csname, p->fullname) == 0)
            return p->osslname;
    }

    return NULL;
}

static const char* get_cs_fullname(const char *csname) {
    const ciphername_t *p;

    for (p = &ciphernames[0]; p->fullname != NULL; ++p) {
        if (strcmp(csname, p->osslname) == 0)
            return p->fullname;
    }

    return NULL;
}

/* -------------------------------------------------------------------- */
static const int zero = 0;
static const int one  = 1;

/* -------------------------------------------------------------------- */
void client(SSL_CTX *sslctx, const struct echossl_s *options) {
#define BLKSZ (256 * 1024u)
    int   i;
    int   fd;
    int   rr;
    in4_t peername;

    SSL *ssl = NULL;

    size_t sent = 0;
    size_t upos = 0;

    struct timeval tv1;
    struct timeval tv2;

    unsigned hsdone  = 0;
    double   hsticks = 0;

    memset(&peername, 0, sizeof(in4_t));
    peername.sin_family = AF_INET;
    peername.sin_addr   = (struct in_addr) { .s_addr = htonl(INADDR_LOOPBACK) };
    peername.sin_port   = htons(5000);

    for (i = 0; i < 250; ++i) {
        uint8_t byte[1] = { 0x00 };

        if ((fd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
            sock_error("socket(AF_INET, SOCK_STREAM)");
        if (connect(fd, (sockaddr_t*) &peername, sizeof(in4_t)) < 0)
            sock_error("connecting to server (HS)");

        (void) gettimeofday(&tv1, NULL);

        if ((ssl = SSL_new(sslctx)) == NULL)
            i_error("cannot SSL server side SSL context");
        (void) SSL_set_fd(ssl, fd);
        /* If the underlying BIO is blocking, SSL_connect() will only
           return once the handshake has been finished or an error
           occurred. */
        if ((rr = SSL_connect(ssl)) <= 0)
            s_error(ERR_get_error(), "SSL connect failed");

        if (SSL_write(ssl, byte, 1) <= 0)
            s_error(ERR_get_error(), "SSL write (HS) failed");

        (void) gettimeofday(&tv2, NULL);

        (void) SSL_shutdown(ssl);
        (void) SSL_free(ssl);
        (void) closesocket(fd); fd = -1;

        double tv1_d = (double)tv1.tv_sec + ((double)tv1.tv_usec) / 1000000;
        double tv2_d = (double)tv2.tv_sec + ((double)tv2.tv_usec) / 1000000;

        if (i != 0) {
            hsdone  += 1;
            hsticks += (tv2_d - tv1_d);
            
        }
    }

    if ((fd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        sock_error("socket(AF_INET, SOCK_STREAM)");

    if (connect(fd, (sockaddr_t*) &peername, sizeof(in4_t)) < 0)
        sock_error("connecting to server");

    {   int ival = 128 * 1024;
        int oval = 128 * 1024;
        setsockopt(fd, SOL_SOCKET, SO_RCVBUF, (void*) &ival, sizeof(ival));
        setsockopt(fd, SOL_SOCKET, SO_SNDBUF, (void*) &oval, sizeof(oval));
    }

    if ((ssl = SSL_new(sslctx)) == NULL)
        i_error("cannot SSL server side SSL context");
    (void) SSL_set_fd(ssl, fd);
    if ((rr = SSL_connect(ssl)) <= 0)
        s_error(ERR_get_error(), "SSL connect failed");

    (void) gettimeofday(&tv1, NULL);

    while (sent < TOSEND) {
        if (sizeof(udata) - upos < BLKSZ)
            upos = 0;
        if ((rr = SSL_write(ssl, &udata[upos], BLKSZ)) <= 0)
            s_error(ERR_get_error(), "client-side write failed");
        sent += rr;
        upos += rr;
        
    }

    (void) gettimeofday(&tv2, NULL);

    if ((rr = SSL_shutdown(ssl)) < 0)
        s_error(ERR_get_error(), "client-side shutdown failed");
    if (rr < 0)
        s_error(ERR_get_error(), "client-side shutdown failed");
    if (rr == 0) {
        if ((rr = SSL_shutdown(ssl)) < 0) {
            printf("%d\n", SSL_get_error(ssl, rr));
            s_error(ERR_get_error(), "client-side (bis) shutdown failed");
        }
    }

    SSL_free(ssl);

    double tv1_d = (double)tv1.tv_sec + ((double)tv1.tv_usec) / 1000000;
    double tv2_d = (double)tv2.tv_sec + ((double)tv2.tv_usec) / 1000000;

    printf("%s: %.2f HS/s\n",
           get_cs_fullname(options->ciphers),
           (hsdone / hsticks));
    printf("%s: %.2f MiB/s\n",
           get_cs_fullname(options->ciphers),
           (sent / ((double) (1024 * 1024))) / (tv2_d - tv1_d));

    (void) closesocket(fd);
}

/* -------------------------------------------------------------------- */
int main(void) {
    struct echossl_s options;
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

    options.ciphers = getenv("CIPHERSUITE");
    options.sname   = NULL;
    options.cname   = NULL;
    options.pki     = getenv("PKI");
    options.tlsver  = TLS_1p2;

    if (options.ciphers == NULL)
        i_error("no cipher suite given");
    options.ciphers = (char*) get_ossl_cs(options.ciphers);
    if (options.ciphers == NULL)
        i_error("unknown cipher name");
    options.ciphers = xstrdup(options.ciphers);
    if (options.pki == NULL)
        i_error("no PKI directory given");
    options.pki = xstrdup(options.pki);

    (void) SSL_library_init();
    udata_initialize();

    if ((sslctx = evssl_init(&options, 0)) == NULL)
        i_error("cannot initialize SSL context");
    (void) SSL_CTX_set_mode(sslctx, SSL_MODE_AUTO_RETRY);
    (void) SSL_CTX_set_session_cache_mode(sslctx, SSL_SESS_CACHE_OFF);
    client(sslctx, &options);

#ifdef WIN32
    (void) WSACleanup();
#endif

    return EXIT_SUCCESS;
}
