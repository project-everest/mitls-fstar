/* -------------------------------------------------------------------- */
#ifndef ECHO_SSL_H__
# define ECHO_SSL_H__

/* -------------------------------------------------------------------- */
#include <openssl/ssl.h>

/* -------------------------------------------------------------------- */
typedef enum tlsversion_e {
    SSL_3p0 = 0x00,
    TLS_1p0 = 0x01,
    TLS_1p1 = 0x02,
    TLS_1p2 = 0x03,
} tlsver_t;

struct tlsversion_s {
    /*-*/ enum  tlsversion_e  version;
    const /*-*/ char         *name;
};

extern const struct tlsversion_s tlsversions[];

tlsver_t tlsver_of_name(const char *name);

/* -------------------------------------------------------------------- */
typedef struct echossl_s {
    char     *ciphers;
    char     *sname  ;
    char     *cname  ;
    char     *pki    ;
    tlsver_t  tlsver ;
} echossl_t;

/* -------------------------------------------------------------------- */
SSL_CTX* evssl_init(const echossl_t *options, int server);

#endif /* !ECHO_SSL_H__ */
