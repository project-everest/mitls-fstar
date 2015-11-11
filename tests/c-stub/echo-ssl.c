/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>

#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/rand.h>

#include "echo-log.h"
#include "echo-memory.h"
#include "echo-ssl.h"

/* -------------------------------------------------------------------- */
const struct tlsversion_s tlsversions[] = {
    [SSL_3p0] = { SSL_3p0, "SSL_3p0"},
    [TLS_1p0] = { TLS_1p0, "TLS_1p0"},
    [TLS_1p1] = { TLS_1p1, "TLS_1p1"},
    [TLS_1p2] = { TLS_1p2, "TLS_1p2"},
};

/* -------------------------------------------------------------------- */
long SSL_CTX_use_tmp_dh_file(SSL_CTX *ctx, const char *filename) {
    BIO *stream   = NULL;
    DH  *dhparams = NULL;
    int  rr       = 0;

    if ((stream = BIO_new_file(filename, "r")) == NULL)
        goto bailout;
    if ((dhparams = PEM_read_bio_DHparams(stream, NULL, NULL, NULL)) == NULL)
        goto bailout;
    if (!(rr = SSL_CTX_set_tmp_dh(ctx, dhparams)))
        goto bailout;

    DH_free(dhparams);
    BIO_free(stream);

    return rr;

 bailout:
    if (dhparams != NULL) DH_free(dhparams);
    if (stream   != NULL) BIO_free(stream);

    return 0;
}

/* -------------------------------------------------------------------- */
tlsver_t tlsver_of_name(const char *name) {
    size_t i;

    for (i = 0; i < ARRAY_SIZE(tlsversions); ++i) {
        const struct tlsversion_s *p = &tlsversions[i];
        if (p->name != NULL && strcmp(p->name, name) == 0)
            return p->version;
    }

    return (tlsver_t) -1;
}

/* -------------------------------------------------------------------- */
SSL_CTX* evssl_init(const echossl_t *options, int isserver) {
    /*-*/ SSL_CTX    *context = NULL;
    /*-*/ char       *crtfile = NULL;
    /*-*/ char       *keyfile = NULL;
    /*-*/ char       *dhfile  = NULL;
    /*-*/ char       *CApath  = NULL;
    const SSL_METHOD *method  = NULL;

    if (options->sname != NULL) {
        crtfile = xjoin(options->pki, "/certificates/", options->sname, ".crt", NULL);
        keyfile = xjoin(options->pki, "/certificates/", options->sname, ".key", NULL);
    }

    dhfile  = xjoin(options->pki, "/certificates/dh.pem", NULL);
    CApath  = xjoin(options->pki, "/db/ca.db.certs", NULL);

    SSL_load_error_strings();
    SSL_library_init();

    if (!RAND_poll()) {
        elog(LOG_FATAL, "cannot initialize entropy");
        goto bailout;
    }

    if (isserver) {
        switch (options->tlsver) {
        case SSL_3p0: method = SSLv3_server_method  (); break ;
        case TLS_1p0: method = TLSv1_server_method  (); break ;
        case TLS_1p1: method = TLSv1_1_server_method(); break ;
        case TLS_1p2: method = TLSv1_2_server_method(); break ;
    
        default:
            abort();
        }
    } else {
        switch (options->tlsver) {
        case SSL_3p0: method = SSLv3_client_method  (); break ;
        case TLS_1p0: method = TLSv1_client_method  (); break ;
        case TLS_1p1: method = TLSv1_1_client_method(); break ;
        case TLS_1p2: method = TLSv1_2_client_method(); break ;
    
        default:
            abort();
        }
    }

    if ((context = SSL_CTX_new(method)) == NULL) {
        elog(LOG_FATAL, "cannot create SSL context");
        goto bailout;
    }

    if (options->ciphers != NULL) {
        if (!SSL_CTX_set_cipher_list(context, options->ciphers)) {
            elog(LOG_FATAL, "cannot set ciphers list `%s'", options->ciphers);
            goto bailout;
        }
    }

    if (!SSL_CTX_use_tmp_dh_file(context, dhfile)) {
        elog(LOG_FATAL, "cannot load/set DH parameters from file `%s'", dhfile);
        goto bailout;
    }

    if (!SSL_CTX_load_verify_locations(context, NULL, CApath)) {
        elog(LOG_FATAL, "cannot load trusted hashed CA path");
        goto bailout;
    }

    (void) SSL_CTX_set_default_verify_paths(context);

    if (isserver) {
        if (options->sname != NULL) {
            if (!SSL_CTX_use_certificate_chain_file(context, crtfile)) {
                elog(LOG_FATAL, "cannot load certificate `%s'", crtfile);
                goto bailout;
            }
    
            if (!SSL_CTX_use_PrivateKey_file(context, keyfile, SSL_FILETYPE_PEM)) {
                elog(LOG_FATAL, "cannot load certificate key `%s'", keyfile);
                goto bailout;
            }
        }
    }

    (void) SSL_CTX_set_options(context, SSL_OP_NO_COMPRESSION); 

    if (options->sname != NULL) {
        free(keyfile);
        free(crtfile);
    }

    free(dhfile);
    free(CApath);

    return context;

 bailout:
    if (context != NULL)
        SSL_CTX_free(context);

    if (keyfile != NULL) free(keyfile);
    if (crtfile != NULL) free(crtfile);
    if (dhfile  != NULL) free(dhfile);
    if (CApath  != NULL) free(CApath);

    return NULL;
}
