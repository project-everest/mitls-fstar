/* -------------------------------------------------------------------- */
#ifndef ECHO_OPTIONS_H__
# define ECHO_OPTIONS_H__

/* -------------------------------------------------------------------- */
# include "echo-ssl.h"
# include "echo-net.h"

/* -------------------------------------------------------------------- */
typedef struct options {
    int       debug   ;
    int       client  ;
    in4_t     echoname;
    tlsver_t  tlsver  ;
    char     *sname   ;
    char     *cname   ;
    char     *ciphers ;
    char     *dbdir   ;
    char     *pki     ;
} options_t;

/* -------------------------------------------------------------------- */
int _options(int argc, char *argv[], options_t *options);

#endif /* !ECHO_OPTIONS_H__ */
