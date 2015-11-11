/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>

#include <openssl/ssl.h>
#include <openssl/err.h>

#include "echo-log.h"
#include "echo-memory.h"
#include "echo-options.h"
#include "echo-ssl.h"
#include "echo-net.h"
#include "echo-server.h"

/* -------------------------------------------------------------------- */
typedef struct stream {
    /* options ref. */
    const options_t *options;

    /* remote hand FD / bevent */
    int fd, rdclosed, wrclosed;
    bufferevent_t *bevent;

    /* SSL context */
    SSL *sslcontext;

    /* logger */
    char *addst, *adsrc;
} stream_t;

/* -------------------------------------------------------------------- */
#define stelog(S, L, F, ...) \
    elog(L, "%s <-> %s: " F, (S)->adsrc, (S)->addst, ## __VA_ARGS__)

#define S2C_LOG_ERROR(S) (stelog(S, LOG_ERROR, "S2C copy failure"))
#define C2S_LOG_ERROR(S) (stelog(S, LOG_ERROR, "C2S copy failure"))

/* -------------------------------------------------------------------- */
static stream_t* stream_new(void) {
    stream_t *the = NEW(stream_t, 1);

    the->options    = NULL;
    the->rdclosed   = 0;
    the->wrclosed   = 0;
    the->fd         = -1;
    the->bevent     = NULL;
    the->sslcontext = NULL;
    the->addst      = NULL;
    the->adsrc      = NULL;

    return the;
}

static void stream_free(stream_t *the) {
    if (the->adsrc) free(the->adsrc);
    if (the->addst) free(the->addst);

    if (the->bevent != NULL)
        bufferevent_free(the->bevent);
    if (the->fd >= 0)
        (void) EVUTIL_CLOSESOCKET(the->fd);
    if (the->sslcontext != NULL)
        SSL_free(the->sslcontext);

    free(the);
}

/* -------------------------------------------------------------------- */
static int _check_for_stream_end(stream_t *stream) {
    if (stream->rdclosed && !stream->wrclosed) {
        evbuffer_t *output = bufferevent_get_output(stream->bevent);

        if (evbuffer_get_length(output) == 0) {
            (void) shutdown(stream->fd, SHUT_WR);
            stream->wrclosed = 1;
        }
    }

    if (!stream->wrclosed)
        return 0;

    stelog(stream, LOG_INFO, "all messages echo'ed. closing");
    stream_free(stream);

    return 1;
}

/* -------------------------------------------------------------------- */
static void _server_onread(bufferevent_t *be, void *arg) {
    stream_t *stream = (stream_t*) arg;

    evbuffer_t *ibuffer = bufferevent_get_input (stream->bevent);
    evbuffer_t *obuffer = bufferevent_get_output(stream->bevent);

    (void) be;

    while (1) {
        size_t  len  = 0u;
        char   *line = evbuffer_readln(ibuffer, &len, EVBUFFER_EOL_CRLF);

        if (line == NULL)
            break ;

        if (strcmp(line, "<renegotiate>") == 0) {
            stelog(stream, LOG_INFO, "starting renegotiation");

            if (bufferevent_ssl_renegotiate(be) < 0) {
                stelog(stream, LOG_ERROR, "error setting renegotiation");
                goto bailout;
            }
        }

        (void) evbuffer_expand(obuffer, len+2);
        if (evbuffer_add(obuffer, line  , len) < 0 ||
            evbuffer_add(obuffer, "\r\n", 2  ) < 0)
        {
            C2S_LOG_ERROR(stream);
            goto bailout;
        }
    }

    return ;

 bailout:
    stelog(stream, LOG_ERROR, "closing connection");
    stream_free(stream);
}

/* -------------------------------------------------------------------- */
static void _server_onwrite(bufferevent_t *be, void *arg) {
    stream_t *stream = (stream_t*) arg;

    (void) be;

    bufferevent_disable(stream->bevent, EV_WRITE);
    bufferevent_modcb(stream->bevent,
                      BEV_MOD_CB_READ | BEV_MOD_CB_WRITE,
                      NULL, NULL, NULL, stream);
    _check_for_stream_end(stream);
}

/* -------------------------------------------------------------------- */
static void _server_onerror(bufferevent_t *be, short what, void *arg) {
    stream_t *stream = (stream_t*) arg;

    (void) be;

    if ((what & BEV_EVENT_ERROR)) {
        int rr = evutil_socket_geterror(bufferevent_getfd(be));

        if (rr != 0) {
            stelog(stream, LOG_ERROR, "communication error: %s", strerror(rr));
        } else {
            unsigned long sslrr = bufferevent_get_openssl_error(be);

            if (sslrr != 0) {
                char txterr[256];

                ERR_error_string_n(sslrr, txterr, ARRAY_SIZE(txterr));
                stelog(stream, LOG_ERROR, "SSL error: %s", txterr);
            } else {
                stelog(stream, LOG_ERROR, "unknown communication error");
            }
        }

        goto bailout;
    }

    if ((what & BEV_EVENT_EOF)) {
        evbuffer_t *ibuffer = bufferevent_get_input (stream->bevent);
        evbuffer_t *obuffer = bufferevent_get_output(stream->bevent);

        if (evbuffer_add_buffer(obuffer, ibuffer) < 0) {
            C2S_LOG_ERROR(stream);
            goto bailout;
        }

        (void) shutdown(stream->fd, SHUT_RD);
        stream->rdclosed = 1;

        if (!_check_for_stream_end(stream)) {
            bufferevent_modcb(stream->bevent,
                              BEV_MOD_CB_READ | BEV_MOD_CB_WRITE,
                              NULL, _server_onwrite, NULL, stream);
        }
    }

    return ;

 bailout:
    stelog(stream, LOG_ERROR, "closing connection");
    stream_free(stream);
}

/* -------------------------------------------------------------------- */
typedef struct bindctxt {
    /*-*/ SSL_CTX   *sslcontext;
    const options_t *options;
} bindctxt_t;

/* -------------------------------------------------------------------- */
static void _server_onaccept(struct evconnlistener  *listener,
                             /*--*/ evutil_socket_t  fd      ,
                             struct sockaddr        *address ,
                             /*--*/ int              socklen ,
                             /*--*/ void            *arg     )
{
    bindctxt_t *context = (bindctxt_t*) arg;
    stream_t   *stream  = NULL;

    (void) listener;
    (void) socklen;

    stream = stream_new();

    stream->options = context->options;
    stream->fd      = fd;
    stream->adsrc   = inet4_ntop_x((in4_t*) address);
    stream->addst   = inet4_ntop_x(&context->options->echoname);

    evutil_make_socket_nonblocking(stream->fd);

    stelog(stream, LOG_INFO, "new client");

    if ((stream->sslcontext = SSL_new(context->sslcontext)) == NULL) {
        elog(LOG_ERROR, "cannot create SSL context");
        goto bailout;
    }

    stream->bevent =
        bufferevent_openssl_socket_new(evconnlistener_get_base(listener),
                                       stream->fd, stream->sslcontext,
                                       BUFFEREVENT_SSL_ACCEPTING,
                                       BEV_OPT_DEFER_CALLBACKS);
    bufferevent_setcb(stream->bevent, _server_onread, NULL, _server_onerror, stream);
    bufferevent_enable(stream->bevent, EV_READ|EV_WRITE);

    return ;

 bailout:
    if (stream != NULL)
        stream_free(stream);
}

/* -------------------------------------------------------------------- */
static void _server_onaccept_error(struct evconnlistener *listener, void *ctxt) {
    int err = EVUTIL_SOCKET_ERROR();

    (void) listener;
    (void) ctxt;

    elog(LOG_FATAL, "got an error %d (%s) on the listener",
         err, evutil_socket_error_to_string(err));
    event_loopexit(NULL);
}

/* -------------------------------------------------------------------- */
int echo_server_setup(event_base_t *evb, const options_t *options) {
    echossl_t         echossl;
    bindctxt_t       *context    = NULL;
    SSL_CTX          *sslcontext = NULL;
    evconnlistener_t *acceptln   = NULL;

    memset(&echossl, 0, sizeof(echossl));
    echossl.ciphers = options->ciphers;
    echossl.sname   = options->sname;
    echossl.cname   = options->cname;
    echossl.pki     = options->pki;
    echossl.tlsver  = options->tlsver;

    if ((sslcontext = evssl_init(&echossl, 1)) == NULL) {
        elog(LOG_FATAL, "cannot create SSL context");
        goto bailout;
    }

    context = NEW(bindctxt_t, 1);
    context->options    = options;
    context->sslcontext = sslcontext;

    acceptln = evconnlistener_new_bind
        (evb, _server_onaccept, context,
         LEV_OPT_CLOSE_ON_FREE | LEV_OPT_REUSEABLE, -1,
         (struct sockaddr*) &options->echoname,
         sizeof(options->echoname));

    if (acceptln == NULL) {
        elog(LOG_FATAL, "cannot create [libevent] listener");
        goto bailout;
    }

    evconnlistener_set_error_cb(acceptln, _server_onaccept_error);

    return 0;

 bailout:
    if (acceptln   != NULL) evconnlistener_free(acceptln);
    if (context    != NULL) free(context);
    if (sslcontext != NULL) SSL_CTX_free(sslcontext);

    return -1;
}
