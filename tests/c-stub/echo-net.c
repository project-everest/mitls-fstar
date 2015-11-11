/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <string.h>

#include <assert.h>

#include "echo-memory.h"
#include "echo-net.h"

/* -------------------------------------------------------------------- */
void bufferevent_modcb(bufferevent_t *be, int flags,
                       bufferevent_data_cb readcb,
                       bufferevent_data_cb writecb,
                       bufferevent_event_cb errorcb,
                       void *cbarg)
{
    bufferevent_setcb
        (be, (flags & BEV_MOD_CB_READ ) ? readcb  : be->readcb ,
             (flags & BEV_MOD_CB_WRITE) ? writecb : be->writecb,
             (flags & BEV_MOD_CB_ERROR) ? errorcb : be->errorcb,
         cbarg);
}


/* -------------------------------------------------------------------- */
int be_empty(bufferevent_t *be) {
    evbuffer_t *ibuffer = bufferevent_get_input (be);
    evbuffer_t *obuffer = bufferevent_get_output(be);

    return
        evbuffer_get_length(ibuffer) == 0 &&
        evbuffer_get_length(obuffer) == 0;
}

/* -------------------------------------------------------------------- */
int getaddr4(in4_t *out, const char *hostname, const char *service) {
    int rr = 0;

    struct evutil_addrinfo ai, *res = NULL;

    memset(&ai, 0, sizeof(ai));
    ai.ai_flags    = 0;
    ai.ai_family   = AF_INET;
    ai.ai_socktype = SOCK_STREAM;
    ai.ai_protocol = 0;

    if ((rr = evutil_getaddrinfo(hostname, service, &ai, &res)) != 0)
        goto bailout;

    assert(res[0].ai_addrlen == sizeof(in4_t));
    memcpy(out, res[0].ai_addr, sizeof(in4_t));

 bailout:
    if (res != NULL)
        evutil_freeaddrinfo(res);

    return rr;
}

/* -------------------------------------------------------------------- */
char* inet4_ntop_x(const in4_t *addr) {
    char ip[] = "xxx.xxx.xxx.xxx";
    char *the = NULL;

    evutil_inet_ntop(AF_INET, &addr->sin_addr, ip, sizeof(ip));
    the = NEW(char, strlen(ip) + sizeof(uint16_t) * 8 + 1);
    sprintf(the, "%s:%d", ip, (uint16_t) ntohs(addr->sin_port));
    return the;
}
