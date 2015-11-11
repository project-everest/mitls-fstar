/* -------------------------------------------------------------------- */
#ifndef ECHO_NET_H__
# define ECHO_NET_H__

/* -------------------------------------------------------------------- */
#ifndef WIN32
# include <unistd.h>
#endif

#ifdef WIN32
# define _WINSOCKAPI_
# include <winsock2.h>
# include <ws2tcpip.h>
#else
# include <sys/socket.h>
# include <netinet/in.h>
# include <netinet/tcp.h>
# include <arpa/inet.h>
# include <netdb.h>
#endif

#ifdef WIN32
# define SHUT_RD   SD_RECEIVE
# define SHUT_WR   SD_SEND
# define SHUT_RDWR SD_BOTH
#endif

#ifdef WIN32
#define ERR(e) WSA##e
#else
#define ERR(e) e
#endif

/* -------------------------------------------------------------------- */
#ifndef ECHO_NO_EVENT_LIB
#include <event.h>
#include <event2/util.h>
#include <event2/listener.h>
#include <event2/bufferevent_ssl.h>
#endif

/* -------------------------------------------------------------------- */
typedef struct sockaddr_in in4_t;

/* -------------------------------------------------------------------- */
#ifndef ECHO_NO_EVENT_LIB
typedef struct event event_t;
typedef struct event_base event_base_t;
typedef struct bufferevent bufferevent_t;
typedef struct evbuffer evbuffer_t;
typedef struct evconnlistener evconnlistener_t;
#endif

/* -------------------------------------------------------------------- */
#ifndef ECHO_NO_EVENT_LIB

#define BEV_MOD_CB_READ  0x01
#define BEV_MOD_CB_WRITE 0x02
#define BEV_MOD_CB_ERROR 0x04

void bufferevent_modcb(bufferevent_t *be, int flags,
                       bufferevent_data_cb readcb,
                       bufferevent_data_cb writecb,
                       bufferevent_event_cb errorcb,
                       void *cbarg);

int be_empty(bufferevent_t *be);
#endif

/* -------------------------------------------------------------------- */
#ifndef ECHO_NO_EVENT_LIB
int   getaddr4(in4_t *out, const char *hostname, const char *service);
char* inet4_ntop_x(const in4_t *addr);
#endif

#endif /* !ECHO_NET_H__ */
