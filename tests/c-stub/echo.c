/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>

#include <pthread.h>

#include "echo-log.h"
#include "echo-memory.h"
#include "echo-options.h"
#include "echo-client.h"
#include "echo-server.h"

/* -------------------------------------------------------------------- */
/* ------------ 0x0MNNFFPPSL ------------------------------------------ */
#define REQOSSL 0x01000103fL    /* 1.0.1c FINAL */

#if OPENSSL_VERSION_NUMBER < REQOSSL
# error "invalid OpenSSL version number"
#endif

/* -------------------------------------------------------------------- */
static event_base_t *evb = NULL;

/* -------------------------------------------------------------------- */
const intptr_t zero = 0;
const intptr_t one  = 1;

/* -------------------------------------------------------------------- */
static void* _entry (void *arg) {
    const options_t *options = (options_t*) arg;

    if ((evb = event_init()) == NULL) {
        elog(LOG_FATAL, "cannot initialize libevent");
        return (void*) zero;
    }

    event_set_log_callback(_evlog);
    event_set_mem_functions(&xmalloc, &xrealloc, &free);

    {   int rr;

        if (options->client)
            rr = echo_client_setup(evb, options);
        else
            rr = echo_server_setup(evb, options);

        if (rr < 0)
            return (void*) zero;
    }

    elog(LOG_NOTICE, "started");
    event_dispatch();

    return (void*) one;
}

/* -------------------------------------------------------------------- */
int main(int argc, char *argv[]) {
    options_t options;
    pthread_t worker;

#ifdef WIN32
    WSADATA WSAData;
#endif

    int rr = 0;

    if (argc-1 == 1 && strcmp(argv[1], "--info") == 0) {
        printf("Using OpenSSL 0x%08lx\n", SSLeay());
        return EXIT_SUCCESS;
    }

    initialize_log4c();

    if (SSLeay() < REQOSSL) {
        elog(LOG_FATAL, "OpenSSL version < 0x%08lx (compiled with 0x%08lx)",
             SSLeay(), OPENSSL_VERSION_NUMBER);
        return EXIT_FAILURE;
    }

    if (_options(argc, argv, &options) < 0)
        return EXIT_FAILURE;

    if (options.debug)
        log4c_category_set_priority(logcat, LOG_DEBUG);

#ifdef WIN32
    if (WSAStartup(MAKEWORD(2, 2), &WSAData) != 0) {
        elog(LOG_FATAL, "cannot initialize winsocks");
        return EXIT_FAILURE;
    }
#endif

    if (pthread_create(&worker, NULL, &_entry, &options) != 0) {
        elog(LOG_FATAL, "Cannot create worker thread");
        return EXIT_FAILURE;
    }

    (void) pthread_join(worker, (void**) &rr);

#ifdef WIN32
    (void) WSACleanup();
#endif

    return rr ? EXIT_SUCCESS : EXIT_FAILURE;
}
