/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>

#include "echo-log.h"
#include "echo-memory.h"
#include "echo-options.h"
#include "echo-ssl.h"
#include "echo-net.h"
#include "echo-client.h"

/* -------------------------------------------------------------------- */
int echo_client_setup(event_base_t *evb, const options_t *options) {
    (void) evb;
    (void) options;

    abort();
}
