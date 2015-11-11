/* -------------------------------------------------------------------- */
#ifndef ECHO_SERVER_H__
# define ECHO_SERVER_H__

/* -------------------------------------------------------------------- */
#include "echo-options.h"
#include "echo-net.h"

/* -------------------------------------------------------------------- */
int echo_server_setup(event_base_t *evb, const options_t *options);

#endif /* !ECHO_SERVER_H__ */

