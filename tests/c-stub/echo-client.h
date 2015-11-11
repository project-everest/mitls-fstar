/* -------------------------------------------------------------------- */
#ifndef ECHO_CLIENT_H__
# define ECHO_CLIENT_H__

/* -------------------------------------------------------------------- */
#include "echo-options.h"
#include "echo-net.h"

/* -------------------------------------------------------------------- */
int echo_client_setup(event_base_t *evb, const options_t *options);

#endif /* !ECHO_CLIENT_H__ */
