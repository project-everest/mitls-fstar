#ifndef TLS13_IO_KARAMEL_H
#define TLS13_IO_KARAMEL_H

#include <stddef.h>
#include <stdint.h>

#include "tls13_connection_backend.h"

TLS13_IO_channel tls13_io_channel_from_fd(int fd);

void tls13_io_channel_free(TLS13_IO_channel ch);

#endif
