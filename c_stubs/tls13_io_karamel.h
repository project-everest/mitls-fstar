#ifndef TLS13_IO_KARAMEL_H
#define TLS13_IO_KARAMEL_H

#include <stddef.h>
#include <stdint.h>

typedef struct TLS13_IO_channel_s *TLS13_IO_channel;
typedef struct TLS13_IO_listener_s *TLS13_IO_listener;

TLS13_IO_channel tls13_io_channel_from_fd(int fd);

void tls13_io_channel_free(TLS13_IO_channel ch);

#endif
