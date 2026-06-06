#ifndef TLS13_IO_KARAMEL_H
#define TLS13_IO_KARAMEL_H

#include <stddef.h>
#include <stdint.h>

#include "tls13_connection_backend.h"

TLS13_IO_channel tls13_io_channel_from_fd(int fd);

void tls13_io_channel_free(TLS13_IO_channel ch);

typedef struct option__TLS13_IO_channel_s option__TLS13_IO_channel;

option__TLS13_IO_channel TLS13_IO_connect_tcp(
    uint8_t *hostname,
    size_t hostname_len,
    uint16_t port,
    void *hostname_bytes);

size_t TLS13_IO_read(
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t max_len,
    void *old);

size_t TLS13_IO_write(
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes);

void TLS13_IO_close(TLS13_IO_channel ch);

#endif
