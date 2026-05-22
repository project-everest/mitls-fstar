#ifndef TLS13_IO_STUBS_H
#define TLS13_IO_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/types.h>

ssize_t tls13_io_read_fd(int fd, uint8_t *out, size_t max_len);

ssize_t tls13_io_write_fd(int fd, const uint8_t *buf, size_t len);

#endif
