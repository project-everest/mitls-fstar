#ifndef COMMON_TCP_CUSTARD_H
#define COMMON_TCP_CUSTARD_H

#include <stddef.h>
#include <stdint.h>

typedef struct Common_TCP_channel_s *Common_TCP_channel;
typedef struct Common_TCP_listener_s *Common_TCP_listener;

Common_TCP_channel Common_TCP_channel_of_fd(int fd);
/* A channel that reads from rfd and writes to wfd (e.g. stdin/stdout). */
Common_TCP_channel Common_TCP_channel_of_fds(int rfd, int wfd);

#ifdef COMMON_TCP_CUSTARD_FULL_DECLS

size_t Common_TCP_read_full(
    Common_TCP_channel ch,
    uint8_t *out,
    size_t len);

size_t Common_TCP_write(
    Common_TCP_channel ch,
    uint8_t *buf,
    size_t len);

void Common_TCP_close(Common_TCP_channel ch);

#endif

#endif
