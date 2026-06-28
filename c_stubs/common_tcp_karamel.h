#ifndef COMMON_TCP_KARAMEL_H
#define COMMON_TCP_KARAMEL_H

#include <stddef.h>
#include <stdint.h>

typedef struct Common_TCP_channel_s *Common_TCP_channel;
typedef struct Common_TCP_listener_s *Common_TCP_listener;

Common_TCP_channel Common_TCP_channel_of_fd(int fd);

size_t Common_TCP_read_full(
    Common_TCP_channel ch,
    uint8_t *out,
    size_t len,
    void *erased0,
    void *erased1,
    void *erased2);

size_t Common_TCP_write(
    Common_TCP_channel ch,
    uint8_t *buf,
    size_t len,
    void *erased0,
    void *erased1,
    void *erased2);

void Common_TCP_close(Common_TCP_channel ch, void *erased0, void *erased1);

#endif
