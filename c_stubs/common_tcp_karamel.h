#ifndef COMMON_TCP_KARAMEL_H
#define COMMON_TCP_KARAMEL_H

#include <stddef.h>
#include <stdint.h>

typedef struct Common_TCP_channel_s *Common_TCP_channel;
typedef struct Common_TCP_listener_s *Common_TCP_listener;

size_t Common_TCP_read_full(Common_TCP_channel ch, uint8_t *out, size_t len);

#endif
