#define _GNU_SOURCE

#include "atlas_trace.h"

#if ATLAS_ENABLE_LOGGING

#include <errno.h>
#include <fcntl.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

static _Atomic uint64_t atlas_trace_sequence = 1U;
static _Atomic uint64_t atlas_trace_connection_sequence = 1U;
static _Thread_local uint64_t atlas_trace_connection;
static _Atomic int atlas_trace_fd = -2;

static int atlas_trace_output_fd(void) {
  int fd = atomic_load_explicit(&atlas_trace_fd, memory_order_acquire);
  if (fd != -2) {
    return fd;
  }

  int opened = STDERR_FILENO;
  const char *path = getenv("ATLAS_TRACE_FILE");
  if (path != NULL && path[0] != '\0') {
    opened = open(path, O_APPEND | O_CREAT | O_WRONLY | O_CLOEXEC, 0600);
    if (opened < 0) {
      opened = STDERR_FILENO;
    }
  }

  int expected = -2;
  if (!atomic_compare_exchange_strong_explicit(
          &atlas_trace_fd,
          &expected,
          opened,
          memory_order_release,
          memory_order_relaxed)) {
    if (opened != STDERR_FILENO) {
      close(opened);
    }
    return expected;
  }
  return opened;
}

uint64_t atlas_trace_new_connection(void) {
  uint64_t local = atomic_fetch_add_explicit(
      &atlas_trace_connection_sequence, 1U, memory_order_relaxed);
  return ((uint64_t)(uint32_t)getpid() << 32) | (local & UINT32_MAX);
}

void atlas_trace_set_connection(uint64_t connection) {
  atlas_trace_connection = connection;
}

void atlas_trace_emit(
    uint32_t event,
    uint64_t arg0,
    uint64_t arg1,
    uint64_t arg2) {
  struct timespec now = {0, 0};
  (void)clock_gettime(CLOCK_MONOTONIC, &now);
  uint64_t timestamp_ns =
      (uint64_t)now.tv_sec * UINT64_C(1000000000) + (uint64_t)now.tv_nsec;
  uint64_t sequence = atomic_fetch_add_explicit(
      &atlas_trace_sequence, 1U, memory_order_relaxed);
  long thread_id = syscall(SYS_gettid);

  char line[384];
  int length = snprintf(
      line,
      sizeof line,
      "{\"atlas_trace\":1,\"ts_ns\":%llu,\"pid\":%ld,\"tid\":%ld,"
      "\"connection\":%llu,\"seq\":%llu,\"event\":%u,"
      "\"a0\":%llu,\"a1\":%llu,\"a2\":%llu}\n",
      (unsigned long long)timestamp_ns,
      (long)getpid(),
      thread_id,
      (unsigned long long)atlas_trace_connection,
      (unsigned long long)sequence,
      (unsigned int)event,
      (unsigned long long)arg0,
      (unsigned long long)arg1,
      (unsigned long long)arg2);
  if (length <= 0) {
    return;
  }
  size_t output_length =
      (size_t)length < sizeof line ? (size_t)length : sizeof line - 1U;
  ssize_t ignored;
  do {
    ignored = write(atlas_trace_output_fd(), line, output_length);
  } while (ignored < 0 && errno == EINTR);
  (void)ignored;
}

#endif
