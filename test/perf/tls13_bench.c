#define _GNU_SOURCE

#include "tls13_client_driver.h"
#include "tls13_server_driver.h"

#include <arpa/inet.h>
#include <errno.h>
#include <inttypes.h>
#include <netinet/in.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define TLS13_BENCH_MAX_RECORD ((size_t)16384u)
#define TLS13_BENCH_CONTROL_BYTE ((uint8_t)0xa5u)
#define TLS13_BENCH_CONNECT_RETRIES 100000u
#define TLS13_BENCH_CONNECT_RETRY_US 100u

enum implementation {
  IMPL_VERIFIED,
  IMPL_OPENSSL,
};

enum role {
  ROLE_CLIENT,
  ROLE_SERVER,
};

enum operation {
  OP_HANDSHAKE,
  OP_SEND,
  OP_RECEIVE,
};

struct benchmark_case {
  const char *name;
  enum implementation implementation;
  enum role role;
  enum operation operation;
};

struct options {
  const struct benchmark_case *benchmark;
  size_t iterations;
  size_t warmup;
  size_t transfer_bytes;
  size_t message_size;
  unsigned trial;
  const char *cert_dir;
};

struct files {
  char ca_pem[512];
  char chain_pem[512];
  char leaf_der[512];
  char leaf_key[512];
};

struct buffer {
  uint8_t *data;
  size_t len;
};

struct usage_snapshot {
  uint64_t wall_ns;
  uint64_t cpu_ns;
  struct rusage usage;
};

struct measurement {
  uint64_t wall_ns;
  uint64_t cpu_ns;
  uint64_t user_us;
  uint64_t system_us;
  long minor_faults;
  long major_faults;
  long voluntary_context_switches;
  long involuntary_context_switches;
  long max_rss_kb;
};

static const struct benchmark_case benchmark_cases[] = {
    {"verified-client-handshake", IMPL_VERIFIED, ROLE_CLIENT, OP_HANDSHAKE},
    {"openssl-client-handshake", IMPL_OPENSSL, ROLE_CLIENT, OP_HANDSHAKE},
    {"verified-server-handshake", IMPL_VERIFIED, ROLE_SERVER, OP_HANDSHAKE},
    {"openssl-server-handshake", IMPL_OPENSSL, ROLE_SERVER, OP_HANDSHAKE},
    {"verified-client-send", IMPL_VERIFIED, ROLE_CLIENT, OP_SEND},
    {"verified-client-receive", IMPL_VERIFIED, ROLE_CLIENT, OP_RECEIVE},
    {"verified-server-send", IMPL_VERIFIED, ROLE_SERVER, OP_SEND},
    {"verified-server-receive", IMPL_VERIFIED, ROLE_SERVER, OP_RECEIVE},
    {"openssl-client-send", IMPL_OPENSSL, ROLE_CLIENT, OP_SEND},
    {"openssl-client-receive", IMPL_OPENSSL, ROLE_CLIENT, OP_RECEIVE},
    {"openssl-server-send", IMPL_OPENSSL, ROLE_SERVER, OP_SEND},
    {"openssl-server-receive", IMPL_OPENSSL, ROLE_SERVER, OP_RECEIVE},
};

static uint64_t timespec_ns(const struct timespec *ts) {
  return (uint64_t)ts->tv_sec * UINT64_C(1000000000) + (uint64_t)ts->tv_nsec;
}

static uint64_t timeval_us(const struct timeval *tv) {
  return (uint64_t)tv->tv_sec * UINT64_C(1000000) + (uint64_t)tv->tv_usec;
}

static uint64_t clock_ns(clockid_t clock_id) {
  struct timespec ts;
  if (clock_gettime(clock_id, &ts) != 0) {
    perror("clock_gettime");
    exit(2);
  }
  return timespec_ns(&ts);
}

static void take_snapshot(struct usage_snapshot *snapshot) {
  snapshot->wall_ns = clock_ns(CLOCK_MONOTONIC_RAW);
  snapshot->cpu_ns = clock_ns(CLOCK_PROCESS_CPUTIME_ID);
  if (getrusage(RUSAGE_SELF, &snapshot->usage) != 0) {
    perror("getrusage");
    exit(2);
  }
}

static struct measurement measurement_between(
    const struct usage_snapshot *start,
    const struct usage_snapshot *end) {
  struct measurement result;
  result.wall_ns = end->wall_ns - start->wall_ns;
  result.cpu_ns = end->cpu_ns - start->cpu_ns;
  result.user_us =
      timeval_us(&end->usage.ru_utime) - timeval_us(&start->usage.ru_utime);
  result.system_us =
      timeval_us(&end->usage.ru_stime) - timeval_us(&start->usage.ru_stime);
  result.minor_faults = end->usage.ru_minflt - start->usage.ru_minflt;
  result.major_faults = end->usage.ru_majflt - start->usage.ru_majflt;
  result.voluntary_context_switches =
      end->usage.ru_nvcsw - start->usage.ru_nvcsw;
  result.involuntary_context_switches =
      end->usage.ru_nivcsw - start->usage.ru_nivcsw;
  result.max_rss_kb = end->usage.ru_maxrss;
  return result;
}

static int compare_u64(const void *left, const void *right) {
  uint64_t a = *(const uint64_t *)left;
  uint64_t b = *(const uint64_t *)right;
  return (a > b) - (a < b);
}

static double percentile_us(uint64_t *samples, size_t count, unsigned percentile) {
  if (count == 0u) {
    return 0.0;
  }
  size_t index = ((count - 1u) * (size_t)percentile + 99u) / 100u;
  return (double)samples[index] / 1000.0;
}

static int parse_size(const char *text, size_t *out) {
  char *end = NULL;
  errno = 0;
  unsigned long long value = strtoull(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' || value > SIZE_MAX) {
    return -1;
  }
  *out = (size_t)value;
  return 0;
}

static int parse_unsigned(const char *text, unsigned *out) {
  size_t value = 0u;
  if (parse_size(text, &value) != 0 || value > UINT32_MAX) {
    return -1;
  }
  *out = (unsigned)value;
  return 0;
}

static const struct benchmark_case *find_case(const char *name) {
  size_t count = sizeof benchmark_cases / sizeof benchmark_cases[0];
  for (size_t i = 0u; i < count; ++i) {
    if (strcmp(name, benchmark_cases[i].name) == 0) {
      return &benchmark_cases[i];
    }
  }
  return NULL;
}

static void print_usage(const char *program) {
  fprintf(
      stderr,
      "usage: %s --case NAME [--iterations N] [--warmup N] "
      "[--bytes N] [--size N] [--trial N] [--cert-dir DIR]\n"
      "\nCases:\n",
      program);
  size_t count = sizeof benchmark_cases / sizeof benchmark_cases[0];
  for (size_t i = 0u; i < count; ++i) {
    fprintf(stderr, "  %s\n", benchmark_cases[i].name);
  }
}

static int parse_options(int argc, char **argv, struct options *options) {
  *options = (struct options){
      .benchmark = NULL,
      .iterations = 50u,
      .warmup = 5u,
      .transfer_bytes = 64u * 1024u * 1024u,
      .message_size = TLS13_BENCH_MAX_RECORD,
      .trial = 1u,
      .cert_dir = "test/certs",
  };
  for (int i = 1; i < argc; ++i) {
    if (i + 1 >= argc) {
      return -1;
    }
    const char *value = argv[++i];
    if (strcmp(argv[i - 1], "--case") == 0) {
      options->benchmark = find_case(value);
      if (options->benchmark == NULL) {
        fprintf(stderr, "unknown benchmark case: %s\n", value);
        return -1;
      }
    } else if (strcmp(argv[i - 1], "--iterations") == 0) {
      if (parse_size(value, &options->iterations) != 0) {
        return -1;
      }
    } else if (strcmp(argv[i - 1], "--warmup") == 0) {
      if (parse_size(value, &options->warmup) != 0) {
        return -1;
      }
    } else if (strcmp(argv[i - 1], "--bytes") == 0) {
      if (parse_size(value, &options->transfer_bytes) != 0) {
        return -1;
      }
    } else if (strcmp(argv[i - 1], "--size") == 0) {
      if (parse_size(value, &options->message_size) != 0) {
        return -1;
      }
    } else if (strcmp(argv[i - 1], "--trial") == 0) {
      if (parse_unsigned(value, &options->trial) != 0) {
        return -1;
      }
    } else if (strcmp(argv[i - 1], "--cert-dir") == 0) {
      options->cert_dir = value;
    } else {
      fprintf(stderr, "unknown option: %s\n", argv[i - 1]);
      return -1;
    }
  }
  if (options->benchmark == NULL || options->iterations == 0u ||
      options->message_size == 0u ||
      options->message_size > TLS13_BENCH_MAX_RECORD ||
      options->transfer_bytes == 0u) {
    return -1;
  }
  return 0;
}

static int make_path(char *out, size_t out_len, const char *dir, const char *name) {
  int written = snprintf(out, out_len, "%s/%s", dir, name);
  return written < 0 || (size_t)written >= out_len ? -1 : 0;
}

static int initialize_files(const struct options *options, struct files *files) {
  return make_path(files->ca_pem, sizeof files->ca_pem, options->cert_dir, "ca.pem") ||
         make_path(
             files->chain_pem,
             sizeof files->chain_pem,
             options->cert_dir,
             "chain.pem") ||
         make_path(
             files->leaf_der,
             sizeof files->leaf_der,
             options->cert_dir,
             "leaf.der") ||
         make_path(
             files->leaf_key,
             sizeof files->leaf_key,
             options->cert_dir,
             "leaf.key");
}

static int read_file(const char *path, struct buffer *out) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    perror(path);
    return -1;
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    perror("fseek");
    fclose(file);
    return -1;
  }
  long length = ftell(file);
  if (length < 0 || fseek(file, 0, SEEK_SET) != 0) {
    perror("ftell/fseek");
    fclose(file);
    return -1;
  }
  uint8_t *data = malloc(length == 0 ? 1u : (size_t)length);
  if (data == NULL) {
    fclose(file);
    return -1;
  }
  if (fread(data, 1u, (size_t)length, file) != (size_t)length) {
    perror("fread");
    free(data);
    fclose(file);
    return -1;
  }
  fclose(file);
  out->data = data;
  out->len = (size_t)length;
  return 0;
}

static int make_listener(uint16_t port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    return -1;
  }
  int one = 1;
  (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in address;
  memset(&address, 0, sizeof address);
  address.sin_family = AF_INET;
  address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  address.sin_port = htons(port);
  if (bind(fd, (struct sockaddr *)&address, sizeof address) != 0 ||
      listen(fd, 16) != 0) {
    close(fd);
    return -1;
  }
  return fd;
}

static int reserve_port(uint16_t *port) {
  int fd = make_listener(0u);
  if (fd < 0) {
    return -1;
  }
  struct sockaddr_in address;
  socklen_t address_len = sizeof address;
  if (getsockname(fd, (struct sockaddr *)&address, &address_len) != 0) {
    close(fd);
    return -1;
  }
  *port = ntohs(address.sin_port);
  close(fd);
  return 0;
}

static int connect_with_retry_delay(uint16_t port, useconds_t retry_delay_us) {
  struct sockaddr_in address;
  memset(&address, 0, sizeof address);
  address.sin_family = AF_INET;
  address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  address.sin_port = htons(port);
  for (unsigned attempt = 0u; attempt < TLS13_BENCH_CONNECT_RETRIES; ++attempt) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
      return -1;
    }
    if (connect(fd, (struct sockaddr *)&address, sizeof address) == 0) {
      return fd;
    }
    int saved_errno = errno;
    close(fd);
    if (saved_errno != ECONNREFUSED && saved_errno != EINTR &&
        saved_errno != EADDRNOTAVAIL) {
      errno = saved_errno;
      return -1;
    }
    if (retry_delay_us != 0u) {
      usleep(retry_delay_us);
    }
  }
  errno = ETIMEDOUT;
  return -1;
}

static int accept_retry(int listener) {
  int fd;
  do {
    fd = accept(listener, NULL, NULL);
  } while (fd < 0 && errno == EINTR);
  return fd;
}

static SSL_CTX *make_server_context(const struct files *files) {
  SSL_CTX *context = SSL_CTX_new(TLS_server_method());
  if (context == NULL) {
    return NULL;
  }
  SSL_CTX_clear_options(context, SSL_OP_ENABLE_MIDDLEBOX_COMPAT);
  SSL_CTX_set_options(context, SSL_OP_NO_TICKET);
  SSL_CTX_set_session_cache_mode(context, SSL_SESS_CACHE_OFF);
  if (SSL_CTX_set_min_proto_version(context, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_max_proto_version(context, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_ciphersuites(
          context, "TLS_CHACHA20_POLY1305_SHA256") != 1 ||
      SSL_CTX_set1_groups_list(context, "X25519") != 1 ||
      SSL_CTX_use_certificate_chain_file(context, files->chain_pem) != 1 ||
      SSL_CTX_use_PrivateKey_file(
          context, files->leaf_key, SSL_FILETYPE_PEM) != 1 ||
      SSL_CTX_check_private_key(context) != 1) {
    SSL_CTX_free(context);
    return NULL;
  }
  SSL_CTX_set_verify(context, SSL_VERIFY_NONE, NULL);
  return context;
}

static SSL_CTX *make_client_context(const struct files *files) {
  SSL_CTX *context = SSL_CTX_new(TLS_client_method());
  if (context == NULL) {
    return NULL;
  }
  SSL_CTX_clear_options(context, SSL_OP_ENABLE_MIDDLEBOX_COMPAT);
  SSL_CTX_set_options(context, SSL_OP_NO_TICKET);
  SSL_CTX_set_session_cache_mode(context, SSL_SESS_CACHE_OFF);
  if (SSL_CTX_set_min_proto_version(context, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_max_proto_version(context, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_ciphersuites(
          context, "TLS_CHACHA20_POLY1305_SHA256") != 1 ||
      SSL_CTX_set1_groups_list(context, "X25519") != 1 ||
      SSL_CTX_set1_sigalgs_list(context, "rsa_pss_rsae_sha256") != 1 ||
      SSL_CTX_load_verify_locations(context, files->ca_pem, NULL) != 1) {
    SSL_CTX_free(context);
    return NULL;
  }
  SSL_CTX_set_verify(context, SSL_VERIFY_PEER, NULL);
  return context;
}

static SSL *connect_openssl_with_delay(
    SSL_CTX *context,
    uint16_t port,
    useconds_t retry_delay_us,
    int *out_fd) {
  int fd = connect_with_retry_delay(port, retry_delay_us);
  if (fd < 0) {
    return NULL;
  }
  SSL *ssl = SSL_new(context);
  if (ssl == NULL || SSL_set_fd(ssl, fd) != 1 ||
      SSL_set_tlsext_host_name(ssl, "localhost") != 1 ||
      SSL_set1_host(ssl, "localhost") != 1 || SSL_connect(ssl) != 1) {
    SSL_free(ssl);
    close(fd);
    return NULL;
  }
  *out_fd = fd;
  return ssl;
}

static SSL *connect_openssl(SSL_CTX *context, uint16_t port, int *out_fd) {
  return connect_openssl_with_delay(
      context, port, TLS13_BENCH_CONNECT_RETRY_US, out_fd);
}

static SSL *accept_openssl(SSL_CTX *context, int listener, int *out_fd) {
  int fd = accept_retry(listener);
  if (fd < 0) {
    return NULL;
  }
  SSL *ssl = SSL_new(context);
  if (ssl == NULL || SSL_set_fd(ssl, fd) != 1 || SSL_accept(ssl) != 1) {
    SSL_free(ssl);
    close(fd);
    return NULL;
  }
  *out_fd = fd;
  return ssl;
}

static void close_openssl(SSL *ssl, int fd) {
  if (ssl != NULL) {
    (void)SSL_shutdown(ssl);
    SSL_free(ssl);
  }
  if (fd >= 0) {
    close(fd);
  }
}

static int ssl_write_all(SSL *ssl, const uint8_t *data, size_t length) {
  size_t offset = 0u;
  while (offset < length) {
    size_t written = 0u;
    if (SSL_write_ex(ssl, data + offset, length - offset, &written) != 1 ||
        written == 0u) {
      return -1;
    }
    offset += written;
  }
  return 0;
}

static int ssl_read_all(SSL *ssl, uint8_t *data, size_t length) {
  size_t offset = 0u;
  while (offset < length) {
    size_t read_length = 0u;
    if (SSL_read_ex(ssl, data + offset, length - offset, &read_length) != 1 ||
        read_length == 0u) {
      return -1;
    }
    offset += read_length;
  }
  return 0;
}

static int ssl_send_bytes(
    SSL *ssl,
    const uint8_t *payload,
    size_t total_bytes,
    size_t message_size) {
  size_t sent = 0u;
  while (sent < total_bytes) {
    size_t length = total_bytes - sent;
    if (length > message_size) {
      length = message_size;
    }
    if (ssl_write_all(ssl, payload, length) != 0) {
      return -1;
    }
    sent += length;
  }
  return 0;
}

static int validate_payload(
    const uint8_t *data,
    size_t total_bytes,
    const uint8_t *payload,
    size_t message_size) {
  size_t offset = 0u;
  while (offset < total_bytes) {
    size_t length = total_bytes - offset;
    if (length > message_size) {
      length = message_size;
    }
    if (memcmp(data + offset, payload, length) != 0) {
      fprintf(stderr, "application data mismatch near byte %zu\n", offset);
      return -1;
    }
    offset += length;
  }
  return 0;
}

static int ssl_receive_bytes(
    SSL *ssl,
    uint8_t *buffer,
    size_t total_bytes) {
  size_t received = 0u;
  while (received < total_bytes) {
    size_t capacity = total_bytes - received;
    if (capacity > TLS13_BENCH_MAX_RECORD) {
      capacity = TLS13_BENCH_MAX_RECORD;
    }
    size_t read_length = 0u;
    if (SSL_read_ex(
            ssl, buffer + received, capacity, &read_length) != 1 ||
        read_length == 0u) {
      return -1;
    }
    received += read_length;
  }
  return 0;
}

static int signal_ready(int fd) {
  uint8_t ready = TLS13_BENCH_CONTROL_BYTE;
  ssize_t written;
  do {
    written = write(fd, &ready, sizeof ready);
  } while (written < 0 && errno == EINTR);
  return written == (ssize_t)sizeof ready ? 0 : -1;
}

static int wait_ready(int fd) {
  uint8_t ready = 0u;
  ssize_t read_length;
  do {
    read_length = read(fd, &ready, sizeof ready);
  } while (read_length < 0 && errno == EINTR);
  return read_length == (ssize_t)sizeof ready &&
                 ready == TLS13_BENCH_CONTROL_BYTE
             ? 0
             : -1;
}

static int wait_child(pid_t child) {
  int status = 0;
  if (waitpid(child, &status, 0) < 0) {
    perror("waitpid");
    return -1;
  }
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    fprintf(stderr, "benchmark peer failed (status=%d)\n", status);
    return -1;
  }
  return 0;
}

static void terminate_child(pid_t child) {
  if (kill(child, SIGTERM) != 0 && errno != ESRCH) {
    perror("kill");
  }
  int status = 0;
  while (waitpid(child, &status, 0) < 0 && errno == EINTR) {
  }
}

static int openssl_server_handshake_peer(
    uint16_t port,
    size_t count,
    int ready_fd,
    const struct files *files) {
  alarm(300u);
  SSL_CTX *context = make_server_context(files);
  int listener = make_listener(port);
  if (context == NULL || listener < 0 || signal_ready(ready_fd) != 0) {
    ERR_print_errors_fp(stderr);
    SSL_CTX_free(context);
    if (listener >= 0) {
      close(listener);
    }
    return -1;
  }
  close(ready_fd);
  for (size_t i = 0u; i < count; ++i) {
    int fd = -1;
    SSL *ssl = accept_openssl(context, listener, &fd);
    if (ssl == NULL) {
      ERR_print_errors_fp(stderr);
      close(listener);
      SSL_CTX_free(context);
      return -1;
    }
    close_openssl(ssl, fd);
  }
  close(listener);
  SSL_CTX_free(context);
  return 0;
}

static int openssl_client_handshake_peer(
    uint16_t port,
    size_t count,
    const struct files *files,
    int sync_fd) {
  alarm(300u);
  SSL_CTX *context = make_client_context(files);
  if (context == NULL) {
    ERR_print_errors_fp(stderr);
    return -1;
  }
  for (size_t i = 0u; i < count; ++i) {
    if (wait_ready(sync_fd) != 0) {
      SSL_CTX_free(context);
      return -1;
    }
    int fd = -1;
    SSL *ssl = connect_openssl_with_delay(context, port, 0u, &fd);
    if (ssl == NULL) {
      ERR_print_errors_fp(stderr);
      SSL_CTX_free(context);
      return -1;
    }
    close_openssl(ssl, fd);
  }
  close(sync_fd);
  SSL_CTX_free(context);
  return 0;
}

static int verified_client_once(
    uint16_t port,
    const struct buffer *ca,
    uint64_t *latency_ns) {
  tls13_client_driver *driver = NULL;
  uint64_t start = clock_ns(CLOCK_MONOTONIC_RAW);
  int result = tls13_client_driver_connect(
      &driver,
      "127.0.0.1",
      port,
      "localhost",
      ca->data,
      ca->len,
      0u);
  *latency_ns = clock_ns(CLOCK_MONOTONIC_RAW) - start;
  if (result != 0) {
    fprintf(
        stderr,
        "verified client handshake failed: %s\n",
        tls13_client_driver_last_error(driver));
    tls13_client_driver_free(driver);
    return -1;
  }
  result = tls13_client_driver_close(driver, false);
  tls13_client_driver_free(driver);
  return result == 0 ? 0 : -1;
}

static int openssl_client_once(
    SSL_CTX *context,
    uint16_t port,
    uint64_t *latency_ns) {
  int fd = -1;
  uint64_t start = clock_ns(CLOCK_MONOTONIC_RAW);
  SSL *ssl = connect_openssl(context, port, &fd);
  *latency_ns = clock_ns(CLOCK_MONOTONIC_RAW) - start;
  if (ssl == NULL) {
    ERR_print_errors_fp(stderr);
    return -1;
  }
  close_openssl(ssl, fd);
  return 0;
}

static int run_client_handshakes(
    const struct options *options,
    const struct files *files,
    struct measurement *measurement,
    uint64_t *latencies) {
  struct buffer ca = {0};
  if (options->benchmark->implementation == IMPL_VERIFIED &&
      read_file(files->ca_pem, &ca) != 0) {
    return -1;
  }
  SSL_CTX *client_context = NULL;
  if (options->benchmark->implementation == IMPL_OPENSSL) {
    client_context = make_client_context(files);
    if (client_context == NULL) {
      ERR_print_errors_fp(stderr);
      free(ca.data);
      return -1;
    }
  }

  uint16_t port = 0u;
  int ready_pipe[2] = {-1, -1};
  if (reserve_port(&port) != 0 || pipe(ready_pipe) != 0) {
    perror("reserve_port/pipe");
    SSL_CTX_free(client_context);
    free(ca.data);
    return -1;
  }
  pid_t child = fork();
  if (child < 0) {
    perror("fork");
    SSL_CTX_free(client_context);
    free(ca.data);
    close(ready_pipe[0]);
    close(ready_pipe[1]);
    return -1;
  }
  if (child == 0) {
    close(ready_pipe[0]);
    int result = openssl_server_handshake_peer(
        port,
        options->warmup + options->iterations,
        ready_pipe[1],
        files);
    _exit(result == 0 ? 0 : 1);
  }
  close(ready_pipe[1]);
  if (wait_ready(ready_pipe[0]) != 0) {
    close(ready_pipe[0]);
    (void)wait_child(child);
    SSL_CTX_free(client_context);
    free(ca.data);
    return -1;
  }
  close(ready_pipe[0]);

  int result = 0;
  for (size_t i = 0u; i < options->warmup; ++i) {
    uint64_t ignored = 0u;
    if ((options->benchmark->implementation == IMPL_VERIFIED
             ? verified_client_once(port, &ca, &ignored)
             : openssl_client_once(client_context, port, &ignored)) != 0) {
      result = -1;
      break;
    }
  }

  struct usage_snapshot start;
  struct usage_snapshot end;
  take_snapshot(&start);
  for (size_t i = 0u; result == 0 && i < options->iterations; ++i) {
    if ((options->benchmark->implementation == IMPL_VERIFIED
             ? verified_client_once(port, &ca, &latencies[i])
             : openssl_client_once(client_context, port, &latencies[i])) != 0) {
      result = -1;
    }
  }
  take_snapshot(&end);
  *measurement = measurement_between(&start, &end);

  if (result != 0) {
    terminate_child(child);
  } else if (wait_child(child) != 0) {
    result = -1;
  }
  SSL_CTX_free(client_context);
  free(ca.data);
  return result;
}

static int verified_server_once(
    uint16_t port,
    const struct buffer *certificate,
    const struct buffer *key,
    uint64_t *latency_ns) {
  tls13_server_driver *driver = NULL;
  uint64_t start = clock_ns(CLOCK_MONOTONIC_RAW);
  int result = tls13_server_driver_accept(
      &driver,
      "127.0.0.1",
      port,
      certificate->data,
      certificate->len,
      key->data,
      key->len);
  *latency_ns = clock_ns(CLOCK_MONOTONIC_RAW) - start;
  if (result != 0) {
    fprintf(
        stderr,
        "verified server handshake failed: %s\n",
        tls13_server_driver_last_error(driver));
    tls13_server_driver_free(driver);
    return -1;
  }
  result = tls13_server_driver_close(driver, false);
  tls13_server_driver_free(driver);
  return result == 0 ? 0 : -1;
}

static int openssl_server_once(
    SSL_CTX *context,
    int listener,
    uint64_t *latency_ns) {
  int fd = -1;
  uint64_t start = clock_ns(CLOCK_MONOTONIC_RAW);
  SSL *ssl = accept_openssl(context, listener, &fd);
  *latency_ns = clock_ns(CLOCK_MONOTONIC_RAW) - start;
  if (ssl == NULL) {
    ERR_print_errors_fp(stderr);
    return -1;
  }
  close_openssl(ssl, fd);
  return 0;
}

static int run_server_handshakes(
    const struct options *options,
    const struct files *files,
    struct measurement *measurement,
    uint64_t *latencies) {
  struct buffer certificate = {0};
  struct buffer key = {0};
  SSL_CTX *server_context = NULL;
  int listener = -1;
  int sync_pair[2] = {-1, -1};
  uint16_t port = 0u;

  if (reserve_port(&port) != 0 ||
      socketpair(AF_UNIX, SOCK_STREAM, 0, sync_pair) != 0) {
    perror("reserve_port/socketpair");
    return -1;
  }
  if (options->benchmark->implementation == IMPL_VERIFIED) {
    if (read_file(files->leaf_der, &certificate) != 0 ||
        read_file(files->leaf_key, &key) != 0) {
      free(certificate.data);
      free(key.data);
      close(sync_pair[0]);
      close(sync_pair[1]);
      return -1;
    }
  } else {
    server_context = make_server_context(files);
    listener = make_listener(port);
    if (server_context == NULL || listener < 0) {
      ERR_print_errors_fp(stderr);
      SSL_CTX_free(server_context);
      if (listener >= 0) {
        close(listener);
      }
      close(sync_pair[0]);
      close(sync_pair[1]);
      return -1;
    }
  }

  pid_t child = fork();
  if (child < 0) {
    perror("fork");
    SSL_CTX_free(server_context);
    if (listener >= 0) {
      close(listener);
    }
    free(certificate.data);
    free(key.data);
    close(sync_pair[0]);
    close(sync_pair[1]);
    return -1;
  }
  if (child == 0) {
    close(sync_pair[0]);
    if (listener >= 0) {
      close(listener);
    }
    int result = openssl_client_handshake_peer(
        port,
        options->warmup + options->iterations,
        files,
        sync_pair[1]);
    _exit(result == 0 ? 0 : 1);
  }
  close(sync_pair[1]);

  int result = 0;
  for (size_t i = 0u; i < options->warmup; ++i) {
    uint64_t ignored = 0u;
    if (signal_ready(sync_pair[0]) != 0 ||
        (options->benchmark->implementation == IMPL_VERIFIED
             ? verified_server_once(port, &certificate, &key, &ignored)
             : openssl_server_once(server_context, listener, &ignored)) != 0) {
      result = -1;
      break;
    }
  }

  struct usage_snapshot start;
  struct usage_snapshot end;
  take_snapshot(&start);
  for (size_t i = 0u; result == 0 && i < options->iterations; ++i) {
    if (signal_ready(sync_pair[0]) != 0 ||
        (options->benchmark->implementation == IMPL_VERIFIED
             ? verified_server_once(
                   port, &certificate, &key, &latencies[i])
             : openssl_server_once(
                   server_context, listener, &latencies[i])) != 0) {
      result = -1;
    }
  }
  take_snapshot(&end);
  *measurement = measurement_between(&start, &end);

  close(sync_pair[0]);
  if (result != 0) {
    terminate_child(child);
  } else if (wait_child(child) != 0) {
    result = -1;
  }
  if (listener >= 0) {
    close(listener);
  }
  SSL_CTX_free(server_context);
  free(certificate.data);
  free(key.data);
  return result;
}

static int openssl_transfer_protocol(
    SSL *ssl,
    int sync_fd,
    enum operation measured_operation,
    const uint8_t *payload,
    uint8_t *buffer,
    size_t transfer_bytes,
    size_t message_size) {
  uint8_t control = TLS13_BENCH_CONTROL_BYTE;
  if (signal_ready(sync_fd) != 0 || wait_ready(sync_fd) != 0) {
    return -1;
  }
  if (measured_operation == OP_SEND) {
    if (ssl_receive_bytes(
            ssl,
            buffer,
            transfer_bytes) != 0 ||
        validate_payload(
            buffer, transfer_bytes, payload, message_size) != 0 ||
        ssl_write_all(ssl, &control, sizeof control) != 0) {
      return -1;
    }
  } else {
    if (ssl_send_bytes(ssl, payload, transfer_bytes, message_size) != 0 ||
        ssl_read_all(ssl, &control, sizeof control) != 0 ||
        control != TLS13_BENCH_CONTROL_BYTE) {
      return -1;
    }
  }
  return 0;
}

static int openssl_server_transfer_peer(
    uint16_t port,
    int ready_fd,
    int sync_fd,
    enum operation measured_operation,
    const struct options *options,
    const struct files *files,
    const uint8_t *payload,
    uint8_t *buffer) {
  alarm(300u);
  SSL_CTX *context = make_server_context(files);
  int listener = make_listener(port);
  if (context == NULL || listener < 0 || signal_ready(ready_fd) != 0) {
    ERR_print_errors_fp(stderr);
    SSL_CTX_free(context);
    if (listener >= 0) {
      close(listener);
    }
    return -1;
  }
  close(ready_fd);
  int fd = -1;
  SSL *ssl = accept_openssl(context, listener, &fd);
  int result =
      ssl == NULL
          ? -1
          : openssl_transfer_protocol(
                ssl,
                sync_fd,
                measured_operation,
                payload,
                buffer,
                options->transfer_bytes,
                options->message_size);
  if (result != 0) {
    ERR_print_errors_fp(stderr);
  }
  close_openssl(ssl, fd);
  close(sync_fd);
  close(listener);
  SSL_CTX_free(context);
  return result;
}

static int openssl_client_transfer_peer(
    uint16_t port,
    int sync_fd,
    enum operation measured_operation,
    const struct options *options,
    const struct files *files,
    const uint8_t *payload,
    uint8_t *buffer) {
  alarm(300u);
  SSL_CTX *context = make_client_context(files);
  if (context == NULL) {
    ERR_print_errors_fp(stderr);
    return -1;
  }
  int fd = -1;
  SSL *ssl = connect_openssl(context, port, &fd);
  int result =
      ssl == NULL
          ? -1
          : openssl_transfer_protocol(
                ssl,
                sync_fd,
                measured_operation,
                payload,
                buffer,
                options->transfer_bytes,
                options->message_size);
  if (result != 0) {
    ERR_print_errors_fp(stderr);
  }
  close_openssl(ssl, fd);
  close(sync_fd);
  SSL_CTX_free(context);
  return result;
}

static int verified_client_send_bytes(
    tls13_client_driver *driver,
    const uint8_t *payload,
    size_t total_bytes,
    size_t message_size) {
  size_t sent = 0u;
  while (sent < total_bytes) {
    size_t length = total_bytes - sent;
    if (length > message_size) {
      length = message_size;
    }
    if (tls13_client_driver_send_application_data(driver, payload, length) != 0) {
      fprintf(stderr, "%s\n", tls13_client_driver_last_error(driver));
      return -1;
    }
    sent += length;
  }
  return 0;
}

static int verified_client_receive_bytes(
    tls13_client_driver *driver,
    uint8_t *buffer,
    size_t total_bytes) {
  size_t received = 0u;
  while (received < total_bytes) {
    size_t length = 0u;
    if (tls13_client_driver_receive_application_data(
            driver,
            buffer + received,
            TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE,
            &length) != 0 ||
        length == 0u || length > total_bytes - received) {
      fprintf(stderr, "%s\n", tls13_client_driver_last_error(driver));
      return -1;
    }
    received += length;
  }
  return 0;
}

static int verified_server_send_bytes(
    tls13_server_driver *driver,
    const uint8_t *payload,
    size_t total_bytes,
    size_t message_size) {
  size_t sent = 0u;
  while (sent < total_bytes) {
    size_t length = total_bytes - sent;
    if (length > message_size) {
      length = message_size;
    }
    if (tls13_server_driver_send_application_data(driver, payload, length) != 0) {
      fprintf(stderr, "%s\n", tls13_server_driver_last_error(driver));
      return -1;
    }
    sent += length;
  }
  return 0;
}

static int verified_server_receive_bytes(
    tls13_server_driver *driver,
    uint8_t *buffer,
    size_t total_bytes) {
  size_t received = 0u;
  while (received < total_bytes) {
    size_t length = 0u;
    if (tls13_server_driver_receive_application_data(
            driver,
            buffer + received,
            TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE,
            &length) != 0 ||
        length == 0u || length > total_bytes - received) {
      fprintf(stderr, "%s\n", tls13_server_driver_last_error(driver));
      return -1;
    }
    received += length;
  }
  return 0;
}

static int run_verified_client_transfer(
    const struct options *options,
    uint16_t port,
    const struct buffer *ca,
    const uint8_t *payload,
    uint8_t *buffer,
    int sync_fd,
    struct measurement *measurement) {
  tls13_client_driver *driver = NULL;
  if (tls13_client_driver_connect(
          &driver,
          "127.0.0.1",
          port,
          "localhost",
          ca->data,
          ca->len,
          0u) != 0) {
    fprintf(stderr, "%s\n", tls13_client_driver_last_error(driver));
    tls13_client_driver_free(driver);
    return -1;
  }
  uint8_t control[TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE];
  size_t control_len = 0u;
  int result = 0;
  struct usage_snapshot start;
  struct usage_snapshot end;
  if (wait_ready(sync_fd) != 0) {
    result = -1;
  }
  take_snapshot(&start);
  if (result == 0 && signal_ready(sync_fd) != 0) {
    result = -1;
  }
  if (options->benchmark->operation == OP_SEND) {
    if (result == 0 &&
        verified_client_send_bytes(
            driver,
            payload,
            options->transfer_bytes,
            options->message_size) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        (tls13_client_driver_receive_application_data(
             driver, control, sizeof control, &control_len) != 0 ||
         control_len != 1u || control[0] != TLS13_BENCH_CONTROL_BYTE)) {
      result = -1;
    }
  } else {
    if (result == 0 &&
        verified_client_receive_bytes(
            driver,
            buffer,
            options->transfer_bytes) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        validate_payload(
            buffer,
            options->transfer_bytes,
            payload,
            options->message_size) != 0) {
      result = -1;
    }
    if (result == 0 &&
        tls13_client_driver_send_application_data(
            driver, &((uint8_t){TLS13_BENCH_CONTROL_BYTE}), 1u) != 0) {
      result = -1;
    }
  }
  *measurement = measurement_between(&start, &end);
  (void)tls13_client_driver_close(driver, false);
  tls13_client_driver_free(driver);
  return result;
}

static int run_openssl_client_transfer(
    const struct options *options,
    uint16_t port,
    SSL_CTX *context,
    const uint8_t *payload,
    uint8_t *buffer,
    int sync_fd,
    struct measurement *measurement) {
  int fd = -1;
  SSL *ssl = connect_openssl(context, port, &fd);
  if (ssl == NULL) {
    ERR_print_errors_fp(stderr);
    return -1;
  }
  uint8_t control = TLS13_BENCH_CONTROL_BYTE;
  int result = 0;
  struct usage_snapshot start;
  struct usage_snapshot end;
  if (wait_ready(sync_fd) != 0) {
    result = -1;
  }
  take_snapshot(&start);
  if (result == 0 && signal_ready(sync_fd) != 0) {
    result = -1;
  }
  if (options->benchmark->operation == OP_SEND) {
    if (result == 0 &&
        ssl_send_bytes(
            ssl, payload, options->transfer_bytes, options->message_size) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        (ssl_read_all(ssl, &control, sizeof control) != 0 ||
         control != TLS13_BENCH_CONTROL_BYTE)) {
      result = -1;
    }
  } else {
    if (result == 0 &&
        ssl_receive_bytes(
            ssl,
            buffer,
            options->transfer_bytes) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        validate_payload(
            buffer,
            options->transfer_bytes,
            payload,
            options->message_size) != 0) {
      result = -1;
    }
    if (result == 0 &&
        ssl_write_all(ssl, &control, sizeof control) != 0) {
      result = -1;
    }
  }
  *measurement = measurement_between(&start, &end);
  if (result != 0) {
    ERR_print_errors_fp(stderr);
  }
  close_openssl(ssl, fd);
  return result;
}

static int run_client_transfer(
    const struct options *options,
    const struct files *files,
    const uint8_t *payload,
    uint8_t *buffer,
    struct measurement *measurement) {
  struct buffer ca = {0};
  SSL_CTX *client_context = NULL;
  if (options->benchmark->implementation == IMPL_VERIFIED) {
    if (read_file(files->ca_pem, &ca) != 0) {
      return -1;
    }
  } else {
    client_context = make_client_context(files);
    if (client_context == NULL) {
      ERR_print_errors_fp(stderr);
      return -1;
    }
  }

  uint16_t port = 0u;
  int ready_pipe[2] = {-1, -1};
  int sync_pair[2] = {-1, -1};
  if (reserve_port(&port) != 0 || pipe(ready_pipe) != 0) {
    perror("reserve_port/pipe");
    free(ca.data);
    SSL_CTX_free(client_context);
    return -1;
  }
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sync_pair) != 0) {
    perror("socketpair");
    close(ready_pipe[0]);
    close(ready_pipe[1]);
    free(ca.data);
    SSL_CTX_free(client_context);
    return -1;
  }
  pid_t child = fork();
  if (child < 0) {
    perror("fork");
    free(ca.data);
    SSL_CTX_free(client_context);
    close(ready_pipe[0]);
    close(ready_pipe[1]);
    close(sync_pair[0]);
    close(sync_pair[1]);
    return -1;
  }
  if (child == 0) {
    close(ready_pipe[0]);
    close(sync_pair[0]);
    int result = openssl_server_transfer_peer(
        port,
        ready_pipe[1],
        sync_pair[1],
        options->benchmark->operation,
        options,
        files,
        payload,
        buffer);
    _exit(result == 0 ? 0 : 1);
  }
  close(ready_pipe[1]);
  close(sync_pair[1]);
  int result = wait_ready(ready_pipe[0]);
  close(ready_pipe[0]);
  if (result == 0) {
    result = options->benchmark->implementation == IMPL_VERIFIED
                 ? run_verified_client_transfer(
                       options,
                       port,
                       &ca,
                       payload,
                       buffer,
                       sync_pair[0],
                       measurement)
                 : run_openssl_client_transfer(
                       options,
                       port,
                       client_context,
                       payload,
                       buffer,
                       sync_pair[0],
                       measurement);
  }
  close(sync_pair[0]);
  if (result != 0) {
    terminate_child(child);
  } else if (wait_child(child) != 0) {
    result = -1;
  }
  free(ca.data);
  SSL_CTX_free(client_context);
  return result;
}

static int run_verified_server_transfer(
    const struct options *options,
    uint16_t port,
    const struct buffer *certificate,
    const struct buffer *key,
    const uint8_t *payload,
    uint8_t *buffer,
    int sync_fd,
    struct measurement *measurement) {
  tls13_server_driver *driver = NULL;
  if (tls13_server_driver_accept(
          &driver,
          "127.0.0.1",
          port,
          certificate->data,
          certificate->len,
          key->data,
          key->len) != 0) {
    fprintf(stderr, "%s\n", tls13_server_driver_last_error(driver));
    tls13_server_driver_free(driver);
    return -1;
  }
  uint8_t control[TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE];
  size_t control_len = 0u;
  int result = 0;
  struct usage_snapshot start;
  struct usage_snapshot end;
  if (wait_ready(sync_fd) != 0) {
    result = -1;
  }
  take_snapshot(&start);
  if (result == 0 && signal_ready(sync_fd) != 0) {
    result = -1;
  }
  if (options->benchmark->operation == OP_SEND) {
    if (result == 0 &&
        verified_server_send_bytes(
            driver,
            payload,
            options->transfer_bytes,
            options->message_size) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        (tls13_server_driver_receive_application_data(
             driver, control, sizeof control, &control_len) != 0 ||
         control_len != 1u || control[0] != TLS13_BENCH_CONTROL_BYTE)) {
      result = -1;
    }
  } else {
    if (result == 0 &&
        verified_server_receive_bytes(
            driver,
            buffer,
            options->transfer_bytes) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        validate_payload(
            buffer,
            options->transfer_bytes,
            payload,
            options->message_size) != 0) {
      result = -1;
    }
    if (result == 0 &&
        tls13_server_driver_send_application_data(
            driver, &((uint8_t){TLS13_BENCH_CONTROL_BYTE}), 1u) != 0) {
      result = -1;
    }
  }
  *measurement = measurement_between(&start, &end);
  (void)tls13_server_driver_close(driver, false);
  tls13_server_driver_free(driver);
  return result;
}

static int run_openssl_server_transfer(
    const struct options *options,
    SSL_CTX *context,
    int listener,
    const uint8_t *payload,
    uint8_t *buffer,
    int sync_fd,
    struct measurement *measurement) {
  int fd = -1;
  SSL *ssl = accept_openssl(context, listener, &fd);
  if (ssl == NULL) {
    ERR_print_errors_fp(stderr);
    return -1;
  }
  uint8_t control = TLS13_BENCH_CONTROL_BYTE;
  int result = 0;
  struct usage_snapshot start;
  struct usage_snapshot end;
  if (wait_ready(sync_fd) != 0) {
    result = -1;
  }
  take_snapshot(&start);
  if (result == 0 && signal_ready(sync_fd) != 0) {
    result = -1;
  }
  if (options->benchmark->operation == OP_SEND) {
    if (result == 0 &&
        ssl_send_bytes(
            ssl, payload, options->transfer_bytes, options->message_size) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        (ssl_read_all(ssl, &control, sizeof control) != 0 ||
         control != TLS13_BENCH_CONTROL_BYTE)) {
      result = -1;
    }
  } else {
    if (result == 0 &&
        ssl_receive_bytes(
            ssl,
            buffer,
            options->transfer_bytes) != 0) {
      result = -1;
    }
    take_snapshot(&end);
    if (result == 0 &&
        validate_payload(
            buffer,
            options->transfer_bytes,
            payload,
            options->message_size) != 0) {
      result = -1;
    }
    if (result == 0 &&
        ssl_write_all(ssl, &control, sizeof control) != 0) {
      result = -1;
    }
  }
  *measurement = measurement_between(&start, &end);
  if (result != 0) {
    ERR_print_errors_fp(stderr);
  }
  close_openssl(ssl, fd);
  return result;
}

static int run_server_transfer(
    const struct options *options,
    const struct files *files,
    const uint8_t *payload,
    uint8_t *buffer,
    struct measurement *measurement) {
  struct buffer certificate = {0};
  struct buffer key = {0};
  SSL_CTX *server_context = NULL;
  int listener = -1;
  int sync_pair[2] = {-1, -1};
  uint16_t port = 0u;
  if (reserve_port(&port) != 0 ||
      socketpair(AF_UNIX, SOCK_STREAM, 0, sync_pair) != 0) {
    return -1;
  }
  if (options->benchmark->implementation == IMPL_VERIFIED) {
    if (read_file(files->leaf_der, &certificate) != 0 ||
        read_file(files->leaf_key, &key) != 0) {
      free(certificate.data);
      free(key.data);
      close(sync_pair[0]);
      close(sync_pair[1]);
      return -1;
    }
  } else {
    server_context = make_server_context(files);
    listener = make_listener(port);
    if (server_context == NULL || listener < 0) {
      ERR_print_errors_fp(stderr);
      SSL_CTX_free(server_context);
      if (listener >= 0) {
        close(listener);
      }
      close(sync_pair[0]);
      close(sync_pair[1]);
      return -1;
    }
  }

  pid_t child = fork();
  if (child < 0) {
    perror("fork");
    SSL_CTX_free(server_context);
    if (listener >= 0) {
      close(listener);
    }
    free(certificate.data);
    free(key.data);
    close(sync_pair[0]);
    close(sync_pair[1]);
    return -1;
  }
  if (child == 0) {
    close(sync_pair[0]);
    if (listener >= 0) {
      close(listener);
    }
    int result = openssl_client_transfer_peer(
        port,
        sync_pair[1],
        options->benchmark->operation,
        options,
        files,
        payload,
        buffer);
    _exit(result == 0 ? 0 : 1);
  }
  close(sync_pair[1]);

  int result =
      options->benchmark->implementation == IMPL_VERIFIED
          ? run_verified_server_transfer(
                options,
                port,
                &certificate,
                &key,
                payload,
                buffer,
                sync_pair[0],
                measurement)
          : run_openssl_server_transfer(
                options,
                server_context,
                listener,
                payload,
                buffer,
                sync_pair[0],
                measurement);
  close(sync_pair[0]);
  if (result != 0) {
    terminate_child(child);
  } else if (wait_child(child) != 0) {
    result = -1;
  }
  if (listener >= 0) {
    close(listener);
  }
  SSL_CTX_free(server_context);
  free(certificate.data);
  free(key.data);
  return result;
}

static const char *implementation_name(enum implementation implementation) {
  return implementation == IMPL_VERIFIED ? "verified" : "openssl";
}

static const char *role_name(enum role role) {
  return role == ROLE_CLIENT ? "client" : "server";
}

static const char *operation_name(enum operation operation) {
  switch (operation) {
    case OP_HANDSHAKE:
      return "handshake";
    case OP_SEND:
      return "send";
    case OP_RECEIVE:
      return "receive";
  }
  return "unknown";
}

static void print_result(
    const struct options *options,
    const struct measurement *measurement,
    uint64_t *latencies) {
  bool handshake = options->benchmark->operation == OP_HANDSHAKE;
  size_t operations =
      handshake
          ? options->iterations
          : (options->transfer_bytes + options->message_size - 1u) /
                options->message_size;
  size_t bytes = handshake ? 0u : options->transfer_bytes;
  double wall_seconds = (double)measurement->wall_ns / 1.0e9;
  double cpu_seconds = (double)measurement->cpu_ns / 1.0e9;
  double operations_per_second =
      wall_seconds == 0.0 ? 0.0 : (double)operations / wall_seconds;
  double mib_per_second =
      wall_seconds == 0.0
          ? 0.0
          : ((double)bytes / (1024.0 * 1024.0)) / wall_seconds;
  double nanoseconds_per_operation =
      operations == 0u ? 0.0 : (double)measurement->wall_ns / (double)operations;
  double p50_us = 0.0;
  double p95_us = 0.0;
  double p99_us = 0.0;
  if (handshake) {
    qsort(latencies, options->iterations, sizeof latencies[0], compare_u64);
    p50_us = percentile_us(latencies, options->iterations, 50u);
    p95_us = percentile_us(latencies, options->iterations, 95u);
    p99_us = percentile_us(latencies, options->iterations, 99u);
  }
  printf(
      "case,trial,implementation,role,operation,message_size,operations,bytes,"
      "wall_seconds,cpu_seconds,ops_per_second,mib_per_second,"
      "ns_per_operation,p50_us,p95_us,p99_us,user_seconds,system_seconds,"
      "minor_faults,major_faults,voluntary_context_switches,"
      "involuntary_context_switches,max_rss_kb\n");
  printf(
      "%s,%u,%s,%s,%s,%zu,%zu,%zu,%.9f,%.9f,%.3f,%.3f,%.3f,"
      "%.3f,%.3f,%.3f,%.6f,%.6f,%ld,%ld,%ld,%ld,%ld\n",
      options->benchmark->name,
      options->trial,
      implementation_name(options->benchmark->implementation),
      role_name(options->benchmark->role),
      operation_name(options->benchmark->operation),
      handshake ? 0u : options->message_size,
      operations,
      bytes,
      wall_seconds,
      cpu_seconds,
      operations_per_second,
      mib_per_second,
      nanoseconds_per_operation,
      p50_us,
      p95_us,
      p99_us,
      (double)measurement->user_us / 1.0e6,
      (double)measurement->system_us / 1.0e6,
      measurement->minor_faults,
      measurement->major_faults,
      measurement->voluntary_context_switches,
      measurement->involuntary_context_switches,
      measurement->max_rss_kb);
}

int main(int argc, char **argv) {
  struct options options;
  if (parse_options(argc, argv, &options) != 0) {
    print_usage(argv[0]);
    return 2;
  }
  struct files files;
  if (initialize_files(&options, &files) != 0) {
    fprintf(stderr, "certificate path is too long\n");
    return 2;
  }
  alarm(600u);
  signal(SIGPIPE, SIG_IGN);
  OPENSSL_init_ssl(0u, NULL);

  struct measurement measurement;
  memset(&measurement, 0, sizeof measurement);
  uint64_t *latencies = NULL;
  uint8_t *payload = NULL;
  uint8_t *buffer = NULL;
  int result = -1;

  if (options.benchmark->operation == OP_HANDSHAKE) {
    latencies = calloc(options.iterations, sizeof latencies[0]);
    if (latencies == NULL) {
      return 2;
    }
    result = options.benchmark->role == ROLE_CLIENT
                 ? run_client_handshakes(
                       &options, &files, &measurement, latencies)
                 : run_server_handshakes(
                       &options, &files, &measurement, latencies);
  } else {
    size_t receive_slack =
        TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE >
                TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE
            ? TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE
            : TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE;
    if (options.transfer_bytes > SIZE_MAX - receive_slack) {
      return 2;
    }
    payload = malloc(options.message_size);
    buffer = malloc(options.transfer_bytes + receive_slack);
    if (payload == NULL || buffer == NULL) {
      free(payload);
      free(buffer);
      return 2;
    }
    for (size_t i = 0u; i < options.message_size; ++i) {
      payload[i] = (uint8_t)(i * 31u + 7u);
    }
    result = options.benchmark->role == ROLE_CLIENT
                 ? run_client_transfer(
                       &options, &files, payload, buffer, &measurement)
                 : run_server_transfer(
                       &options, &files, payload, buffer, &measurement);
  }

  if (result == 0) {
    print_result(&options, &measurement, latencies);
  }
  free(latencies);
  free(payload);
  free(buffer);
  return result == 0 ? 0 : 1;
}
