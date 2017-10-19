#ifndef HEADER_MIPKIH
#define HEADER_MIPKIH
#include <stdint.h>

typedef struct {
  const char *cert_file;
  const char *key_file;
  int is_universal;
} mipki_config_entry;

typedef uint16_t mipki_signature;

// A callback used to ask for the passphrase of the private key
typedef int (*password_callback)(char *pass, int max_size, const char *key_file);

int mipki_init(const mipki_config_entry config[], size_t config_len, password_callback pcb, int *erridx);
int mipki_add_root_file_or_path(const char *ca_file);
void* mipki_select_certificate(const char *sni, mipki_signature *algs, size_t algs_len, mipki_signature *selected);
size_t mipki_sign(const void *cert_ptr, const mipki_signature sigalg, const char *tbs, size_t tbs_len, char *sig);

#endif
