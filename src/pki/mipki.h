#ifndef HEADER_MIPKIH
#define HEADER_MIPKIH
#include <stdint.h>

typedef struct {
  const char *cert_file;
  const char *key_file;
  int is_universal;
} mipki_config_entry;

typedef enum {
  MIPKI_SIGN,
  MIPKI_VERIFY
} mipki_mode;

typedef uint16_t mipki_signature;
typedef void* mipki_chain;

// A callback used to ask for the passphrase of the private key
typedef int (*password_callback)(char *pass, int max_size, const char *key_file);

int mipki_init(const mipki_config_entry config[], size_t config_len, password_callback pcb, int *erridx);
int mipki_add_root_file_or_path(const char *ca_file);
mipki_chain mipki_select_certificate(const char *sni, mipki_signature *algs, size_t algs_len, mipki_signature *selected);
int mipki_sign_verify(const mipki_chain cert_ptr, const mipki_signature sigalg, const char *tbs, size_t tbs_len, char *sig, size_t *sig_len, mipki_mode m);
mipki_chain mipki_parse_chain(const char *chain, size_t chain_len);
int mipki_format_chain(const mipki_chain chain, char *buffer, size_t buffer_len);
int mipki_validate_chain(const mipki_chain chain, const char *host);
void mipki_free_chain(mipki_chain chain);

#endif
