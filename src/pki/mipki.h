#ifndef HEADER_MIPKIH
#define HEADER_MIPKIH
#include <stdint.h>

#if defined(_MSC_VER)  // Visual Studio - always use __cdecl keyword
  #define MITLS_CALLCONV __cdecl
#elif defined(__cdecl) // GCC/MinGW targeting Windows 32-bit - use the __cdecl macro
  #define MITLS_CALLCONV __cdecl
#else                  // Targeting other platforms - use the ambient calling convention
  #define MITLS_CALLCONV
#endif

typedef struct {
  const char *cert_file;
  const char *key_file;
  int is_universal; // If true, this certificate can be used with any name
} mipki_config_entry;

typedef enum {
  MIPKI_SIGN,
  MIPKI_VERIFY
} mipki_mode;

// Abstract state of the PKI library, implementation-specific
typedef struct mipki_state mipki_state;

// Uses the TLS code points for signature schemes
//  rsa_pkcs1_sha1(0x0201),
//  rsa_pkcs1_sha256(0x0401),
//  rsa_pkcs1_sha384(0x0501),
//  rsa_pkcs1_sha512(0x0601),
//  rsa_pss_sha256(0x0804),
//  rsa_pss_sha384(0x0805),
//  rsa_pss_sha512(0x0806),
//  ecdsa_sha1(0x0203),
//  ecdsa_secp256r1_sha256(0x0403),
//  ecdsa_secp384r1_sha384(0x0503),
//  ecdsa_secp521r1_sha512(0x0603),
//  ed25519(0x0807),
//  ed448(0x0808),
typedef uint16_t mipki_signature;

// Abstract pointer to an entry in the certificate store
typedef const void* mipki_chain;

// A callback used to ask for the passphrase of the private key
// Should return the size of the written passphrase, or 0 on error
typedef int (MITLS_CALLCONV *password_callback)(char *pass, int max_size, const char *key_file);

// Create a new instance of the PKI library using the provided server configuration
// The configuration describes the selectable certificates as a server, and
// their private keys. They are loaded in memory until mipki_free is called.
// The created instance may be used in multiple TLS connections, for instance,
// it is recommanded to share the mipki_state accoress incoming connections on a server
mipki_state* MITLS_CALLCONV mipki_init(const mipki_config_entry config[], size_t config_len, password_callback pcb, int *erridx);
void MITLS_CALLCONV mipki_free(mipki_state *st);

// OpenSSL specific: configure a root certificate file or hash directory.
// This is mandatory to perform certificate chain validation
int MITLS_CALLCONV mipki_add_root_file_or_path(mipki_state *st, const char *ca_file);

// Find a certificate and signature algorithm compatible with the given SNI and list of offered signature algorithms
// Returns a pointer to the selected entry or NULL if no certificate is suitable
mipki_chain MITLS_CALLCONV mipki_select_certificate(mipki_state *st, const char *sni, const mipki_signature *algs, size_t algs_len, mipki_signature *selected);

// A combined signature-and-verify function (depending on m)
// Returns 0 on error. When signing, pass a reference to the size of the signature buffer to sig_len,
// after calling sig_len contains the acutal size of the signature. When verifying, pass a reference to the
// input signature length.
int MITLS_CALLCONV mipki_sign_verify(mipki_state *st, mipki_chain cert_ptr, const mipki_signature sigalg, const char *tbs, size_t tbs_len, char *sig, size_t *sig_len, mipki_mode m);

// Parse a chain in TLS network format into an abstract chain object
// Each certificate in the chain is encoded in DER, prefixed with the size of the
// DER-encodeded structure over 3 bytes. The returned chain must be freed after use
mipki_chain MITLS_CALLCONV mipki_parse_chain(mipki_state *st, const char *chain, size_t chain_len);

// Format an abstract chain into the TLS network format
size_t MITLS_CALLCONV mipki_format_chain(mipki_state *st, mipki_chain chain, char *buffer, size_t buffer_len);

// Certificate chain validation. This checks revocation, expiration, and matches the hostname
int MITLS_CALLCONV mipki_validate_chain(mipki_state *st, mipki_chain chain, const char *host);

// Free a chain after use.
void MITLS_CALLCONV mipki_free_chain(mipki_state *st, mipki_chain chain);


#endif
