#ifndef TLS13_OPENSSL_KARAMEL_H
#define TLS13_OPENSSL_KARAMEL_H

#include <stddef.h>
#include <stdint.h>

typedef struct TLS13_OpenSSL_auth_context_s *TLS13_OpenSSL_auth_context;
typedef struct TLS13_OpenSSL_server_credentials_s *TLS13_OpenSSL_server_credentials;

#ifndef TLS13_X509_SPEC_TRUST_STORE_DEFINED
#define TLS13_X509_SPEC_TRUST_STORE_DEFINED
typedef void *TLS13_X509_Spec_trust_store;
#endif

typedef uint8_t *TLS13_X509_Spec_cert_chain;
typedef void *TLS13_X509_Spec_peer_identity;

typedef struct TLS13_X509_Spec_validation_time_s {
  size_t seconds_since_epoch;
} TLS13_X509_Spec_validation_time;

#endif
