/* Spec-level and abstract implementation types needed by extracted C. */
#ifndef TLS13_SPEC_TYPES_H
#define TLS13_SPEC_TYPES_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifndef FStar_SizeT_uint_to_t
#define FStar_SizeT_uint_to_t(n) ((size_t)(n))
#endif
#ifndef FStar_SizeT_v
#define FStar_SizeT_v(n) ((size_t)(n))
#endif

/* Keep this C shim ABI-compatible with KaRaMeL's uint8_t extraction. */
#ifndef TLS13_Record_Spec_Initial
#define TLS13_Record_Spec_Initial 0
#endif
#ifndef TLS13_Record_Spec_Handshake
#define TLS13_Record_Spec_Handshake 1
#endif
#ifndef TLS13_Record_Spec_Application
#define TLS13_Record_Spec_Application 2
#endif

#define TLS13_Record_Spec_HandshakeEpoch TLS13_Record_Spec_Handshake
#define TLS13_Record_Spec_ApplicationEpoch TLS13_Record_Spec_Application

typedef uint8_t TLS13_Record_Spec_epoch;

#ifndef TLS13_X509_SPEC_TRUST_STORE_DEFINED
#define TLS13_X509_SPEC_TRUST_STORE_DEFINED
typedef void *TLS13_X509_Spec_trust_store;
#endif

typedef uint8_t *TLS13_X509_Spec_cert_chain;
typedef void *TLS13_X509_Spec_peer_identity;

typedef struct TLS13_X509_Spec_validation_time_s {
  size_t seconds_since_epoch;
} TLS13_X509_Spec_validation_time;

typedef struct TLS13_Record_record_state_s {
  uint8_t *key;
  uint8_t *iv;
  uint64_t *seq;
  bool *installed;
} TLS13_Record_record_state;

#endif /* TLS13_SPEC_TYPES_H */
