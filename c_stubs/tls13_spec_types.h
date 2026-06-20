/* Compatibility definitions for symbols that generated headers use before
   KaRaMeL emits a concrete C definition for them. */
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

/* Test code historically used the Epoch suffixes; generated code emits the
   unsuffixed names. */
#define TLS13_Record_Spec_HandshakeEpoch TLS13_Record_Spec_Handshake
#define TLS13_Record_Spec_ApplicationEpoch TLS13_Record_Spec_Application

#ifndef TLS13_X509_SPEC_TRUST_STORE_DEFINED
#define TLS13_X509_SPEC_TRUST_STORE_DEFINED
typedef void *TLS13_X509_Spec_trust_store;
#endif

typedef uint8_t *TLS13_X509_Spec_cert_chain;
typedef void *TLS13_X509_Spec_peer_identity;

typedef struct TLS13_X509_Spec_validation_time_s {
  size_t seconds_since_epoch;
} TLS13_X509_Spec_validation_time;

#endif /* TLS13_SPEC_TYPES_H */
