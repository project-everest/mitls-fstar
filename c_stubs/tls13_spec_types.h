/* Spec-level types needed by TLS13.Record internal functions */
#ifndef TLS13_SPEC_TYPES_H
#define TLS13_SPEC_TYPES_H

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

#endif /* TLS13_SPEC_TYPES_H */
