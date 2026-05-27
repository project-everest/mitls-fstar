/* Spec-level types needed by TLS13.Record internal functions */
#ifndef TLS13_SPEC_TYPES_H
#define TLS13_SPEC_TYPES_H

/* TLS13.Record.Spec.epoch - handshake or application data epoch */
typedef enum {
  TLS13_Record_Spec_HandshakeEpoch,
  TLS13_Record_Spec_ApplicationEpoch  
} TLS13_Record_Spec_epoch;

#endif /* TLS13_SPEC_TYPES_H */
