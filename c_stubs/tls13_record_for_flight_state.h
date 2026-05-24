#ifndef TLS13_RECORD_FOR_FLIGHT_STATE_H
#define TLS13_RECORD_FOR_FLIGHT_STATE_H

#include "TLS13_Record.h"
#include "TLS13_Record_Framing.h"

#define TLS13_Record_record_state_free(st, erased) TLS13_Record_record_state_free(st)
#define TLS13_Record_install_handshake_keys_runtime(st, key, iv, erased_st, key_bytes, iv_bytes) \
    TLS13_Record_install_handshake_keys_runtime(st, key, iv)
#define TLS13_Record_seal_application_runtime(st, aad, aad_len, plain, plain_len, out, erased_st, aad_bytes, plain_bytes, old_out) \
    TLS13_Record_seal_application_runtime(st, aad, aad_len, plain, plain_len, out)
#define TLS13_Record_open_application_runtime(st, aad, aad_len, cipher, cipher_len, out, erased_st, aad_bytes, cipher_bytes, old_out) \
    TLS13_Record_open_application_runtime(st, aad, aad_len, cipher, cipher_len, out)
#define TLS13_Record_Framing_decode_inner_plaintext_no_padding(inner, inner_len, content_type_out, content_type_out_len, inner_bytes, old_content_type_out) \
    TLS13_Record_Framing_decode_inner_plaintext_no_padding(inner, inner_len, content_type_out, content_type_out_len)

#endif
