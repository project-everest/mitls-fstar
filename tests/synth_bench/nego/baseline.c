#include <stdlib.h>
#include <stdint.h>

// TODO: fix these
typedef uint8_t random_bytes[32];

// Fill an array with random bytes.
void mk_random_bytes(random_bytes arr) {
    int i = 0;
    for (; i < 32; i++) {
        arr[i] = rand() % 256;
    }
}

typedef int sessionID;

// Not sure about this one
typedef uint8_t valid_cipher_suite[32];

void mk_cipher_suite(valid_cipher_suite cipher) {
    int i = 0;
    for (; i < 32; i++) {
        cipher[i] = rand() % 256;
    }
}

void mk_cipher_suites(valid_cipher_suite * arr) {
    int i = 0;
    for (; i < 256; i++) {
        mk_cipher_suite(arr[i]);
    }
}

typedef int compression;

void mk_compressions(compression * arr) {
    int i = 0;
    for (; i < 256; i++) {
        arr[i] = rand();
    }
}

typedef struct offer {
  // ch_protocol_version: protocolVersion;  // max supported version up to TLS_1p2 (TLS 1.3 uses the supported_versions extension)
  random_bytes ch_client_random;
  sessionID h_sessionID;
  valid_cipher_suite ch_cipher_suites[256];
  compression ch_compressions[256];
  // ch_extensions: option (ce:list extension{List.Tot.length ce < 256});
} offer;

offer mk_offer() {
    offer o;
    mk_random_bytes(o.ch_client_random);
    o.h_sessionID = 10;
    mk_cipher_suites(o.ch_cipher_suites);
    mk_compressions(o.ch_compressions);
    return o;
}

typedef int retryInfo;
typedef int mode;
typedef int cert;

// do we need these?
typedef int config;
typedef int resumeInfo;

typedef enum negotationState_tag {
    C_Init,
    C_Offer,
    C_HRR,
    C_WaitFinished1,
    C_Mode,
    C_WaitFinished2,
    C_Complete,
    S_Init,
    S_HRR,
    S_CientHello,
    S_Mode,
    S_Complete
} negotationState_tag;

typedef struct C_Init_data {
   random_bytes n_client_data;
} C_Init_data;

typedef struct C_Offer_data {
    offer n_offer;
} C_Offer_data;

typedef struct C_HRR_data {
    offer n_offer;
    retryInfo n_hrr;
} C_HRR_data;

typedef struct C_WaitFinished1_data {
    mode n_partial_mode;
} C_WaitFinished1_data;

typedef struct C_Mode_data {
    mode n_mode;
} C_Mode_data;

typedef struct C_WaitFinished2_data {
    mode n_partial_mode;
    cert n_client_certificate;
} C_WaitFinished2_data;

typedef struct C_Complete_data {
    mode n_mode;
    cert n_client_certificate;
} C_Complete_data;

typedef struct S_Init_data {
    random_bytes n_server_random;
} S_Init_data;

typedef struct S_HRR_data {
   offer n_offer;
   retryInfo n_hrr;
} S_HRR_data;

typedef struct S_ClientHello_data {
    mode n_mode;
} S_ClientHello_data;

typedef struct S_Mode_data {
    mode n_mode;
} S_Mode_data;

typedef struct S_Complete_data {
    mode n_mode;
    cert n_client_certificate;
} S_Complete_data;

typedef struct negotationState {
    negotationState_tag tag;
    union {
        C_Init_data c_init_field;
        C_Offer_data c_offer_field;
        C_HRR_data c_hrr_field;
        C_WaitFinished1_data c_wait_finished1_field;
        C_Mode_data c_mode_field;
        C_WaitFinished2_data c_wait_finished2_field;
        C_Complete_data c_complete_field;
        S_Init_data server_init_field;
        S_HRR_data server_hrr_field;
        S_ClientHello_data server_hello_field;
        S_Mode_data server_mode_field;
        S_Complete_data server_complete_field;
    };
} negotationState;

negotationState mk_client_init() {
    negotationState st;
    st.tag = C_Init;
    C_Init_data * data = &st.c_init_field;
    mk_random_bytes(data->n_client_data);
    return st;
}

negotationState mk_client_offer() {
    negotationState st;
    st.tag = C_Offer;
    C_Offer_data * data = &st.c_offer_field;
    data->n_offer = mk_offer();
    return st;
}

typedef struct negotationContext {
    // config cfg; Do we care about this?
    // resumeInfo resume;
    // random_bytes nonce;
    negotationState * state;
} negotationContext;

negotationContext mk_context() {
    negotationContext ctxt;
    ctxt.state = (negotationState*)(malloc(sizeof(negotationState)));
    // ctxt.cfg = 0;
    return ctxt;
}

negotationState read_state(negotationContext ctxt) {
    return *ctxt.state;
}

negotationContext write_state(negotationContext ctxt, negotationState st) {
    *ctxt.state = st;
    return ctxt;
}

// A synthetic set of state transition functions.
negotationContext c_init_to_c_offer(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // probably need to use st here or it will be optimized away
    st = mk_client_offer();
    write_state(ctxt, st);
    return ctxt;
}

negotationContext c_offer_to_c_mode(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
    return ctxt;
}

// let ns_step (#r:role) (#cfg:config) (#resume:resumeInfo r)
//   (ns:negotiationState r cfg resume) (ns':negotiationState r cfg resume) =
//   match ns, ns' with
//   | C_Init nonce, C_Offer offer -> nonce == offer.ch_client_random
//   | C_Offer offer, C_Mode mode -> mode.n_offer == offer
//   | C_Offer _, C_Complete _ _ -> True
//   | C_Mode _, C_WaitFinished2 _ _ -> True
//   | C_Mode _, C_Complete _ _ -> True
//   | S_Init _, S_ClientHello _ -> True
//   | S_ClientHello _, S_Mode _ -> True
//   | _, _ -> ns == ns'


negotationContext c_offer_to_c_complete(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
    return ctxt;
}

void nego_baseline(int iterations) {
    for (int i = 0; i < iterations; i++) {
        negotationContext ctxt = mk_context();
        // Move through client state transitions.
        ctxt = c_init_to_c_offer(ctxt);
    }
}
