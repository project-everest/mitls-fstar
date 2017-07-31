#include "types.h"

// Fill an array with random bytes.
void mk_random_bytes(random_bytes arr) {
    int i = 0;
    for (; i < 32; i++) {
        arr[i] = rand() % 256;
    }
}

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

void mk_compressions(compression * arr) {
    int i = 0;
    for (; i < 256; i++) {
        arr[i] = rand();
    }
}

offer mk_offer() {
    offer o;
    mk_random_bytes(o.ch_client_random);
    o.h_sessionID = 10;
    mk_cipher_suites(o.ch_cipher_suites);
    mk_compressions(o.ch_compressions);
    return o;
}

//TODO: flesh out config
config mk_config() {
    return 0;
}

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

negotationContext mk_context() {
    negotationContext ctxt;
    ctxt.cfg = mk_config();
    ctxt.state = (negotationState*)(malloc(sizeof(negotationState)));
    return ctxt;
}

// TODO: flesh out
mode mk_mode(offer n_offer) {
    mode m;
    m.n_offer = n_offer;
    return m;
}

negotationState mk_client_mode(offer n_offer) {
    negotationState st;
    st.tag = C_Mode;
    st.c_mode_field.n_mode = mk_mode(n_offer);
    return st;
}

negotationState mk_client_complete(mode n_mode) {
    negotationState st;
    st.tag = C_Complete;
    st.c_mode_field.n_mode = n_mode;
    return st;
}

negotationState mk_client_(offer n_offer) {
    negotationState st;
    st.tag = C_Complete;
    st.c_mode_field.n_mode = mk_mode(n_offer);
    return st;
}
