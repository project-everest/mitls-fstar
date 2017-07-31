#include "types.h"

extern negotationState ns_identity(negotationState ns);

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

void c_offer_to_c_mode(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void c_offer_to_c_complete(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void c_mode_to_c_wait_finished2(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void c_mode_to_complete(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void s_init_to_s_client_Hello(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void s_client_hello_to_s_mode(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void nego_baseline(int iterations) {
    for (int i = 0; i < iterations; i++) {
        negotationContext ctxt = mk_context();
        // Move through client state transitions.
        c_init_to_c_offer(ctxt);
        c_offer_to_c_mode(ctxt);
    }
}
