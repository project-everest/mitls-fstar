#include "types.h"

extern void ns_live(negotationState ns);

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
    ns_live(st);
    st = mk_client_offer();
    write_state(ctxt, st);
    return ctxt;
}

void c_offer_to_c_mode(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    ns_live(st);
    st = mk_client_mode(st.c_offer_field.n_offer);
    write_state(ctxt, st);
}

void c_offer_to_c_hrr(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    ns_live(st);
    write_state(ctxt, st);
}

// This function sets the representation directly isn't what we are trying to benchmark.
void reset_to_mode(negotationState * st) {
    *st = mk_client_mode(mk_offer());
}

// This function sets the representation directly isn't what we are trying to benchmark.
void reset_to_server_init(negotationState * st) {
    *st = mk_client_mode(mk_offer());
}

void c_mode_to_c_complete(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    ns_live(st);
    st = mk_client_complete(st.c_mode_field.n_mode);
    write_state(ctxt, st);
}

void c_mode_to_c_wait_finished2(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void c_mode_to_c_hrr(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    // // probably need to use st here or it will be optimized away
    // st = mk_client_offer();
    write_state(ctxt, st);
}

void s_init_to_s_client_hello(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    ns_live(st);
    st = mk_server_client_hello();
    write_state(ctxt, st);
}

void s_client_hello_to_s_mode(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    ns_live(st);
    st = mk_server_mode(st.server_hello_field.n_mode);
    write_state(ctxt, st);
}

void s_client_hello_to_s_complete(negotationContext ctxt) {
    negotationState st = read_state(ctxt);
    ns_live(st);
    st = mk_server_complete(st.server_mode_field.n_mode);
    write_state(ctxt, st);
}

void nego_baseline(int iterations) {
    for (int i = 0; i < iterations; i++) {
        negotationContext ctxt = mk_context();
        // Move through client state transitions.
        c_init_to_c_offer(ctxt);
        c_offer_to_c_mode(ctxt);
        c_mode_to_c_complete(ctxt);
        reset_to_mode(ctxt.state);
        c_mode_to_c_wait_finished2(ctxt);
        reset_to_mode(ctxt.state);
        c_mode_to_c_hrr(ctxt);
        reset_to_server_init(ctxt.state);
        s_init_to_s_client_hello(ctxt);
        s_client_hello_to_s_mode(ctxt);
        s_client_hello_to_s_complete(ctxt);
    }
}
