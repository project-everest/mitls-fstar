#include "types.h"

// A synthetic set of state transition functions.
static void c_init_to_c_offer(negotationContext ctxt) {
    *ctxt.state = mk_client_offer();
}

static void c_offer_to_c_mode(negotationContext ctxt) {
    *ctxt.state = mk_client_mode(ctxt.state->c_offer_field.n_offer);
}

static void c_offer_to_c_hrr(negotationContext ctxt) {
    //todo fix me
}

// This function sets the representation directly isn't what we are trying to benchmark.
static void reset_to_offer(negotationState * st) {
    *st = mk_client_offer(mk_offer());
}

// This function sets the representation directly isn't what we are trying to benchmark.
static void reset_to_mode(negotationState * st) {
    *st = mk_client_mode(mk_offer());
}

// This function sets the representation directly isn't what we are trying to benchmark.
static void reset_to_server_init(negotationState * st) {
    *st = mk_client_mode(mk_offer());
}

static void c_mode_to_c_complete(negotationContext ctxt) {
    *ctxt.state = mk_client_complete(ctxt.state->c_mode_field.n_mode);
}

static void c_mode_to_c_wait_finished2(negotationContext ctxt) {
    *ctxt.state = mk_client_wait2(ctxt.state->c_mode_field.n_mode);
}

static void c_mode_to_c_hrr(negotationContext ctxt) {
    *ctxt.state = mk_client_hrr(mk_offer());
}

static void s_init_to_s_client_hello(negotationContext ctxt) {
    *ctxt.state = mk_server_client_hello();
}

static void s_client_hello_to_s_mode(negotationContext ctxt) {
    *ctxt.state = mk_server_mode(ctxt.state->server_hello_field.n_mode);
}

static void s_client_hello_to_s_complete(negotationContext ctxt) {
    *ctxt.state = mk_server_complete(ctxt.state->server_mode_field.n_mode);
}

void nego_state_by_ptr(int iterations) {
    for (int i = 0; i < iterations; i++) {
        negotationContext ctxt = mk_context();
        // Move through client state transitions.
        c_init_to_c_offer(ctxt);
        c_offer_to_c_mode(ctxt);
        c_mode_to_c_complete(ctxt);
        reset_to_mode(ctxt.state);
        c_mode_to_c_wait_finished2(ctxt);
        reset_to_offer(ctxt.state);
        c_mode_to_c_hrr(ctxt);
        reset_to_server_init(ctxt.state);
        s_init_to_s_client_hello(ctxt);
        s_client_hello_to_s_mode(ctxt);
        s_client_hello_to_s_complete(ctxt);
    }
}
