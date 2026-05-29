/**
 * calc_wrapper.h - Wrapper to fix heap allocation for server_state
 */

#ifndef CALC_WRAPPER_H
#define CALC_WRAPPER_H

#include "Calc_Server.h"

// Allocate server state on heap (fixes dangling pointer issue in extracted code)
Calc_Impl_Types_server_state* new_server_heap(void);

// Free server state
void free_server(Calc_Impl_Types_server_state *srv);

// Wrapper for process_request that takes pointer
void process_request_wrapper(Calc_Impl_Types_server_state *srv, uint8_t *req_buf, uint8_t *resp_buf);

#endif /* CALC_WRAPPER_H */
