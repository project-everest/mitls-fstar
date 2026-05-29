/**
 * calc_wrapper.c - Wrapper to fix heap allocation for server_state
 * 
 * The extracted new_server() function uses stack allocation, which causes
 * dangling pointers. This wrapper fixes it by using heap allocation.
 */

#include <stdlib.h>
#include <string.h>
#include "Calc_Server.h"

Calc_Impl_Types_server_state* new_server_heap(void)
{
    // Allocate server state on heap
    Calc_Impl_Types_server_state *srv = malloc(sizeof(Calc_Impl_Types_server_state));
    if (!srv) return NULL;
    
    // Allocate stack array on heap  
    srv->stack = malloc(10 * sizeof(uint32_t));
    if (!srv->stack) {
        free(srv);
        return NULL;
    }
    memset(srv->stack, 0, 10 * sizeof(uint32_t));
    
    // Allocate size ref on heap
    srv->size = malloc(sizeof(size_t));
    if (!srv->size) {
        free(srv->stack);
        free(srv);
        return NULL;
    }
    *srv->size = 0;
    
    return srv;
}

void free_server(Calc_Impl_Types_server_state *srv)
{
    if (srv) {
        free(srv->stack);
        free(srv->size);
        free(srv);
    }
}

void process_request_wrapper(Calc_Impl_Types_server_state *srv, uint8_t *req_buf, uint8_t *resp_buf)
{
    // Note: process_request expects server_state by value, but since it contains pointers
    // to heap-allocated data, passing the struct by value is safe.
    process_request(*srv, req_buf, resp_buf);
}
