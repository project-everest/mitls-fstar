#include <stdint.h>

// TODO: fix these
typedef uint32_t random;
typedef int offer;
typedef int retryInfo;
typedef int mode;
typedef int cert;
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

// int is_valid_step(negotationState_tag t1, negotationState_tag t2) {
//     if (t1 == C_Init && t2 == C_Offer) {
//         return 1;
//     } else {

//     }
// }

typedef struct C_Init_data {
   random n_client_data;
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
    random n_server_random;
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
    negotationState_tag m_tag;
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

typedef struct negotationContext {
    config cfg;
    resumeInfo resume;
    random nonce;
    negotationState * state;
} negotationContext;
