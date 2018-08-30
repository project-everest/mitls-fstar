
//**********************************************************************************************************************************
//
//   Purpose: Component FFI stubs source code file
//
//   Project: Everest
//
//  Filename: mitlsstub.cpp
//
//   Authors: Caroline.M.Mathieson (CMM)
//
//**********************************************************************************************************************************
//
//  Description
//  -----------
//
//! \file mitlsstub.cpp
//! \brief Contains stub functions for the mitls FFI interface. This is to allow debugging without the real component.
//!
//!<pre><code>
//!
//!   The full TLS Handshake (Simplified) is:-
//!
//!      Client                                                           Server
//!        |                          ClientHello                           |
//!        |--------------------------------------------------------------->|
//!        |                                                                |
//!        |                          ServerHello                           |
//!        |<---------------------------------------------------------------|
//!        |                                                                |
//!        |                      EncryptedExtensions                       |
//!        |<---------------------------------------------------------------|
//!        |                                                                |
//!        |                      CertificateRequest                        |
//!        |<---------------------------------------------------------------|
//!        |                                                                |
//!        |                          Certificate                           |
//!        |--------------------------------------------------------------->|
//!        |                                                                |
//!        |                       CertificateVerify                        |
//!        |<---------------------------------------------------------------|
//!        |                                                                |
//!        |                       Application Data                         |
//!        |<-------------------------------------------------------------->|
//!        |                                                                |
//!
//!</code></pre>
//!
//**********************************************************************************************************************************

#include "stdafx.h"

#define USE_COMPONENT_DLL // turn on use of DLL

#ifndef USE_COMPONENT_DLL

#include "Tester.h"

#include "mitlsffi.h" // this is the real interface!

extern class TLSTESTER *Tester;

//**********************************************************************************************************************************

typedef int (MITLS_CALLCONV *pfn_FFI_send)(void *ctx, const unsigned char *buffer, size_t buffer_size);

//**********************************************************************************************************************************

typedef int (MITLS_CALLCONV *pfn_FFI_recv)(void *ctx, unsigned char *buffer, size_t buffer_size);

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_init ( void )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

void MITLS_CALLCONV FFI_mitls_cleanup ( void )
{
    Sleep ( rand () % 10 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure ( mitls_state **state,
                                         const char  *tls_version,
                                         const char  *host_name )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_set_ticket_key ( const char          *alg,
                                              const unsigned char *ticketkey,
                                              size_t               klen )
{
    Sleep ( rand () % 10 ); 

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure_cipher_suites ( mitls_state *state,
                                                       const char  *cs )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms ( mitls_state *state,
                                                              const char  *sa )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure_named_groups ( mitls_state *state,
                                                      const char  *ng )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure_alpn ( mitls_state *state,
                                              const char  *apl )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure_early_data ( mitls_state *state,
                                                    uint32_t     max_early_data )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure_ticket_callback ( mitls_state       *state,
                                                         void              *cb_state,
                                                         pfn_FFI_ticket_cb  ticket_cb )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_configure_cert_callbacks ( mitls_state   *state,
                                                        void          *cb_state,
                                                        mitls_cert_cb *cert_cb )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

void MITLS_CALLCONV FFI_mitls_close ( mitls_state *state )
{
    Sleep ( rand () % 10 );

}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_connect ( void         *send_recv_ctx,
                                       pfn_FFI_send  psend,
                                       pfn_FFI_recv  precv,
                                       mitls_state  *state )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_accept_connected ( void         *send_recv_ctx,
                                                pfn_FFI_send  psend,
                                                pfn_FFI_recv  precv,
                                                mitls_state  *state )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_get_exporter ( mitls_state  *state,
                                            int           early,
                                            mitls_secret *secret )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

void *MITLS_CALLCONV FFI_mitls_get_cert ( mitls_state *state,
                                          size_t      *cert_size )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_send ( mitls_state         *state,
                                    const unsigned char *buffer,
                                    size_t               buffer_size )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

unsigned char *MITLS_CALLCONV FFI_mitls_receive ( mitls_state *state,
                                                  size_t      *packet_size )
{
    Sleep ( rand () % 10 );

    return ( NULL );
}

//**********************************************************************************************************************************

void MITLS_CALLCONV FFI_mitls_free_packet ( mitls_state *state,
                                            void        *packet )
{
    Sleep ( rand () % 10 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_quic_create ( quic_state  **state,
                                           quic_config  *cfg )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

quic_result MITLS_CALLCONV FFI_mitls_quic_process ( quic_state          *state,
                                                    const unsigned char *inBuf,
                                                    size_t              *pInBufLen,
                                                    unsigned char       *outBuf,
                                                    size_t              *pOutBufLen )
{
    Sleep ( rand () % 10 );

    return ( ( quic_result ) 0 );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV FFI_mitls_quic_get_exporter ( quic_state  *state,
                                                 int          early,
                                                 quic_secret *secret )
{
    Sleep ( rand () % 10 );

    return ( 0 );
}

//**********************************************************************************************************************************

void MITLS_CALLCONV FFI_mitls_quic_free ( quic_state *state,
                                          void       *pv )
{
    Sleep ( rand () % 10 );
}

//**********************************************************************************************************************************

#endif USE_COMPONENT_DLL
