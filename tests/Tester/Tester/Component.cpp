
//**********************************************************************************************************************************
//
//   Purpose: Component, Library and Measurement implementation source code file
//
//   Project: Everest
//
//  Filename: Component.cpp
//
//   Authors: Caroline.M.Mathieson (CMM)
//
//**********************************************************************************************************************************
//
//  Description
//  -----------
//
//! \file Component.cpp
//! \brief Contains the complete implementation of the COMPONENT Object.
//!
//! The COMPONENT object encapsulates two dlls, the "libmitls.dll" which provides the TLS/QUIC handshake, and the "libmipki.dll"
//! which provides certificate handling. The two have to be used in conjunction and they communicate with each other. In fact these
//! two dlls require the presence of the libquiccrypto.dll as well. The performance of each DLL will impact the others, so each must
//! be instrumented and measured. In addition, each DLL uses callbacks and these callbacks must be instrumented and measured as well
//! to measure and eliminate the time spent in the tester code.
//!
//**********************************************************************************************************************************

#include "Tester.h" // pulls in everything else

//**********************************************************************************************************************************

extern class TLSTESTER *Tester; // to give access to the component instance(s) for callbacks!!

//**********************************************************************************************************************************

static unsigned char LargeTransmitBuffer [ 65536 ]; // almost the maximum packet the network will transmit in one go
static unsigned char LargeReceiveBuffer  [ 65536 ]; // almost the maximum packet the network will receive in one go

static unsigned int LargeTransmitBufferReadIndex = 0;
static unsigned int LargeReceiveBufferReadIndex  = 0;

static int AmountTransmitted = 0;
static int AmountReceived    = 0;

static bool IncompleteTransmission = FALSE;
static bool IncompleteTransfer     = FALSE;

static unsigned int ExpectedRecordLength = 0;

static TRANSFER_BUFFER SendBuffer;
static TRANSFER_BUFFER ReceiveBuffer;

//**********************************************************************************************************************************

const char *MeasurementTypeNames [] =  // must be in the same order as the enumerated types
{
    "TLS Client Measurements",       // TLS_CLIENT_MEASUREMENTS,
    "QUIC Client Measurements",      // QUIC_CLIENT_MEASUREMENTS,
    "TLS Server Measurements",       // TLS_SERVER_MEASUREMENTS,
    "QUIC Server Measurements",      // QUIC_SERVER_MEASUREMENTS,
    "OPENSSL Server Measurements",   // OPENSSL_SERVER_MEASUREMENTS,
    "BORINGSSL Server Measurements", // BORINGSSL_SERVER_MEASUREMENTS,
    "MBEDTLS Server Measurements",   // MBEDTLS_SERVER_MEASUREMENTS,
    "WOLFSSL Server Measurements",   // WOLFSSL_SERVER_MEASUREMENTS,
    "FIZZ Server Measurements",      // FIZZ_SERVER_MEASUREMENTS,
    "OPENSSL Client Measurements",   // OPENSSL_CLIENT_MEASUREMENTS,
    "BORINGSSL Client Measurements", // BORINGSSL_CLIENT_MEASUREMENTS,
    "MBEDTLS Client Measurements",   // MBEDTLS_CLIENT_MEASUREMENTS,
    "WOLFSSL Client Measurements",   // WOLFSSL_CLIENT_MEASUREMENTS,
    "FIZZ Client Measurements",      // FIZZ_CLIENT_MEASUREMENTS,
};

const char *FFIMeasurementEntryNames [ MAX_FFI_FUNCTIONS ] = // must be in the same order as the enumerated types
{
    // TLS API functions

    "FFI_mitls_init",                           // FFI_MITLS_INIT,
    "FFI_mitls_configure",                      // FFI_MITLS_CONFIGURE,
    "FFI_mitls_set_ticket_key",                 // FFI_MITLS_SET_TICKET_KEY,
    "FFI_mitls_configure_ticket",               // FFI_MITLS_CONFIGURE_TICKET
    "FFI_mitls_configure_cipher_suites",        // FFI_MITLS_CONFIGURE_CIPHER_SUITES,
    "FFI_mitls_configure_signature_algorithms", // FFI_MITLS_CONFIGURE_SIGNATURE_ALGORITHMS,
    "FFI_mitls_configure_named_groups",         // FFI_MITLS_CONFIGURE_NAMED_GROUPS,
    "FFI_mitls_configure_alpn",                 // FFI_MITLS_CONFIGURE_ALPN,
    "FFI_mitls_configure_early_data",           // FFI_MITLS_CONFIGURE_EARLY_DATA,
    "FFI_mitls_configure_custom_extensions",    // FFI_MITLS_CONFIGURE_CUSTOM_EXTENSIONS
    "FFI_mitls_configure_ticket_callback",      // FFI_MITLS_CONFIGURE_TICKET_CALLBACK,
    "FFI_mitls_configure_nego_callback",        // FFI_MITLS_CONFIGURE_NEGO_CALLBACK
    "FFI_mitls_configure_cert_callbacks",       // FFI_MITLS_CONFIGURE_CERT_CALLBACKS,
    "FFI_mitls_close",                          // FFI_MITLS_CLOSE,
    "FFI_mitls_connect",                        // FFI_MITLS_CONNECT,
    "FFI_mitls_accept_connected",               // FFI_MITLS_ACCEPT_CONNECTED,
    "FFI_mitls_get_exporter",                   // FFI_MITLS_GET_EXPORTER,
    "FFI_mitls_get_cert",                       // FFI_MITLS_GET_CERT,
    "FFI_mitls_send",                           // FFI_MITLS_SEND,
    "FFI_mitls_receive",                        // FFI_MITLS_RECEIVE,
    "FFI_mitls_free",                           // FFI_MITLS_FREE,
    "FFI_mitls_cleanup",                        // FFI_MITLS_CLEANUP,
    "FFI_mitls_set_trace_callback",             // FFI_MITLS_SET_TRACE_CALLBACK,

    // QUIC API functions

    "FFI_mitls_quic_create",           // FFI_MITLS_QUIC_CREATE,
    "FFI_mitls_quic_process",          // FFI_MITLS_QUIC_PROCESS,
    "FFI_mitls_quic_get_exporter",     // FFI_MITLS_QUIC_GET_EXPORTER,
    "FFI_mitls_quic_close",            // FFI_MITLS_QUIC_CLOSE
    "FFI_mitls_get_hello_summary",     // FFI_MITLS_GET_HELLO_SUMMARY,
    "FFI_mitls_find_custom_extension", // FFI_MITLS_FIND_CUSTOM_EXTENSION,
    "FFI_mitls_global_free"            // FFI_MITLS_GLOBAL_FREE,
};

const char *FFICallbackMeasurementEntryNames [ MAX_FFI_CALLBACK_FUNCTIONS ] = // must be in the same order as the enumerated types
{
    // TLS Callback functions

    "FFI_mitls_send_callback",    // FFI_MITLS_SEND_CALLBACK
    "FFI_mitls_receive_callback", // FFI_MITLS_RECEIVE_CALLBACK

    "FFI_mitls_certificate_select_callback", // FFI_MITLS_CERTIFICATE_SELECT_CALLBACK
    "FFI_mitls_certificate_format_callback", // FFI_MITLS_CERTIFICATE_FORMAT_CALLBACK
    "FFI_mitls_certificate_sign_callback",   // FFI_MITLS_CERTIFICATE_SIGN_CALLBACK
    "FFI_mitls_certificate_verify_callback", // FFI_MITLS_CERTIFICATE_VERIFY_CALLBACK

    "FFI_mitls_ticket_callback",      // FFI_MITLS_TICKET_CALLBACK
    "FFI_mitls_negotiation_callback", // FFI_MITLS_NEGOTIATION_CALLBACK
    "FFI_mitls_trace_callback"        // FFI_MITLS_TRACE_CALLBACK
};

const char *PKIMeasurementEntryNames [ MAX_PKI_FUNCTIONS ] = // must be in the same order as the enumerated types
{
    "mipki_init",                  // MIPKI_INIT,
    "mipki_free",                  // MIPKI_FREE,
    "mipki_add_root_file_or_path", // MIPKI_ADD_ROOT_FILE_OR_PATH,
    "mipki_select_certificate",    // MIPKI_SELECT_CERTIFICATE,
    "mipki_sign_verify",           // MIPKI_SIGN_VERFIY,
    "mipki_parse_chain",           // MIPKI_PARSE_CHAIN,
    "mipki_parse_list",            // MIPKI_PARSE_LIST,
    "mipki_format_chain",          // MIPKI_FORMAT_CHAIN,
    "mipki_format_alloc",          // MIPKI_FORMAT_ALLOC,
    "mipki_validate_chain",        // MIPKI_VALIDATE_CHAIN,
    "mipki_free_chain"             // MIPKI_FREE_CHAIN,
};

const char *PKICallbackMeasurementEntryNames [ MAX_PKI_CALLBACK_FUNCTIONS ] = // must be in the same order as the enumerated types
{
    "mipki_password_callback", // MIPKI_PASSWORD_CALLBACK
    "mipki_alloc_callback"     // MIPKI_ALLOC_CALLBACK
};

//**********************************************************************************************************************************
//
// Buffer Functions
//
//**********************************************************************************************************************************

void BufferInitialise ( TRANSFER_BUFFER *TransferBuffer )
{
#ifdef WIN32
    InitializeCriticalSection ( &TransferBuffer->CriticalSection );
#endif
    memset ( TransferBuffer->Buffer, 0, TRANSFER_BUFFER_SIZE );

    TransferBuffer->ReadPointer  = TransferBuffer->Buffer;
    TransferBuffer->WritePointer = TransferBuffer->Buffer;

    TransferBuffer->ReadIndex  = 0;
    TransferBuffer->WriteIndex = 0;

    TransferBuffer->TotalAmountWritten = 0;
    TransferBuffer->TotalAmountRead    = 0;
}

//**********************************************************************************************************************************

unsigned long BufferWrite ( TRANSFER_BUFFER *TransferBuffer, unsigned char *Buffer, unsigned long BufferSize )
{
#ifdef WIN32
    EnterCriticalSection ( &TransferBuffer->CriticalSection );
#endif
    // write the data into the buffer if there is room

    if ( ( TransferBuffer->WriteIndex + BufferSize ) < TRANSFER_BUFFER_SIZE )
    {
        memcpy ( (void *) TransferBuffer->WritePointer, (const void *) Buffer, BufferSize );

        DumpPacket ( Buffer, BufferSize, 0 , 0, "Buffer Write" );

        TransferBuffer->WritePointer += BufferSize;

        TransferBuffer->WriteIndex += BufferSize;

        TransferBuffer->TotalAmountWritten += BufferSize;
    }
    else
    {
        fprintf ( stderr, "Transfer Buffer is full!\n" );

        BufferSize = 0;
    }

#ifdef WIN32
    LeaveCriticalSection ( &TransferBuffer->CriticalSection );
#endif

    return ( BufferSize );
}

//**********************************************************************************************************************************

unsigned long BufferRead ( TRANSFER_BUFFER *TransferBuffer, unsigned char *Buffer, unsigned long BufferSize )
{
    unsigned int AmountRead = 0;

    // make this a blocking call!

    do
    {
#ifdef WIN32
        EnterCriticalSection ( &TransferBuffer->CriticalSection );
#endif
        if ( ( TransferBuffer->WriteIndex - TransferBuffer->ReadIndex ) >= BufferSize ) // is there enough data to read?
        {
            memcpy ( Buffer, TransferBuffer->ReadPointer, BufferSize );

            DumpPacket ( Buffer, BufferSize, 0 , 0, "Buffer Read" );

            TransferBuffer->ReadPointer += BufferSize;

            TransferBuffer->ReadIndex += BufferSize;

            TransferBuffer->TotalAmountRead += BufferSize;

            AmountRead = BufferSize;

            //// if the indices are now the same then reset them
            //
            //if ( TransferBuffer->WriteIndex == TransferBuffer->ReadIndex )
            //{
            //   BufferReset ( TransferBuffer );
            //}
        }

#ifdef WIN32
        LeaveCriticalSection ( &TransferBuffer->CriticalSection );
#endif

    } while ( AmountRead == 0 );

    return ( AmountRead );
}

//**********************************************************************************************************************************

void BufferReset ( TRANSFER_BUFFER *TransferBuffer )
{
    TransferBuffer->WritePointer = TransferBuffer->Buffer;
    TransferBuffer->ReadPointer  = TransferBuffer->Buffer;

    TransferBuffer->WriteIndex = 0;
    TransferBuffer->ReadIndex  = 0;
}

//**********************************************************************************************************************************
//
// FFI Callback Function wrappers
//
//**********************************************************************************************************************************

CALLBACKMEASUREMENTENTRY *GetFFICallbackMeasurement ( unsigned int   CallBackNumber,
                                                      COMPONENT    **Component )
{
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;

    DWORD CurrentThreadId = GetCurrentThreadId (); // which thread is running?

    if ( CurrentThreadId == Tester->ClientTLSTestsThreadIdentifier )
    {
        FFICallbackMeasurement = &Tester->
                                  ClientComponent->
                                  MeasurementResultsArray [ Tester->ClientComponent->TestRunNumber ]->
                                  Measurements [ Tester->ClientComponent->MeasurementNumber ].
                                  FFICallbackMeasurements [ CallBackNumber ];

        *Component = Tester->ClientComponent;
    }
    else
    {
        FFICallbackMeasurement = &Tester->
                                  ServerComponent->
                                  MeasurementResultsArray [ Tester->ServerComponent->TestRunNumber ]->
                                  Measurements [ Tester->ServerComponent->MeasurementNumber ].
                                  FFICallbackMeasurements [ CallBackNumber ];

        *Component = Tester->ServerComponent;
    }

    return ( FFICallbackMeasurement );
}

//**********************************************************************************************************************************

CALLBACKMEASUREMENTENTRY *GetPKICallbackMeasurement ( unsigned int   CallBackNumber,
                                                      COMPONENT    **Component )
{
    CALLBACKMEASUREMENTENTRY *PKICallbackMeasurement = NULL;

    DWORD CurrentThreadId = GetCurrentThreadId (); // which thread is running?

    if ( CurrentThreadId == Tester->ClientTLSTestsThreadIdentifier )
    {
        PKICallbackMeasurement = &Tester->
                                  ClientComponent->
                                  MeasurementResultsArray [ Tester->ClientComponent->TestRunNumber ]->
                                  Measurements [ Tester->ClientComponent->MeasurementNumber ].
                                  PKICallbackMeasurements [ CallBackNumber ];

        *Component = Tester->ClientComponent;
    }
    else
    {
        PKICallbackMeasurement = &Tester->
                                  ServerComponent->
                                  MeasurementResultsArray [ Tester->ServerComponent->TestRunNumber ]->
                                  Measurements [ Tester->ServerComponent->MeasurementNumber ].
                                  PKICallbackMeasurements [ CallBackNumber ];

        *Component = Tester->ServerComponent;
    }

    return ( PKICallbackMeasurement );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV ClientSendCallback ( void                *Context,
                                        const unsigned char *Buffer,
                                        size_t               BufferSize )
{
    size_t                    AmountSent             = 0;
    COMPONENT                *Component              = ( COMPONENT * ) Context;
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_SEND_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    if ( Tester->ConsoleDebugging ) printf ( "Client Send callback function invoked for %zd octets!\n", BufferSize );

    // The component sends the records in sections now (Aug 2018) so we have to send this right away

    if ( Tester->ServerTLSTestsThreadIdentifier != 0 ) // if we are running server tests then use buffers
    {
        AmountSent = BufferWrite ( &ReceiveBuffer, (unsigned char *) Buffer, BufferSize );
    }
    else
    {
        AmountSent = send ( Component->Socket, (char * ) Buffer, (int) BufferSize, 0 );
    }

    // if console debugging is enabled then accumulate the network packets and then decode them

    if ( Tester->ConsoleDebugging )
    {
        if ( AmountSent == 0 )
        {
            printf ( "Socket Closed!\n" );
        }
        else
        {
            // append to temporary decoder buffer

            memcpy ( (void *) &LargeTransmitBuffer [ LargeTransmitBufferReadIndex ], (const void *) Buffer, BufferSize );

            LargeTransmitBufferReadIndex += BufferSize;

            AmountTransmitted += BufferSize;

            if ( IncompleteTransmission == FALSE )
            {
                if ( AmountSent == 5 ) // just the header was sent first (API change August 2018)
                {
                    // peek into message to get record length if its a TLS handshake record

                    TLS_RECORD *TLSRecord = (TLS_RECORD *) Buffer;

                    if ( TLSRecord->RecordHeader.ContentType == TLS_CT_HANDSHAKE )
                    {
                        ExpectedRecordLength = ( TLSRecord->RecordHeader.ContentLengthHigh * 256 ) + TLSRecord->RecordHeader.ContentLengthLow;

                        IncompleteTransmission = TRUE; // we will need to get the rest before decoding
                    }
                    else
                    {
                        if ( TLSRecord->RecordHeader.ContentType == TLS_CT_ALERT )
                        {
                            DecodePacket ( (void *) LargeTransmitBuffer, BufferSize, "Packet sent to server" );

                            // reset decoder buffer as we know what this is

                            LargeTransmitBufferReadIndex = 0;

                            AmountTransmitted = 0;
                        }
                    }
                }
            }
            else
            {
                // do we have enough to decode it yet?

                if ( AmountTransmitted >= ExpectedRecordLength )
                {
                    DecodePacket ( (void *) LargeTransmitBuffer, BufferSize, "Packet sent to server" );

                    // reset decoder buffer

                    LargeTransmitBufferReadIndex = 0;

                    AmountTransmitted = 0;

                    ExpectedRecordLength = 0;

                    IncompleteTransmission = FALSE;
                }
            }
        }

    } // if ConsoleDebugging

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( (int) AmountSent );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV ServerSendCallback ( void                *Context,
                                        const unsigned char *Buffer,
                                        size_t               BufferSize )
{
    size_t                    AmountSent             = 0;
    COMPONENT                *Component              = ( COMPONENT * ) Context;
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_SEND_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    if ( Tester->ConsoleDebugging ) printf ( "Server Send callback function invoked for %zd octets!\n", BufferSize );

    // copy the record into the send buffer if there is room

    AmountSent = BufferWrite ( &SendBuffer, (unsigned char *) Buffer, BufferSize );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

   return ( AmountSent );
}

//**********************************************************************************************************************************
// PROBLEM: MITLS requests data from the server in sections. It reads the header first and then depending on the fragment length,
//          reads that fragment. However this makes debugging very difficult as the whole record is needed for this. The solution
//          is to read the complete response from the peer and then return it bit by bit as requested by MITLS. So the call back
//          function will read the data from a local buffer rather than from the network buffer.
//

int MITLS_CALLCONV ClientReceiveCallback ( void          *Context,
                                           unsigned char *Buffer,
                                           size_t         BufferSize )
{
    size_t                    AmountTransferred      = 0;
    size_t                    AmountRemaining        = 0;
    COMPONENT                *Component              = ( COMPONENT * ) Context;
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_RECEIVE_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    // if console debugging is enabled then we need to buffer the network packet to decode it and return only the requested amount.

    if ( Tester->ConsoleDebugging )
    {
        printf ( "Client Receive callback function invoked (with room for %zu octets)!\n", BufferSize );

        // yes, so did the previous call result in an incomplete transfer?

        if ( IncompleteTransfer == FALSE )
        {
            // No, so get as much as the network will provide

            LargeReceiveBufferReadIndex = 0;

            AmountReceived = recv ( Component->Socket, (char * ) LargeReceiveBuffer, sizeof ( LargeReceiveBuffer ), 0 );

            if ( AmountReceived > 0 )
            {
                IncompleteTransfer = TRUE;

                // we only decode the packet the first time round and if console debuggin is enabled!

                DecodePacket ( (void *) LargeReceiveBuffer, AmountReceived, "Packet received from server" );
            }
        }

        // webservers such as bing.com will go mute when you specify a valid but old cipher suite in the clienthello which means that
        // the call to recv() will timeout and an error returned such as "connection reset by peer". So we have to test for this but we
        // also need to indicate back to the component that it has happened, so that it finishes the ffi_mitls_connect() call.

        if ( AmountReceived == -1 )
        {
            PrintSocketError ();

            return ( AmountReceived ); // let libmitls.dll know what has happened
        }

        if ( AmountReceived == 0 )
        {
            printf ( "Socket Closed!\n" );

            IncompleteTransfer = FALSE;
        }
        else
        {
            AmountRemaining = AmountReceived - LargeReceiveBufferReadIndex;

            if ( AmountRemaining > BufferSize )
            {
                memcpy ( Buffer, &LargeReceiveBuffer [ LargeReceiveBufferReadIndex ], BufferSize );

                AmountTransferred = BufferSize;

                IncompleteTransfer = TRUE; // still more left so still incomplete
            }
            else
            {
                memcpy ( Buffer, &LargeReceiveBuffer [ LargeReceiveBufferReadIndex ], AmountRemaining );

                AmountTransferred = AmountRemaining;

                IncompleteTransfer = FALSE; // no more left now so transfer complete
            }

            LargeReceiveBufferReadIndex += AmountTransferred;
        }
    }
    else
    {
        // no, so just return the amount requested from the network

        if ( Tester->ServerTLSTestsThreadIdentifier != 0 ) // if we are running server tests then use buffers
        {
            // read from the send buffer

            AmountTransferred = BufferRead ( &SendBuffer, Buffer, BufferSize );
        }
        else
        {
            // read from the network socket

            AmountTransferred = recv ( Component->Socket, (char * ) Buffer, BufferSize, 0 );
        }
    }

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( AmountTransferred );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV ServerReceiveCallback ( void          *Context,
                                           unsigned char *Buffer,
                                           size_t         BufferSize )
{
    size_t                    AmountTransferred      = 0;
    size_t                    AmountRemaining        = 0;
    COMPONENT                *Component              = ( COMPONENT * ) Context;
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_RECEIVE_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    if ( Tester->ConsoleDebugging )
    {
        printf ( "Server Receive callback function invoked (with room for %zu octets)!\n", BufferSize );
    }

    // intended behaviour is that this should be blocking

    do
    {
        AmountTransferred = BufferRead ( &ReceiveBuffer, (unsigned char *) Buffer, BufferSize );

    } while ( AmountTransferred == 0 );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

   return ( AmountTransferred );
}

//**********************************************************************************************************************************

void MITLS_CALLCONV TicketCallback ( void               *cb_state,
                                     const char         *sni,
                                     const mitls_ticket *ticket )
{
    COMPONENT                *Component              = NULL;
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_TICKET_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Ticket callback function invoked!\n" );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }
}

//**********************************************************************************************************************************

mitls_nego_action MITLS_CALLCONV NegotiationCallback ( void                 *cb_state,
                                                       mitls_version         ver,
                                                       const unsigned char  *exts,
                                                       size_t                exts_len,
                                                       mitls_extension     **custom_exts,
                                                       size_t               *custom_exts_len,
                                                       unsigned char       **cookie,
                                                       size_t               *cookie_len )
{
    COMPONENT                *Component                 = NULL; // the component using this dll and callback
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement    = NULL;
    unsigned int              CallCount                 = 0;
  //unsigned char            *TransportParameters       = NULL;
  //unsigned long             TransportParametersLength = 0;
  //unsigned int              Result                    = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_NEGOTIATION_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Negotiation callback function invoked!\n" );

    // check first if there was an extension for QUIC transport parameters even if this was not a QUIC test

    // Result = Component->FindCustomExtension ( 1, exts, exts_len, TLS_ET_QUIC_TRANSPORT_PARAMETERS, &TransportParameters, &TransportParametersLength );

    *custom_exts_len = 0; *custom_exts = NULL;

    *cookie = ( unsigned char * ) "Hello TLS World"; *cookie_len = 15;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( TLS_nego_accept );
}

//**********************************************************************************************************************************

void MITLS_CALLCONV TraceCallback ( const char *msg )
{
    DWORD CurrentThreadId = GetCurrentThreadId (); // which thread is running?

    printf ( ASES_SET_FOREGROUND_YELLOW );

    if ( CurrentThreadId == Tester->ClientTLSTestsThreadIdentifier )
    {
        printf ( "Client Traced: %s", msg );
    }
    else
    {
        printf ( "Server Traced: %s", msg );
    }

    printf ( ASES_SET_FOREGROUND_BLACK );
}

//**********************************************************************************************************************************

void *MITLS_CALLCONV CertificateSelectCallback ( void                         *State,
                                                 mitls_version                 TLSVersion,                         // not used below
                                                 const unsigned char          *ServerNameIndicator,
                                                 size_t                        ServerNameIndicatorLength,
                                                 const unsigned char          *ApplicationLevelProtocolName,       // not used below
                                                 size_t                        ApplicationLevelProtocolNameLength, // not used below
                                                 const mitls_signature_scheme *SignatureAlgorithms,
                                                 size_t                        SignatureAlgorithmsLength,
                                                 mitls_signature_scheme       *SelectedSignature )
{
    COMPONENT                *Component              = NULL; // the component using this dll and callback
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_CERTIFICATE_SELECT_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Select Callback function invoked!\n" );

    mipki_chain Chain = Component->SelectCertificate ( (mipki_state *) State,
                                                       ServerNameIndicator,
                                                       ServerNameIndicatorLength,
                                                       SignatureAlgorithms,
                                                       SignatureAlgorithmsLength,
                                                       SelectedSignature );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( (void *) Chain );
}

//**********************************************************************************************************************************

size_t MITLS_CALLCONV CertificateFormatCallback ( void          *State,
                                                  const void    *ChainOfTrust,
                                                  unsigned char  ChainBuffer [ MAX_CHAIN_LEN ] )
{
    COMPONENT                *Component              = NULL; // the component using this dll and callback
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_CERTIFICATE_FORMAT_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Format Callback function invoked!\n" );

    size_t Result = Component->FormatChain ( (mipki_state *) State,
                                             (mipki_chain) ChainOfTrust,
                                             ChainBuffer,
                                             MAX_CHAIN_LEN );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( Result );
}

//**********************************************************************************************************************************

size_t MITLS_CALLCONV CertificateSignCallback ( void                         *State,
                                                const void                   *CertificatePointer,
                                                const mitls_signature_scheme  SignatureAlgorithm,
                                                const unsigned char          *Certificate,
                                                size_t                        CertificateLength,
                                                unsigned char                *Signature )
{
    COMPONENT                *Component               = NULL; // the component using this dll and callback
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement  = NULL;
    unsigned int              CallCount               = 0;
    size_t                    VerifiedSignatureLength = MAX_SIGNATURE_LEN; // signal the maximum before signing (was 0)

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_CERTIFICATE_SIGN_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Sign Callback function invoked!\n" );

    int Result = Component->SignCertificate ( (mipki_state *) State,
                                              CertificatePointer,
                                              SignatureAlgorithm,
                                              (const char *) Certificate,
                                              CertificateLength,
                                              (char *) Signature,
                                              &VerifiedSignatureLength );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( VerifiedSignatureLength );
}

//**********************************************************************************************************************************

int MITLS_CALLCONV CertificateVerifyCallback ( void                         *State,
                                               const unsigned char          *ChainOfTrust,       // the certificate chain of trust
                                               size_t                        ChainLength,        // how many entries are in the chain
                                               const mitls_signature_scheme  SignatureAlgorithm, // what signature algorithm was used to sign it
                                               const unsigned char          *Certificate,        // the certificate to be verified (tbs)
                                               size_t                        CertificateLength,  // how long it is in octets
                                               const unsigned char          *Signature,          // the signature
                                               size_t                        SignatureLength )   // how long the signature is in octets
{
    COMPONENT                *Component               = NULL; // the component using this dll and callback
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement  = NULL;
    unsigned int              CallCount               = 0;
    int                       Result                  = 0;
    size_t                    VerifiedSignatureLength = SignatureLength;

    FFICallbackMeasurement = GetFFICallbackMeasurement ( FFI_MITLS_CERTIFICATE_VERIFY_CALLBACK, &Component );

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    if ( Tester->ConsoleDebugging ) printf ( "Certificate Verify Callback function invoked!\n" );

    //bool Supported = FALSE;
    //
    //const char *SignatureAlgorithmName = LookupSignatureAlgorithm ( SignatureAlgorithm, &Supported );
    //
    //printf ( "             State = 0x%08X\n",     State             );
    //printf ( "      ChainOfTrust = 0x%08X\n",     ChainOfTrust      );
    //printf ( "       ChainLength = %zd octets\n", ChainLength       );
    //
    //printf ( "SignatureAlgorithm = 0x%04X (%s), Supported = %d\n", SignatureAlgorithm, SignatureAlgorithmName, Supported );
    //
    //printf ( "       Certificate = 0x%08X\n",     Certificate       );
    //printf ( " CertificateLength = %zd octets\n", CertificateLength );
    //printf ( "         Signature = 0x%08X\n",     Signature         );
    //printf ( "   SignatureLength = %zd octets\n", SignatureLength   );

    // verification requires us to first parse the chain of trust. If all is well, then we use the library to verify the certificate
    // which is why there are so many parameters to this callback

    int ChainNumber = Component->ParseChain ( (mipki_state *) State, (const char *) ChainOfTrust, ChainLength );

    if ( Component->CertificateChains [ ChainNumber ] != NULL )
    {
        Result = Component->ValidateChain ( Component->CertificateChains [ ChainNumber ] );

        if ( ! Result )
        {
            if ( Tester->ConsoleDebugging )
            {
                if ( Tester->ConsoleDebugging ) printf ( "Chain Validation failed!\n" ); // comment on result but otherwise ignore it
            }
        }

         Result = Component->VerifyCertificate ( (mipki_state *) State,
                                                 Component->CertificateChains [ ChainNumber ],
                                                 SignatureAlgorithm,
                                                 (const char *) Certificate,
                                                 CertificateLength,
                                                 (char *) Signature,
                                                 &VerifiedSignatureLength );

        if ( ! Result )
        {
            if ( Tester->ConsoleDebugging ) printf ( "Certificate Verification failed!\n" );
        }

        // free the chain as we no longer need it

        Component->FreeChain ( Component->CertificateChains [ ChainNumber ] );

        Component->CertificateChains [ ChainNumber ] = NULL;
    }
    else
    {
        if ( Tester->ConsoleDebugging ) printf ( "Certificate Chain Parsing failed!\n" );
    }

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( Result );
}

//**********************************************************************************************************************************
//
// PKI Callback Function wrappers
//
//**********************************************************************************************************************************

int MITLS_CALLCONV CertificatePasswordCallback ( char       *password,
                                                 int         max_size,
                                                 const char *key_file )
{
    CALLBACKMEASUREMENTENTRY *PKICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    PKICallbackMeasurement = &Tester->ClientComponent->MeasurementResultsArray [ Tester->ClientComponent->TestRunNumber ]->Measurements [ Tester->ClientComponent->MeasurementNumber ].PKICallbackMeasurements [ MIPKI_PASSWORD_CALLBACK ];

    CallCount = PKICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &PKICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Password Callback function invoked!\n" );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &PKICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( 0 );
}

//**********************************************************************************************************************************

void *MITLS_CALLCONV CertificateAllocationCallback ( void    *cur,
                                                     size_t   len,
                                                     char   **buf )
{
    CALLBACKMEASUREMENTENTRY *PKICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    PKICallbackMeasurement = &Tester->ClientComponent->MeasurementResultsArray [ Tester->ClientComponent->TestRunNumber ]->Measurements [ Tester->ClientComponent->MeasurementNumber ].PKICallbackMeasurements [ MIPKI_ALLOC_CALLBACK ];

    CallCount = PKICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &PKICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Allocation Callback function invoked!\n" );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &PKICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( NULL );
}

//**********************************************************************************************************************************
//
// Measurement Methods
//
//**********************************************************************************************************************************

void COMPONENT::InitialiseMeasurementResults ( void )
{
    int                 TestRunNumber     = 0;
    MEASUREMENTRESULTS *MeasurementResult = NULL;

    // initialise all array entries to unallocated

    for ( TestRunNumber = 0; TestRunNumber < MAX_MEASUREMENT_TYPES; TestRunNumber++ )
    {
        MeasurementResultsArray [ TestRunNumber ] = NULL;
    }

    // Then allocate the measurement results arrays for the selected measurements

    if ( Tester->DoClientTests )
    {
        if ( Tester->DoTLSTests  ) AllocateMeasurementResult ( TLS_CLIENT_MEASUREMENTS  );
        if ( Tester->DoQUICTests ) AllocateMeasurementResult ( QUIC_CLIENT_MEASUREMENTS );
    }

    if ( Tester->DoServerTests )
    {
        if ( Tester->DoTLSTests  ) AllocateMeasurementResult ( TLS_SERVER_MEASUREMENTS  );
        if ( Tester->DoQUICTests ) AllocateMeasurementResult ( QUIC_SERVER_MEASUREMENTS );
    }

    if ( Tester->DoServerInteroperabilityTests )
    {
        AllocateMeasurementResult ( OPENSSL_SERVER_MEASUREMENTS   );
        AllocateMeasurementResult ( BORINGSSL_SERVER_MEASUREMENTS );
        AllocateMeasurementResult ( MBEDTLS_SERVER_MEASUREMENTS   );
        AllocateMeasurementResult ( WOLFSSL_SERVER_MEASUREMENTS   );
        AllocateMeasurementResult ( FIZZ_SERVER_MEASUREMENTS      );
    }

    if ( Tester->DoClientInteroperabilityTests )
    {
        AllocateMeasurementResult ( OPENSSL_CLIENT_MEASUREMENTS   );
        AllocateMeasurementResult ( BORINGSSL_CLIENT_MEASUREMENTS );
        AllocateMeasurementResult ( MBEDTLS_CLIENT_MEASUREMENTS   );
        AllocateMeasurementResult ( WOLFSSL_CLIENT_MEASUREMENTS   );
        AllocateMeasurementResult ( FIZZ_CLIENT_MEASUREMENTS      );
    }

    // finally, initialise the allocated measurement results arrays

    for ( TestRunNumber = 0; TestRunNumber < MAX_MEASUREMENT_TYPES; TestRunNumber++ )
    {
        if ( MeasurementResultsArray [ TestRunNumber ] != NULL ) // was memory allocated for this measurement?
        {
            MeasurementResult = MeasurementResultsArray [ TestRunNumber ];

            MeasurementResult->MeasurementTypeName = MeasurementTypeNames [ TestRunNumber ];

            InitialiseMeasurementResult ( MeasurementResult );
        }
    }
}

//**********************************************************************************************************************************

void COMPONENT::AllocateMeasurementResult ( int TestRunNumber )
{
    MeasurementResultsArray [ TestRunNumber ] = ( MEASUREMENTRESULTS * ) malloc ( sizeof ( MEASUREMENTRESULTS ) );

    if ( MeasurementResultsArray [ TestRunNumber ] == NULL )
    {
        printf ( "Could not allocate memory for measurement type %d. This is a FATAL error!\n", TestRunNumber );

        exit ( EXIT_FAILURE );
    }
}

//**********************************************************************************************************************************

void COMPONENT::FreeMeasurementResults ( void )
{
    int TestRunNumber = 0;

    for ( TestRunNumber = 0; TestRunNumber < MAX_MEASUREMENT_TYPES; TestRunNumber++ )
    {
        if ( MeasurementResultsArray [ TestRunNumber ] != NULL ) // was memory allocated for this measurement?
        {
            // if so then free it

            free ( MeasurementResultsArray [ TestRunNumber ] );

            MeasurementResultsArray [ TestRunNumber ] = NULL;
        }
    }
}

//**********************************************************************************************************************************

void COMPONENT::InitialiseMeasurementResult ( MEASUREMENTRESULTS *MeasurementResult )
{
    COMPONENTMEASUREMENTENTRY *ComponentMeasurementEntry = NULL;
    CALLBACKMEASUREMENTENTRY  *CallbackMeasurementEntry  = NULL;
    COMPONENTMEASUREMENT      *ComponentMeasurement      = NULL;

    MeasurementResult->TestRunStartTime.QuadPart = 0;
    MeasurementResult->TestRunEndTime.QuadPart   = 0;

    for ( int MeasurementNumber = 0; MeasurementNumber < MAX_MEASUREMENTS; MeasurementNumber++ )
    {
        ComponentMeasurement = &MeasurementResult->Measurements [ MeasurementNumber ];

        ComponentMeasurement->MeasurementStartTime.QuadPart = 0;
        ComponentMeasurement->MeasurementEndTime.QuadPart   = 0;

        //***********************
        // Component measurements
        //***********************

        for ( int FunctionIndex = 0; FunctionIndex < MAX_FFI_FUNCTIONS; FunctionIndex++ )
        {
            ComponentMeasurementEntry = &ComponentMeasurement->FFIMeasurements [ FunctionIndex ];

            ComponentMeasurementEntry->EntryName = FFIMeasurementEntryNames [ FunctionIndex ];

            ComponentMeasurementEntry->NumberOfCalls = 0;

            for ( int CallIndex = 0; CallIndex < MAX_COMPONENT_CALLS_PER_MEASUREMENT; CallIndex++ )
            {
                ComponentMeasurementEntry->StartTimes [ CallIndex ].QuadPart = 0;
                ComponentMeasurementEntry->EndTimes   [ CallIndex ].QuadPart = 0;
            }
        }

        for ( int FunctionIndex = 0; FunctionIndex < MAX_PKI_FUNCTIONS; FunctionIndex++ )
        {
            ComponentMeasurementEntry = &ComponentMeasurement->PKIMeasurements [ FunctionIndex ];

            ComponentMeasurementEntry->EntryName = PKIMeasurementEntryNames [ FunctionIndex ];

            ComponentMeasurementEntry->NumberOfCalls = 0;

            for ( int CallIndex = 0; CallIndex < MAX_COMPONENT_CALLS_PER_MEASUREMENT; CallIndex++ )
            {
                ComponentMeasurementEntry->StartTimes [ CallIndex ].QuadPart = 0;
                ComponentMeasurementEntry->EndTimes   [ CallIndex ].QuadPart = 0;
            }
        }

        //*********************
        // Library measurements
        //*********************

        for ( int FunctionIndex = 0; FunctionIndex < MAX_FFI_CALLBACK_FUNCTIONS; FunctionIndex++ )
        {
            CallbackMeasurementEntry = &ComponentMeasurement->FFICallbackMeasurements [ FunctionIndex ];

            CallbackMeasurementEntry->EntryName = FFICallbackMeasurementEntryNames [ FunctionIndex ];

            CallbackMeasurementEntry->NumberOfCalls = 0;

            for ( int CallIndex = 0; CallIndex < MAX_CALLBACK_CALLS_PER_MEASUREMENT; CallIndex++ )
            {
                CallbackMeasurementEntry->StartTimes [ CallIndex ].QuadPart = 0;
                CallbackMeasurementEntry->EndTimes   [ CallIndex ].QuadPart = 0;
            }
        }

        for ( int FunctionIndex = 0; FunctionIndex < MAX_PKI_CALLBACK_FUNCTIONS; FunctionIndex++ )
        {
            CallbackMeasurementEntry = &ComponentMeasurement->PKICallbackMeasurements [ FunctionIndex ];

            CallbackMeasurementEntry->EntryName = PKICallbackMeasurementEntryNames [ FunctionIndex ];

            CallbackMeasurementEntry->NumberOfCalls = 0;

            for ( int CallIndex = 0; CallIndex < MAX_CALLBACK_CALLS_PER_MEASUREMENT; CallIndex++ )
            {
                CallbackMeasurementEntry->StartTimes [ CallIndex ].QuadPart = 0;
                CallbackMeasurementEntry->EndTimes   [ CallIndex ].QuadPart = 0;
            }
        }
    }
}

//**********************************************************************************************************************************

void COMPONENT::PrintMeasurementResults ( FILE *MeasurementsResultFile )
{
    MEASUREMENTRESULTS *MeasurementResult = NULL;

    // write the measurements to the recorded measurements file

    for ( int TestRunNumber = 0; TestRunNumber < MAX_MEASUREMENT_TYPES; TestRunNumber++ )
    {
        MeasurementResult = MeasurementResultsArray [ TestRunNumber ];

        // only print out the test runs which were actually recorded

        if ( MeasurementResult != NULL ) // was memory allocated?
        {
            if ( MeasurementResult->TestRunStartTime.QuadPart != 0 ) // did the measurement take place?
            {
                PrintMeasurementResult ( MeasurementsResultFile, MeasurementResult );
            }
        }
    }

    PrintMeasurementSummary ( IsServer );
}

//**********************************************************************************************************************************

void COMPONENT::PrintMeasurementResult ( FILE               *MeasurementsResultFile,
                                         MEASUREMENTRESULTS *MeasurementResult )
{
    COMPONENTMEASUREMENTENTRY *ComponentMeasurementEntry = NULL;
    CALLBACKMEASUREMENTENTRY  *CallbackMeasurementEntry  = NULL;
    COMPONENTMEASUREMENT      *ComponentMeasurement      = NULL;

    fprintf ( MeasurementsResultFile, "Test Run Type Type = %s\n", MeasurementResult->MeasurementTypeName );

    fprintf ( MeasurementsResultFile, "Test Run StartTime = %I64u\n", MeasurementResult->TestRunStartTime.QuadPart );

    fprintf ( MeasurementsResultFile, "Test Run EndTime = %I64u\n", MeasurementResult->TestRunEndTime.QuadPart );

    for ( int MeasurementNumber = 0; MeasurementNumber < MAX_MEASUREMENTS; MeasurementNumber++ )
    {
        ComponentMeasurement = &MeasurementResult->Measurements [ MeasurementNumber ];

        // only print out the measurements which were actually recorded

        if ( ComponentMeasurement->MeasurementStartTime.QuadPart == 0 ) break;

        fprintf ( MeasurementsResultFile, "\nMeasurement Results Entry [ %d ]\n\n", MeasurementNumber );

        fprintf ( MeasurementsResultFile, "Measurement Start Time = %I64u\n", ComponentMeasurement->MeasurementStartTime.QuadPart );
        fprintf ( MeasurementsResultFile, "Measurement End Time   = %I64u\n", ComponentMeasurement->MeasurementEndTime.QuadPart   );

        //***********************
        // Component measurements
        //***********************

        for ( int FunctionIndex = 0; FunctionIndex < MAX_FFI_FUNCTIONS; FunctionIndex++ )
        {
            ComponentMeasurementEntry = &ComponentMeasurement->FFIMeasurements [ FunctionIndex ];

            // only print out the component measurements recorded

            if ( ComponentMeasurementEntry->NumberOfCalls > 0 )
            {
                fprintf ( MeasurementsResultFile, " FFI Function Name = %s\n", ComponentMeasurementEntry->EntryName );

                fprintf ( MeasurementsResultFile, "   Number Of Calls = %u\n", ComponentMeasurementEntry->NumberOfCalls );

                for ( int CallIndex = 0; CallIndex < ComponentMeasurementEntry->NumberOfCalls; CallIndex++ )
                {
                    fprintf ( MeasurementsResultFile, " Measurement Start Time [%03d] = %I64u\n", CallIndex, ComponentMeasurementEntry->StartTimes [ CallIndex ].QuadPart );
                    fprintf ( MeasurementsResultFile, " Measurement End Time   [%03d] = %I64u\n", CallIndex, ComponentMeasurementEntry->EndTimes   [ CallIndex ].QuadPart );
                }
            }
        }

        for ( int FunctionIndex = 0; FunctionIndex < MAX_FFI_CALLBACK_FUNCTIONS; FunctionIndex++ )
        {
            CallbackMeasurementEntry = &ComponentMeasurement->FFICallbackMeasurements [ FunctionIndex ];

            // only print out the component callback measurements recorded

            if ( CallbackMeasurementEntry->NumberOfCalls > 0 )
            {
                fprintf ( MeasurementsResultFile, " FFI Callback Name = %s\n", CallbackMeasurementEntry->EntryName );

                fprintf ( MeasurementsResultFile, "   Number Of Calls = %u\n", CallbackMeasurementEntry->NumberOfCalls );

                for ( int CallIndex = 0; CallIndex < CallbackMeasurementEntry->NumberOfCalls; CallIndex++ )
                {
                    fprintf ( MeasurementsResultFile, " Measurement Start Time [%03d] = %I64u\n", CallIndex, CallbackMeasurementEntry->StartTimes [ CallIndex ].QuadPart );
                    fprintf ( MeasurementsResultFile, " Measurement End Time   [%03d] = %I64u\n", CallIndex, CallbackMeasurementEntry->EndTimes   [ CallIndex ].QuadPart );
                }
                }
        }

        //*********************
        // Library measurements
        //*********************

        for ( int FunctionIndex = 0; FunctionIndex < MAX_PKI_FUNCTIONS; FunctionIndex++ )
        {
            ComponentMeasurementEntry = &ComponentMeasurement->PKIMeasurements [ FunctionIndex ];

            // only print the library measurements recorded

            if ( ComponentMeasurementEntry->NumberOfCalls > 0 )
            {
                fprintf ( MeasurementsResultFile, " PKI Function Name = %s\n", ComponentMeasurementEntry->EntryName );

                fprintf ( MeasurementsResultFile, "   Number Of Calls = %u\n", ComponentMeasurementEntry->NumberOfCalls );

                for ( int CallIndex = 0; CallIndex < ComponentMeasurementEntry->NumberOfCalls; CallIndex++ )
                {
                    fprintf ( MeasurementsResultFile, " Measurement Start Time [%03d] = %I64u\n", CallIndex, ComponentMeasurementEntry->StartTimes [ CallIndex ].QuadPart );
                    fprintf ( MeasurementsResultFile, " Measurement End Time   [%03d] = %I64u\n", CallIndex, ComponentMeasurementEntry->EndTimes   [ CallIndex ].QuadPart );
                }
            }
        }

        for ( int FunctionIndex = 0; FunctionIndex < MAX_PKI_CALLBACK_FUNCTIONS; FunctionIndex++ )
        {
            CallbackMeasurementEntry = &ComponentMeasurement->PKICallbackMeasurements [ FunctionIndex ];

            // only print the library callback measurements recorded

            if ( CallbackMeasurementEntry->NumberOfCalls > 0 )
            {
                fprintf ( MeasurementsResultFile, " PKI Callback Name = %s\n", CallbackMeasurementEntry->EntryName );

                fprintf ( MeasurementsResultFile, "   Number Of Calls = %u\n", CallbackMeasurementEntry->NumberOfCalls );

                for ( int CallIndex = 0; CallIndex < CallbackMeasurementEntry->NumberOfCalls; CallIndex++ )
                {
                    fprintf ( MeasurementsResultFile, " Measurement Start Time [%03d] = %I64u\n", CallIndex, CallbackMeasurementEntry->StartTimes [ CallIndex ].QuadPart );
                    fprintf ( MeasurementsResultFile, " Measurement End Time   [%03d] = %I64u\n", CallIndex, CallbackMeasurementEntry->EndTimes   [ CallIndex ].QuadPart );
                }
            }
        }
    }
}

//**********************************************************************************************************************************

unsigned long MeasurementSummaryArrayIndex    = 0;
unsigned long MaxMeasurementSummaryArrayIndex = ( ( MAX_FFI_FUNCTIONS          + MAX_PKI_FUNCTIONS          ) * MAX_COMPONENT_CALLS_PER_MEASUREMENT * 2 ) +
                                                ( ( MAX_FFI_CALLBACK_FUNCTIONS + MAX_PKI_CALLBACK_FUNCTIONS ) * MAX_CALLBACK_CALLS_PER_MEASUREMENT  * 2 );

MEASUREMENT_SUMMARY_ENTRY *MeasurementSummaryArray = NULL; // allocate dynamically

void COMPONENT::PrintMeasurementSummary ( bool IsServer )
{
    MEASUREMENTRESULTS        *MeasurementResult                 = NULL;
    COMPONENTMEASUREMENTENTRY *ComponentMeasurementEntry         = NULL;
    CALLBACKMEASUREMENTENTRY  *CallbackMeasurementEntry          = NULL;
    COMPONENTMEASUREMENT      *ComponentMeasurement              = NULL;
    FILE                      *MeasurementSummaryFile            = NULL;
    unsigned int               TestRunNumber                     = 0;
    unsigned int               MeasurementNumber                 = 0;
    unsigned int               FunctionIndex                     = 0;
    unsigned int               CallIndex                         = 0;
    long                       StartTime                         = 0;
    long                       ExecutionTime                     = 0; // in microseconds
    char                      *ClientMeasurementSummaryFilename  = "ClientMeasurementSummary.csv";
    char                      *ServerMeasurementSummaryFilename  = "ServerMeasurementSummary.csv";
    LARGE_INTEGER              MeasurementStartTime;

    if ( IsServer )
    {
        MeasurementSummaryFile = fopen ( ServerMeasurementSummaryFilename, "wt" );
    }
    else
    {
        MeasurementSummaryFile = fopen ( ClientMeasurementSummaryFilename, "wt" );
    }

    if ( MeasurementSummaryFile != NULL ) // was the file opened successfully?
    {
        fprintf ( MeasurementSummaryFile, "#\n" );
        fprintf ( MeasurementSummaryFile, "# Measurement Summary (Unsorted)\n" );
        fprintf ( MeasurementSummaryFile, "# ------------------------------\n" );
        fprintf ( MeasurementSummaryFile, "#\n" );

        // run through each test run

        for ( TestRunNumber = 0; TestRunNumber < MAX_MEASUREMENT_TYPES; TestRunNumber++ )
        {
            // get the measurement array for this test run

            MeasurementResult = MeasurementResultsArray [ TestRunNumber ];

            // only print out the test runs which were actually recorded

            if ( MeasurementResult != NULL ) // was memory allocated for this test run?
            {
                // run through each measurement for this test run

                for ( MeasurementNumber = 0; MeasurementNumber < MAX_MEASUREMENTS; MeasurementNumber++ )
                {
                    // allocate empty measurement summary array for maximum number of component measurements and function calls

                    MeasurementSummaryArray = (MEASUREMENT_SUMMARY_ENTRY *) calloc ( MaxMeasurementSummaryArrayIndex, sizeof ( MEASUREMENT_SUMMARY_ENTRY ) );

                    if ( MeasurementSummaryArray != NULL ) // was memory allocated for the measurement summary array ?
                    {
                        ComponentMeasurement = &MeasurementResult->Measurements [ MeasurementNumber ];

                        MeasurementStartTime = ComponentMeasurement->MeasurementStartTime;

                        // only print out the measurements which were actually recorded

                        if ( MeasurementStartTime.QuadPart == 0 ) break;

                        // work out how long the component measurement took

                        ExecutionTime = Tester->CalculateExecutionTime ( MeasurementStartTime, ComponentMeasurement->MeasurementEndTime );

                        fprintf ( MeasurementSummaryFile,
                                  "# Test Run [%d] Component Measurement [ %d ] Total Execution Time %u microseconds\n", TestRunNumber, MeasurementNumber, ExecutionTime );

                        //***********************
                        // Component measurements
                        //***********************

                        for ( FunctionIndex = 0; FunctionIndex < MAX_FFI_FUNCTIONS; FunctionIndex++ )
                        {
                            ComponentMeasurementEntry = &ComponentMeasurement->FFIMeasurements [ FunctionIndex ];

                            // only print out the component measurements recorded

                            if ( ComponentMeasurementEntry->NumberOfCalls > 0 )
                            {
                                for ( int CallIndex = 0; CallIndex < ComponentMeasurementEntry->NumberOfCalls; CallIndex++ )
                                {
                                    AddMeasurementSummaryEntry ( MeasurementSummaryFile,
                                                                    MeasurementResult,
                                                                    ComponentMeasurement,
                                                                    ComponentMeasurementEntry,
                                                                    TestRunNumber,
                                                                    MeasurementNumber,
                                                                    FunctionIndex,
                                                                    CallIndex );
                                }
                            }
                        }

                        for ( FunctionIndex = 0; FunctionIndex < MAX_FFI_CALLBACK_FUNCTIONS; FunctionIndex++ )
                        {
                            CallbackMeasurementEntry = &ComponentMeasurement->FFICallbackMeasurements [ FunctionIndex ];

                            // only print out the component callback measurements recorded

                            if ( CallbackMeasurementEntry->NumberOfCalls > 0 )
                            {
                                for ( CallIndex = 0; CallIndex < CallbackMeasurementEntry->NumberOfCalls; CallIndex++ )
                                {
                                    AddMeasurementSummaryEntry ( MeasurementSummaryFile,
                                                                    ComponentMeasurement,
                                                                    CallbackMeasurementEntry,
                                                                    TestRunNumber,
                                                                    MeasurementNumber,
                                                                    CallIndex );
                                }
                            }
                        }

                        //*********************
                        // Library measurements
                        //*********************

                        for ( FunctionIndex = 0; FunctionIndex < MAX_PKI_FUNCTIONS; FunctionIndex++ )
                        {
                            ComponentMeasurementEntry = &ComponentMeasurement->PKIMeasurements [ FunctionIndex ];

                            // only print the library measurements recorded

                            if ( ComponentMeasurementEntry->NumberOfCalls > 0 )
                            {
                                for ( CallIndex = 0; CallIndex < ComponentMeasurementEntry->NumberOfCalls; CallIndex++ )
                                {
                                    AddMeasurementSummaryEntry ( MeasurementSummaryFile,
                                                                    MeasurementResult,
                                                                    ComponentMeasurement,
                                                                    ComponentMeasurementEntry,
                                                                    TestRunNumber,
                                                                    MeasurementNumber,
                                                                    FunctionIndex,
                                                                    CallIndex );
                                }
                            }
                        }

                        for ( FunctionIndex = 0; FunctionIndex < MAX_PKI_CALLBACK_FUNCTIONS; FunctionIndex++ )
                        {
                            CallbackMeasurementEntry = &ComponentMeasurement->PKICallbackMeasurements [ FunctionIndex ];

                            // only print the library callback measurements recorded

                            if ( CallbackMeasurementEntry->NumberOfCalls > 0 )
                            {
                                for ( CallIndex = 0; CallIndex < CallbackMeasurementEntry->NumberOfCalls; CallIndex++ )
                                {
                                    AddMeasurementSummaryEntry ( MeasurementSummaryFile,
                                                                    ComponentMeasurement,
                                                                    CallbackMeasurementEntry,
                                                                    TestRunNumber,
                                                                    MeasurementNumber,
                                                                    CallIndex );
                                }
                            }
                        }

                        // now sort the summary array into chronological order

                        qsort ( (void *) MeasurementSummaryArray,
                                (size_t) MeasurementSummaryArrayIndex,
                                (size_t) sizeof ( MEASUREMENT_SUMMARY_ENTRY ),
                                MeasurementSummaryCompare );

                        // and put the resulting array into the summary file

                        fprintf ( MeasurementSummaryFile, "\n" );
                        fprintf ( MeasurementSummaryFile, "# Measurement Summary (Sorted)\n" );
                        fprintf ( MeasurementSummaryFile, "# ----------------------------\n" );
                        fprintf ( MeasurementSummaryFile, "\n" );

                        fprintf ( MeasurementSummaryFile,
                                  "Test Run Number, Measurement Number, Call Index, Function Name, StartTime, Duration\n\n" );

                        for ( int Index = 0; Index < MeasurementSummaryArrayIndex; Index++ )
                        {
                            fprintf ( MeasurementSummaryFile,
                                      "%d, %d, %d, %s, %u, %u\n",
                                      MeasurementSummaryArray [ Index ].TestRunNumber,
                                      MeasurementSummaryArray [ Index ].MeasurementNumber,
                                      MeasurementSummaryArray [ Index ].CallNumber,
                                      MeasurementSummaryArray [ Index ].FunctionName,
                                      MeasurementSummaryArray [ Index ].StartTime,
                                      MeasurementSummaryArray [ Index ].Duration );
                        }

                        if ( Tester->GenerateImageFiles ) CreateMeasurementSummaryImage ( TestRunNumber, MeasurementNumber );

                        // we are finished with the array

                        free ( MeasurementSummaryArray );

                        MeasurementSummaryArray = NULL;

                        MeasurementSummaryArrayIndex = 0;
                    }
                    else
                    {
                        printf ( "Cannot allocate memory for measurement array!\n" );
                    }

                } // Measurement Number

            } // if ( MeasurementResult != NULL )

        } // TestRunNumber

        fclose ( MeasurementSummaryFile );
    }
    else
    {
        printf ( "Cannot open measurement summary file!\n",
                 IsServer ? ClientMeasurementSummaryFilename : ServerMeasurementSummaryFilename );
    }
}

//**********************************************************************************************************************************

int MeasurementSummaryCompare ( const void *arg1, const void *arg2 )
{
    MEASUREMENT_SUMMARY_ENTRY *Entry1 = (MEASUREMENT_SUMMARY_ENTRY *) arg1;
    MEASUREMENT_SUMMARY_ENTRY *Entry2 = (MEASUREMENT_SUMMARY_ENTRY *) arg2;

   // Compare only the start times of both entries

   return ( Entry1->StartTime - Entry2->StartTime );
}

//**********************************************************************************************************************************

void COMPONENT::AddMeasurementSummaryEntry ( FILE                      *MeasurementSummaryFile,
                                             MEASUREMENTRESULTS        *MeasurementResult,
                                             COMPONENTMEASUREMENT      *ComponentMeasurement,
                                             COMPONENTMEASUREMENTENTRY *ComponentMeasurementEntry,
                                             int                        TestRunNumber,
                                             int                        MeasurementNumber,
                                             int                        FunctionIndex,
                                             int                        CallIndex )
{
    long StartTime     = 0;
    long ExecutionTime = 0;

    // work out the start and execution times

    if ( ( FunctionIndex == FFI_MITLS_INIT               ) || // these are all called very early, well before any measurements
         ( FunctionIndex == MIPKI_INIT                   ) ||
         ( FunctionIndex == MIPKI_FREE                   ) ||
         ( FunctionIndex == FFI_MITLS_SET_TRACE_CALLBACK ) ||
         ( FunctionIndex == MIPKI_ADD_ROOT_FILE_OR_PATH  ) ||
         ( FunctionIndex == FFI_MITLS_CLEANUP            ) )  // this is called at the very end
    {
        // dont record these ones

        return;

        //StartTime = Tester->CalculateExecutionTime ( MeasurementResult->TestRunStartTime,
        //                                             ComponentMeasurementEntry->StartTimes [ CallIndex ]);
    }
    else
    {
        StartTime = Tester->CalculateExecutionTime ( ComponentMeasurement->MeasurementStartTime,
                                                     ComponentMeasurementEntry->StartTimes [ CallIndex ]);

        ExecutionTime = Tester->CalculateExecutionTime ( ComponentMeasurementEntry->StartTimes [ CallIndex ],
                                                         ComponentMeasurementEntry->EndTimes   [ CallIndex ]);

        // record the measurement summary in the measurement summary file

        fprintf ( MeasurementSummaryFile,
                  "# %s [%d] Function Start Time %u, Execution Time %u\n",
                  ComponentMeasurementEntry->EntryName,
                  CallIndex,
                  StartTime,
                  ExecutionTime );

        // add an entry to the measurement summary array

        MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].IsCallback        = FALSE;
        MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].FunctionName      = ComponentMeasurementEntry->EntryName;
        MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].TestRunNumber     = TestRunNumber;
        MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].MeasurementNumber = MeasurementNumber;
        MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].CallNumber        = CallIndex;
        MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].StartTime         = StartTime;
        MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].Duration          = ExecutionTime;

        MeasurementSummaryArrayIndex++;
    }
}

//**********************************************************************************************************************************

void COMPONENT::AddMeasurementSummaryEntry ( FILE                     *MeasurementSummaryFile,
                                             COMPONENTMEASUREMENT     *ComponentMeasurement,
                                             CALLBACKMEASUREMENTENTRY *CallbackMeasurementEntry,
                                             int                       TestRunNumber,
                                             int                       MeasurementNumber,
                                             int                       CallIndex )
{
    // work out the start and execution times

    long StartTime = Tester->CalculateExecutionTime ( ComponentMeasurement->MeasurementStartTime,
                                                      CallbackMeasurementEntry->StartTimes [ CallIndex ]);

    long ExecutionTime = Tester->CalculateExecutionTime ( CallbackMeasurementEntry->StartTimes [ CallIndex ],
                                                          CallbackMeasurementEntry->EndTimes   [ CallIndex ]);

    // record the measurement summary in the measurement summary file

    fprintf ( MeasurementSummaryFile,
              "# %s [%d] Callback Execution Time, %u\n",
              CallbackMeasurementEntry->EntryName,
              CallIndex,
              ExecutionTime );

    // add an entry to the measurement summary array

    MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].IsCallback        = TRUE;
    MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].FunctionName      = CallbackMeasurementEntry->EntryName;
    MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].TestRunNumber     = TestRunNumber;
    MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].MeasurementNumber = MeasurementNumber;
    MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].CallNumber        = CallIndex;
    MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].StartTime         = StartTime;
    MeasurementSummaryArray [ MeasurementSummaryArrayIndex ].Duration          = ExecutionTime;

    MeasurementSummaryArrayIndex++;
}

//**********************************************************************************************************************************
//
//    < --------------------------------------- Image Width -------------------------------------->
//    --------------------------------------------------------------------------------------------   ^
//   |                                       Top Border                                           |  |
//   |         --------------------------------------------------------------------------         |  |
//   |        |                               |                                          |        |  |
//   |  Left  |                               |                                          | Right  |  | Image
//   | Border |          Text Area            |                    Line Area             | Border |  | Height
//   |        |                               |                                          |        |  |
//   |        |                               |                                          |        |  |
//   |         --------------------------------------------------------------------------         |  |
//   |                                      Bottom Border                                         |  |
//    --------------------------------------------------------------------------------------------   v
//
//

void COMPONENT::CreateMeasurementSummaryImage ( int TestRunNumber,
                                                int MeasurementNMumber )
{
    int FontSize           = 20;
    int LeftBorder         = 100;
    int RightBorder        = 100;
    int TopBorder          = 100;
    int BottomBorder       = 100;
    int TextAreaHeight     = MeasurementSummaryArrayIndex * ( FontSize + 4); // based in number of lines needed and fontsize
    int ImageHeight        = TextAreaHeight + TopBorder + BottomBorder;
    int ImageWidth         = 3000;
    int TextStart          = 10;  // left border within the Text Area
    int LineStart          = 500; // left border within the Line Area
    long FirstStartTime    = MeasurementSummaryArray [                                0 ].StartTime;
    long LastStartTime     = MeasurementSummaryArray [ MeasurementSummaryArrayIndex - 1 ].StartTime;
    long MaxDuration       = LastStartTime - FirstStartTime;
    long Duration          = 1;
    int  PowerOfTen        = 1;
    int  Value             = MaxDuration;
    int  DurationIncrement = 0;

    char TestImageFilename [ MAX_PATH ];
    char TestImageTitle    [ 1000 ];

    char *FontPath = "C:\\Program Files (x86)\\Graphviz2.38\\share\\fonts\\FreeSans.ttf";

    sprintf ( TestImageFilename, "MeasurementSummaryImage_Run%d_Measurement%d.png", TestRunNumber, MeasurementNMumber );

    pngwriter TestImage ( ImageWidth, ImageHeight, 65535, TestImageFilename ); // a white image

    sprintf ( TestImageTitle, "Measurement Summary Image for Run %d and Measurement %d", TestRunNumber, MeasurementNMumber );

    TestImage.settext ( TestImageTitle,
                        (const char *) "Caroline Mathieson",
                        (const char *) "gantt chart like image of start time and duration for each function call",
                        (const char *) "MITLS Tester" );

    // draw a border round the text and line areas

    TestImage.square ( LeftBorder, BottomBorder, ImageWidth - RightBorder, ImageHeight - TopBorder, 0, 0, 0 );

    // for each entry in the measurement summary array, draw the function name in black

    for ( int Index = 0; Index < MeasurementSummaryArrayIndex; Index++ )
    {
        char *FunctionName = (char *) MeasurementSummaryArray [ Index ].FunctionName;

        TestImage.plot_text_utf8 ( FontPath,
                                   FontSize,
                                   LeftBorder + TextStart,
                                   ImageHeight - TopBorder - FontSize - ( FontSize + 4 ) * Index, // compensate for text height
                                   (double) 0.0,
                                   FunctionName,
                                   0,
                                   0,
                                   0 );
    }

   // find the nearest power of ten

    while ( Value > 0 )
    {
        Value = Value / 10; PowerOfTen++; Duration *= 10;
    }

    DurationIncrement = Duration / 10; // nearest power of ten above the actual total duration so reduce by 10 to get real increment

    // and calculate a scaling factor given the line area size

    double ScalingFactor = (double) ( ImageWidth - LeftBorder - RightBorder - LineStart - 100 ) / (double) ( MaxDuration );

    // draw some power of ten grid lines for scale

    for ( long Index = 0; Index < MaxDuration; Index += DurationIncrement ) // x axis
    {
        for ( int y = BottomBorder; y < ( ImageHeight - TopBorder ); y += 5 ) // y axis
        {
            int x = LeftBorder + LineStart + ( Index * ScalingFactor );

            TestImage.filledsquare ( x, y, x + 1, y + 1, 0.0, 1.0, 0.0 );
        }
    }

    // for each entry in the measurement array, draw the duration line at the right starting point

    for ( int Index = 0; Index < MeasurementSummaryArrayIndex; Index++)
    {
        // plot the duration line

        int y = ImageHeight - TopBorder - FontSize - ( FontSize + 4 ) * Index;

        int x = LeftBorder + LineStart + ( MeasurementSummaryArray [ Index ].StartTime - FirstStartTime ) * ScalingFactor;

        int width = 2 + (int) ( MeasurementSummaryArray [ Index ].Duration ) * ScalingFactor; // minimum width of 2 pixels

        int height = FontSize - 2;

        if ( MeasurementSummaryArray [ Index ].IsCallback )
        {
            TestImage.filledsquare ( x + 1, y + 1, x + width, y + height, 0.0, 0.0, 1.0 ); // draw it in blue
        }
        else
        {
            TestImage.filledsquare ( x + 1, y + 1, x + width, y + height, 1.0, 0.0, 1.0 ); // draw it in magenta
        }

        // plot the duration text (in us)

        char DurationText [ 10 ];

        itoa ( MeasurementSummaryArray [ Index ].Duration, DurationText, 10 );

        strcat ( DurationText, "us" );

        TestImage.plot_text_utf8 ( FontPath,
                                   FontSize - 4,
                                   x + width + 15, // offset the text to the right from the line
                                   y + 2,
                                   (double) 0.0,
                                   (char *) DurationText,
                                   0,
                                   0,
                                   0 );
    }

    TestImage.close ();
}

//**********************************************************************************************************************************

void COMPONENT::RecordTestRunStartTime ( void )
{
     QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->TestRunStartTime );
}

//**********************************************************************************************************************************

void COMPONENT::RecordTestRunEndTime ( void )
{
     QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->TestRunEndTime );
}

//**********************************************************************************************************************************

void COMPONENT::RecordMeasurementStartTime ( void )
{
     QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->Measurements [ MeasurementNumber ].MeasurementStartTime );
}

//**********************************************************************************************************************************

void COMPONENT::RecordMeasurementEndTime ( void )
{
     QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->Measurements [ MeasurementNumber ].MeasurementEndTime );
}

//**********************************************************************************************************************************
//
// COMPONENT Methods
//
//**********************************************************************************************************************************

COMPONENT::COMPONENT ( TLSTESTER *Parent,  FILE *NewDebugFile, bool IsThisAServer )
{
    Tester = Parent;

    DebugFile = NewDebugFile;

    IsServer = IsThisAServer;

    Socket = INVALID_SOCKET;

    // initialise component and library internal state variable addresses

    TLSState  = NULL;
    QUICState = NULL;
    PKIState  = NULL;

    // set the default values here in case they are not over-ridden by command line arguments

    strcpy ( TLSVersion, "1.3" );

    strcpy ( HostName, "google.com" );

    PortNumber = 443;

    strcpy ( ClientCertificateFilename,    "server-ecdsa.crt" );
    strcpy ( ClientCertificateKeyFilename, "server-ecdsa.key" );
    strcpy ( ServerCertificateFilename,    "server-ecdsa.crt" );
    strcpy ( ServerCertificateKeyFilename, "server-ecdsa.key" );

    // initialise certificate chain variables

    NumberOfChainsAllocated = 0; // index into CertificateChains

    for ( int ChainNumber = 0; ChainNumber < MAX_CERTIFICATE_CHAINS; ChainNumber++ )
    {
        CertificateChains [ ChainNumber ] = NULL;
    }

    // initialise measurement results global variables

    TestRunNumber = 0;

    MeasurementNumber = 0;

    NumberOfMeasurementsMade = 0;

    InitialiseMeasurementResults ();

    if ( IsServer ) // initialise the transfer buffers used in server tests
    {
        BufferInitialise ( &SendBuffer    );
        BufferInitialise ( &ReceiveBuffer );
    }

    CurrentComponentMeasurement = &MeasurementResultsArray [ 0 ]->Measurements [ 0 ]; // set to the first test and measurement
}

//**********************************************************************************************************************************

COMPONENT::~COMPONENT ( void )
{
    FreeMeasurementResults ();

    if ( IsServer )
    {
        fprintf ( stderr, "Buffer Management, SendBuffer->TotalAmountWritten    = %u octets\n", SendBuffer.TotalAmountWritten    );
        fprintf ( stderr, "Buffer Management, SendBuffer->TotalAmountRead       = %u octets\n", SendBuffer.TotalAmountRead       );
        fprintf ( stderr, "Buffer Management, ReceiveBuffer->TotalAmountWritten = %u octets\n", ReceiveBuffer.TotalAmountWritten );
        fprintf ( stderr, "Buffer Management, ReceiveBuffer->TotalAmountRead    = %u octets\n", ReceiveBuffer.TotalAmountRead    );
    }
}

//**********************************************************************************************************************************

void COMPONENT::SetClientCertificateFilename ( char *NewClientCertificateFilename )
{
    strcpy ( ClientCertificateFilename, NewClientCertificateFilename );
}

//**********************************************************************************************************************************

void COMPONENT::SetClientCertificateKeyFilename ( char *NewClientCertificateKeyFilename )
{
    strcpy ( ClientCertificateKeyFilename, NewClientCertificateKeyFilename );
}

//**********************************************************************************************************************************

void COMPONENT::SetServerCertificateFilename ( char *NewServerCertificateFilename )
{
    strcpy ( ServerCertificateFilename, NewServerCertificateFilename );
}

//**********************************************************************************************************************************

void COMPONENT::SetServerCertificateKeyFilename ( char *NewServerCertificateKeyFilename )
{
    strcpy ( ServerCertificateKeyFilename, NewServerCertificateKeyFilename );
}

//**********************************************************************************************************************************

void COMPONENT::SetVersion ( char *NewVersion )
{
    strcpy ( TLSVersion, NewVersion );
}

//**********************************************************************************************************************************

void COMPONENT::SetHostName ( char *NewHostName )
{
    strcpy ( HostName, NewHostName );
}

//**********************************************************************************************************************************

void COMPONENT::SetPortNumber ( int NewPortNumber )
{
    PortNumber = NewPortNumber;
}

//**********************************************************************************************************************************

void COMPONENT::SetTestRunNumber ( int NewTestRunNumber )
{
    TestRunNumber = NewTestRunNumber;

    // when we change the test run number, the measurements should start at 0 again

    SetMeasurementNumber ( 0 );
}

//**********************************************************************************************************************************

void COMPONENT::SetMeasurementNumber ( int NewMeasurementNumber )
{
    MeasurementNumber = NewMeasurementNumber;

    CurrentComponentMeasurement = &MeasurementResultsArray [ TestRunNumber ]->Measurements [ MeasurementNumber ];
}

//**********************************************************************************************************************************

void COMPONENT::SetSocket ( SOCKET ServerSocket )
{
    Socket = ServerSocket;
}

//**********************************************************************************************************************************

void COMPONENT::SetNumberOfMeasurementsMade ( int FinalNumberOfMeasurementsMade )
{
    NumberOfMeasurementsMade = FinalNumberOfMeasurementsMade;
}

//**********************************************************************************************************************************

char *COMPONENT::GetHostName ( void )
{
    return ( (char *) HostName );
}

//**********************************************************************************************************************************

int COMPONENT::GetPortNumber ( void )
{
    return ( PortNumber );
}

//**********************************************************************************************************************************
//
// TLS API Function wrappers
//
//**********************************************************************************************************************************

int COMPONENT::InitialiseTLS ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_INIT ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_init () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_init ();

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::Configure ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE ];

    int Result = 0;

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    if ( IsServer )
    {
        // don't specify the host name when in server mode

        Result = FFI_mitls_configure ( &TLSState, TLSVersion, "" ); // note that this one requires a state double pointer!
    }
    else
    {
        Result = FFI_mitls_configure ( &TLSState, TLSVersion, HostName ); // note that this one requires a state double pointer!
    }

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    if ( IsServer ) // reset those transfer buffers for each test that does a configure
    {
        BufferReset ( &SendBuffer    );
        BufferReset ( &ReceiveBuffer );
    }

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::Configure ( char *UseThisHostName ) // configure using the specified host name
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure (%s) called\n", UseThisHostName );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure ( &TLSState, TLSVersion, UseThisHostName ); // note that this one requires a state double pointer!

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::SetTicketKey ( const char          *Algorithm,
                              const unsigned char *TicketKey,
                              size_t               TicketKeyLength )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_SET_TICKET_KEY ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_set_ticket_key () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_set_ticket_key ( Algorithm, TicketKey, TicketKeyLength );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureCipherSuites ( const char *CipherSuites )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_CIPHER_SUITES ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure_cipher_suites () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_cipher_suites ( TLSState, CipherSuites );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureSignatureAlgorithms ( const char *SignatureAlgorithms )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_SIGNATURE_ALGORITHMS ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure_signature_algorithms () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_signature_algorithms ( TLSState, SignatureAlgorithms );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureNamedGroups ( const char *NamedGroups )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_NAMED_GROUPS ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure_named_groups () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_named_groups ( TLSState, NamedGroups );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureApplicationLayerProtocolNegotiation ( const char *ApplicationLayerProtocolNegotiation )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_ALPN ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure_alpn () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_alpn ( TLSState, ApplicationLayerProtocolNegotiation );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureEarlyData ( uint32_t MaximumEarlyData )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_EARLY_DATA ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure_early_data () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_early_data ( TLSState, MaximumEarlyData );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

void COMPONENT::ConfigureTraceCallback ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_SET_TRACE_CALLBACK ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_set_trace_callback () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    FFI_mitls_set_trace_callback ( TraceCallback );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureTicketCallback ( void              *CallbackState,
                                         pfn_FFI_ticket_cb  TicketCallback )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_TICKET_CALLBACK ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure_ticket_callback () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_ticket_callback ( TLSState, CallbackState, TicketCallback );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureNegotiationCallback ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_NEGO_CALLBACK ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure_nego_callback () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_nego_callback ( TLSState, NULL, NegotiationCallback );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ConfigureCertificateCallbacks ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE_CERT_CALLBACKS ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    mitls_cert_cb CertificateCallbacks;

    // setup the callback functions structure with the wrapper functions (so we can do measurements)

    CertificateCallbacks.format = CertificateFormatCallback;
    CertificateCallbacks.select = CertificateSelectCallback;
    CertificateCallbacks.sign   = CertificateSignCallback;
    CertificateCallbacks.verify = CertificateVerifyCallback;

    fprintf ( DebugFile, "FFI_mitls_configure_cert_callbacks () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure_cert_callbacks ( TLSState, PKIState, &CertificateCallbacks );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

void COMPONENT::Close ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CLOSE ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_close () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    FFI_mitls_close ( TLSState );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************

int COMPONENT::Connect ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONNECT ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_connect () called\n" );

    Tester->ClientComponent->MeasurementNumber = MeasurementNumber; // record the measurement number used for the connect call for use in callbacks

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_connect ( ( void * ) this, ClientSendCallback, ClientReceiveCallback, TLSState );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::AcceptConnected ( void  )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_ACCEPT_CONNECTED ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_accept_connected () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_accept_connected ( ( void * ) this, ServerSendCallback, ServerReceiveCallback, TLSState );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::GetExporter ( int           early,
                             mitls_secret *secret )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_GET_EXPORTER ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_get_exporter () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_get_exporter ( TLSState, early, secret );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

void *COMPONENT::GetCertificate ( size_t *cert_size )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_GET_CERT ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_get_cert () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    void *Certificate = FFI_mitls_get_cert ( TLSState, cert_size );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Certificate );
}

//**********************************************************************************************************************************

int COMPONENT::Send ( const unsigned char *buffer,
                      size_t               buffer_size )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_SEND ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_send () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_send ( TLSState, buffer, buffer_size );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

void *COMPONENT::Receive ( size_t *packet_size )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_RECEIVE ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_receive () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    void *Packet = FFI_mitls_receive ( TLSState, packet_size );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Packet );
}

//**********************************************************************************************************************************

void COMPONENT::Cleanup ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CLEANUP ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_cleanup () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    FFI_mitls_cleanup ();

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************
//
// QUIC API Function wrappers
//
//**********************************************************************************************************************************

mitls_cert_cb CertificateCallbacks =
{
    CertificateCallbacks.select = CertificateSelectCallback,
    CertificateCallbacks.format = CertificateFormatCallback,
    CertificateCallbacks.sign   = CertificateSignCallback,
    CertificateCallbacks.verify = CertificateVerifyCallback,
};

mitls_extension QuicClientTransportParameters =
{
    QuicClientTransportParameters.ext_type     = (uint16_t) 0x1A, // TLS_ET_QUIC_TRANSPORT_PARAMETERS
    QuicClientTransportParameters.ext_data     = (const unsigned char*) "\xff\xff\x00\x05\x0a\x0b\x0c\x0d\x0e\x00",
    QuicClientTransportParameters.ext_data_len = 9,
};

int COMPONENT::QuicCreate ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_QUIC_CREATE ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_quic_create () called\n" );

    // set the right configuration for this test

    Configuration.callback_state = &QUICState;
    Configuration.cert_callbacks = &CertificateCallbacks;
    Configuration.nego_callback  = &NegotiationCallback;

    Configuration.exts       = &QuicClientTransportParameters;
    Configuration.exts_count = 1;

    // and call the API with this config

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_quic_create ( &QUICState, &Configuration );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

quic_result COMPONENT::QuicProcess ( const unsigned char *inBuf,
                                     size_t              *pInBufLen,
                                     unsigned char       *outBuf,
                                     size_t              *pOutBufLen )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_QUIC_PROCESS ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_quic_process () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    quic_result Result = FFI_mitls_quic_process ( QUICState, inBuf, pInBufLen, outBuf, pOutBufLen );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::QuicGetExporter ( int          early,
                                 quic_secret *secret )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_QUIC_GET_EXPORTER ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_quic_get_exporter () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    //int Result = FFI_mitls_quic_get_exporter ( QUICState, early, secret );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( 0 /*Result*/ );
}

//**********************************************************************************************************************************

void COMPONENT::QuicClose ( void )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_QUIC_CLOSE ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_quic_close () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    //FFI_mitls_quic_close ( QUICState );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************

int COMPONENT::GetHelloSummary ( const unsigned char  *buffer,
                                 size_t                buffer_len,
                                 mitls_hello_summary  *summary,
                                 unsigned char       **cookie,
                                 size_t               *cookie_len )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_GET_HELLO_SUMMARY ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_quic_get_hello_summary () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_get_hello_summary ( buffer, buffer_len, summary, cookie, cookie_len );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::FindCustomExtension ( int                   is_server,
                                     const unsigned char  *exts,
                                     size_t                exts_len,
                                     uint16_t              ext_type,
                                     unsigned char       **ext_data,
                                     size_t               *ext_data_len )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_FIND_CUSTOM_EXTENSION ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_find_custom_extension () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_find_custom_extension ( is_server, exts, exts_len, ext_type, ext_data, ext_data_len );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

void COMPONENT::GlobalFree ( void *pv )
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_GLOBAL_FREE ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_global_free () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    FFI_mitls_global_free ( pv );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************
//
// PKI API Function wrappers
//
//**********************************************************************************************************************************

int COMPONENT::InitialisePKI ( void )
{
    signed int         ErrorIndex;
    mipki_config_entry Configuration [ 1 ];

    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_INIT ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    Configuration [ 0 ].cert_file    = ServerCertificateFilename; // only 1 certificate and key
    Configuration [ 0 ].key_file     = ServerCertificateKeyFilename;
    Configuration [ 0 ].is_universal = TRUE;

    fprintf ( DebugFile, "mipki_init () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    PKIState = mipki_init ( Configuration, 1, NULL, &ErrorIndex );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( ErrorIndex );
}

//**********************************************************************************************************************************

void COMPONENT::TerminatePKI ( void )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_FREE ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_free () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    mipki_free ( PKIState );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************

int COMPONENT::AddRootFileOrPath ( const char *CertificateAuthorityFile )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_ADD_ROOT_FILE_OR_PATH ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_add_root_file_or_path () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    int Result = mipki_add_root_file_or_path ( PKIState, CertificateAuthorityFile );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

mipki_chain COMPONENT::SelectCertificate ( mipki_state                  *State,
                                           const unsigned char          *ServerNameIndicator,
                                           size_t                        ServerNameIndicatorLength,
                                           const mitls_signature_scheme *SignatureAlgorithms,
                                           size_t                        SignatureAlgorithmsLength,
                                           mitls_signature_scheme       *SelectedSignatureScheme )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_SELECT_CERTIFICATE ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_select_certificate () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    mipki_chain Chain = mipki_select_certificate ( State,
                                                   (const char *) ServerNameIndicator,
                                                   ServerNameIndicatorLength,
                                                   SignatureAlgorithms,
                                                   SignatureAlgorithmsLength,
                                                   SelectedSignatureScheme );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( Chain );
}

//**********************************************************************************************************************************

int COMPONENT::SignCertificate ( mipki_state           *State,
                                 mipki_chain            CertificatePointer,
                                 const mipki_signature  SignatureAlgorithm,
                                 const char            *Certificate,
                                 size_t                 CertificateLength,
                                 char                  *Signature,
                                 size_t                *SignatureLength )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_SIGN_VERFIY ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_sign_verify () called in Sign Mode\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    int Result = mipki_sign_verify ( State,              // use the state provided by the callback!
                                     CertificatePointer,
                                     SignatureAlgorithm,
                                     Certificate,
                                     CertificateLength,
                                     Signature,
                                     SignatureLength,
                                     MIPKI_SIGN );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::VerifyCertificate ( mipki_state           *State,
                                   mipki_chain            CertificatePointer,
                                   const mipki_signature  SignatureAlgorithm,
                                   const char            *Certificate,
                                   size_t                 CertificateLength,
                                   char                  *Signature,
                                   size_t                *SignatureLength )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_SIGN_VERFIY ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_sign_verify () called in Verify Mode\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    int Result = mipki_sign_verify ( State,              // use the state provided by the callback!
                                     CertificatePointer,
                                     SignatureAlgorithm,
                                     Certificate,
                                     CertificateLength,
                                     Signature,
                                     SignatureLength,
                                     MIPKI_VERIFY );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::ParseChain ( mipki_state *State,        // use the state provided by the callback!
                            const char  *ChainOfTrust, // the certificate chain of trust in TLS network format
                            size_t       ChainLength ) // returns index into CertificateChains []
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_PARSE_CHAIN ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_parse_chain () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    if ( NumberOfChainsAllocated < MAX_CERTIFICATE_CHAINS )
    {
        // keep a record of the chains parsed and the parsed chain

        CertificateChains [ NumberOfChainsAllocated ] = mipki_parse_chain ( State, ChainOfTrust, ChainLength );
    }
    else
    {
        printf ( "Number of certificate chains in component exceeded!\n" );
    }

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( NumberOfChainsAllocated++ );
}

//**********************************************************************************************************************************

mipki_chain COMPONENT::ParseList ( void )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_PARSE_LIST ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_parse_list () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    // mipki_chain Chain = mipki_parse_list ( PKIState, const char **certs, const size_t* certs_len, size_t chain_len );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( NULL );
}

//**********************************************************************************************************************************

size_t COMPONENT::FormatChain ( mipki_state   *State,
                                mipki_chain    ChainOfTrust,
                                unsigned char *ChainBuffer,
                                size_t         ChainBufferLength )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_FORMAT_CHAIN ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_format_chain () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    size_t Result = mipki_format_chain ( State, ChainOfTrust, (char *) ChainBuffer, ChainBufferLength );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

void COMPONENT::FormatAllocation ( mipki_chain Chain )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_FORMAT_ALLOC ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_format_alloc () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    // mipki_format_alloc ( PKIState, Chain, void* init, alloc_callback cb );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************

int COMPONENT::ValidateChain ( mipki_chain Chain )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_VALIDATE_CHAIN ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_validate_chain () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    int Result = mipki_validate_chain ( PKIState, Chain, "" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

void COMPONENT::FreeChain ( mipki_chain Chain )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_FREE_CHAIN ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_free_chain () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    mipki_free_chain ( PKIState, Chain );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );
}

//**********************************************************************************************************************************
