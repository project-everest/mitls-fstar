
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

#include "stdafx.h"
#include "time.h"
#include "windows.h"

#include "Tester.h"

#include "mitlsffi.h" // this is the real interface!
#include "mipki.h"    // interface for the certificate handling

//**********************************************************************************************************************************

 // in SimpleServer.cpp

extern unsigned long DecodePacket ( void *Packet, size_t PacketLength, const char *Title );

extern int PrintSocketError ( void );

extern const char *LookupSignatureAlgorithm ( int   SignatureAlgorithm,
                                              bool *Supported );

//**********************************************************************************************************************************

extern class TLSTESTER *Tester; // to give access to the component instance!!

//**********************************************************************************************************************************

static unsigned int CurrentTestRunNumber = 0; // for use in mipki callbacks which don't have the context

static unsigned int CurrentMeasurementNumber = 0; // for use in mipki callbacks which don't have the context

MEASUREMENTRESULTS *MeasurementResultsArray [ MAX_MEASUREMENT_TYPES ]; // actually indexed by TestRunNumber

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

    "ffi_mitls_certificate_select_callback", // FFI_MITLS_CERTIFICATE_SELECT_CALLBACK
    "ffi_mitls_certificate_format_callback", // FFI_MITLS_CERTIFICATE_FORMAT_CALLBACK
    "ffi_mitls_certificate_sign_callback",   // FFI_MITLS_CERTIFICATE_SIGN_CALLBACK
    "ffi_mitls_certificate_verify_callback", // FFI_MITLS_CERTIFICATE_VERIFY_CALLBACK

    "ffi_mitls_ticket_callback",      // FFI_MITLS_TICKET_CALLBACK
    "ffi_mitls_negotiation_callback", // FFI_MITLS_NEGOTIATION_CALLBACK
    "ffi_mitls_trace_callback"        // FFI_MITLS_TRACE_CALLBACK
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
// MEASUREMENT Functions
//
//**********************************************************************************************************************************

void InitialiseMeasurementResults ( void )
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

void AllocateMeasurementResult ( int TestRunNumber )
{
    MeasurementResultsArray [ TestRunNumber ] = ( MEASUREMENTRESULTS * ) malloc ( sizeof ( MEASUREMENTRESULTS ) );

    if ( MeasurementResultsArray [ TestRunNumber ] == NULL )
    {
        printf ( "Could not allocate memory for measurement type %d. This is a FATAL error!\n", TestRunNumber );

        exit ( EXIT_FAILURE );
    }
}

//**********************************************************************************************************************************

void FreeMeasurementResults ( void )
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

void InitialiseMeasurementResult ( MEASUREMENTRESULTS *MeasurementResult )
{
    COMPONENTMEASUREMENTENTRY *ComponentMeasurementEntry = NULL;
    CALLBACKMEASUREMENTENTRY  *CallbackMeasurementEntry  = NULL;
    COMPONENTMEASUREMENT      *ComponentMeasurement      = NULL;

    MeasurementResult->StartTime.QuadPart = 0;
    MeasurementResult->EndTime.QuadPart   = 0;

    for ( int MeasurementNumber = 0; MeasurementNumber < MAX_MEASUREMENTS; MeasurementNumber++ )
    {
        ComponentMeasurement = &MeasurementResult->Measurements [ MeasurementNumber ];

        ComponentMeasurement->StartTime.QuadPart = 0;
        ComponentMeasurement->EndTime.QuadPart   = 0;

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

void PrintMeasurementResults ( FILE *MeasurementsResultFile )
{
    MEASUREMENTRESULTS *MeasurementResult = NULL;

    // write the measurements to the recorded measurements file

    for ( int TestRunNumber = 0; TestRunNumber < MAX_MEASUREMENT_TYPES; TestRunNumber++ )
    {
        MeasurementResult = MeasurementResultsArray [ TestRunNumber ];

        // only print out the test runs which were actually recorded

        if ( MeasurementResult != NULL ) // was memory allocated?
        {
            if ( MeasurementResult->StartTime.QuadPart != 0 ) // did the measurement take place?
            {
                PrintMeasurementResult ( MeasurementsResultFile, MeasurementResult );
            }
        }
    }
}

//**********************************************************************************************************************************

void PrintMeasurementResult ( FILE               *MeasurementsResultFile,
                              MEASUREMENTRESULTS *MeasurementResult )
{
    COMPONENTMEASUREMENTENTRY *ComponentMeasurementEntry = NULL;
    CALLBACKMEASUREMENTENTRY  *CallbackMeasurementEntry  = NULL;
    COMPONENTMEASUREMENT      *ComponentMeasurement      = NULL;

    fprintf ( MeasurementsResultFile, "Measurement Type = %s\n", MeasurementResult->MeasurementTypeName );

    fprintf ( MeasurementsResultFile, "Measurement StartTime = %I64u\n", MeasurementResult->StartTime.QuadPart );

    fprintf ( MeasurementsResultFile, "Measurement EndTime = %I64u\n", MeasurementResult->EndTime.QuadPart );

    for ( int MeasurementNumber = 0; MeasurementNumber < MAX_MEASUREMENTS; MeasurementNumber++ )
    {
        ComponentMeasurement = &MeasurementResult->Measurements [ MeasurementNumber ];

        // only print out the measurements which were actually recorded

        if ( ComponentMeasurement->StartTime.QuadPart == 0 ) break;

        fprintf ( MeasurementsResultFile, "\nMeasurement Results Entry [ %d ]\n\n", MeasurementNumber );

        fprintf ( MeasurementsResultFile, "Component Test Start Time = %I64u\n", ComponentMeasurement->StartTime.QuadPart );
        fprintf ( MeasurementsResultFile, "Component Test End Time   = %I64u\n", ComponentMeasurement->EndTime.QuadPart   );

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

void RecordTestRunStartTime ( int TestRunNumber )
{
     QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->StartTime );
}

//**********************************************************************************************************************************

void RecordTestRunEndTime ( int TestRunNumber )
{
     QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->EndTime );
}

//**********************************************************************************************************************************
//
// Threads
//
//**********************************************************************************************************************************


//**********************************************************************************************************************************
//
// FFI Callback Function wrappers
//
//**********************************************************************************************************************************

void MITLS_CALLCONV TicketCallback ( void               *cb_state,
                                     const char         *sni,
                                     const mitls_ticket *ticket )
{
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_TICKET_CALLBACK ];

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
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_NEGOTIATION_CALLBACK ];

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Negotiation callback function invoked!\n" );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( TLS_nego_accept );
}

//**********************************************************************************************************************************

void MITLS_CALLCONV TraceCallback ( const char *msg )
{
    printf ( ASES_SET_FOREGROUND_YELLOW );

    printf ( msg );

    printf ( ASES_SET_FOREGROUND_BLACK );
}

//**********************************************************************************************************************************

static unsigned char LargeTransmitBuffer [ 65536 ]; // almost the maximum packet the network will process in one go

static unsigned int LargeTransmitBufferReadIndex = 0;

static unsigned int AmountTransmitted = 0;

static unsigned int ExpectedRecordLength = 0;

static bool IncompleteTransmission = FALSE;

int MITLS_CALLCONV SendCallback ( void                *Context,
                                  const unsigned char *Buffer,
                                  size_t               BufferSize )
{
    size_t                    AmountSent             = 0;
    COMPONENT                *Component              = ( COMPONENT * ) Context;
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_SEND_CALLBACK ];

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    if ( Tester->ConsoleDebugging ) printf ( "Send callback function invoked for %zd octets!\n", BufferSize );

    // The component sends the records in sections now (Aug 2018) so we have to send this right away

    AmountSent = send ( Component->Socket, (char * ) Buffer, (int) BufferSize, 0 );

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

// PROBLEM: MITLS requests data from the server in sections. It reads the header first and then depending on the fragment length,
//          reads that fragment. However this makes debugging very difficult as the whole record is needed for this. The solution
//          is to read the complete response from the peer and then return it bit by bit as requested by MITLS. So the call back
//          function will read the data from a local buffer rather than from the network buffer.
//

static unsigned char LargeReceiveBuffer [ 65536 ]; // almost the maximum packet the network will return in one go

static unsigned int LargeBufferReadIndex = 0;

static int AmountReceived = 0;

static bool IncompleteTransfer = FALSE;

int MITLS_CALLCONV ReceiveCallback ( void          *Context,
                                     unsigned char *Buffer,
                                     size_t         BufferSize )
{
    size_t                    AmountTransferred      = 0;
    size_t                    AmountRemaining        = 0;
    COMPONENT                *Component              = ( COMPONENT * ) Context;
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_RECEIVE_CALLBACK ];

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    // if console debugging is enabled then we need to buffer the network packet to decode it and return only the requested amount.

    if ( Tester->ConsoleDebugging )
    {
        printf ( "Receive callback function invoked (with room for %zu octets)!\n", BufferSize );

        // yes, so did the previous call result in an incomplete transfer?

        if ( IncompleteTransfer == FALSE )
        {
            // No, so get as much as the network will provide

            LargeBufferReadIndex = 0;

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
            AmountRemaining = AmountReceived - LargeBufferReadIndex;

            if ( AmountRemaining > BufferSize )
            {
                memcpy ( Buffer, &LargeReceiveBuffer [ LargeBufferReadIndex ], BufferSize );

                AmountTransferred = BufferSize;

                IncompleteTransfer = TRUE; // still more left so still incomplete
            }
            else
            {
                memcpy ( Buffer, &LargeReceiveBuffer [ LargeBufferReadIndex ], AmountRemaining );

                AmountTransferred = AmountRemaining;

                IncompleteTransfer = FALSE; // no more left now so transfer complete
            }

            LargeBufferReadIndex += AmountTransferred;
        }
    }
    else
    {
        // no, so just return the amount requested from the network

        AmountTransferred = recv ( Component->Socket, (char * ) Buffer, BufferSize, 0 );
    }

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( (int) AmountTransferred );
}

//**********************************************************************************************************************************

void *MITLS_CALLCONV CertificateSelectCallback ( void                         *cb_state,
                                                 mitls_version                 ver,
                                                 const unsigned char          *sni,
                                                 size_t                        sni_len,
                                                 const unsigned char          *alpn,
                                                 size_t                        alpn_len,
                                                 const mitls_signature_scheme *sigalgs,
                                                 size_t                        sigalgs_len,
                                                 mitls_signature_scheme       *selected )
{
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_CERTIFICATE_SELECT_CALLBACK ];

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Select Callback function invoked!\n" );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( NULL );
}

//**********************************************************************************************************************************

size_t MITLS_CALLCONV CertificateFormatCallback ( void          *cb_state,
                                                  const void    *cert_ptr,
                                                  unsigned char buffer [ MAX_CHAIN_LEN ] )
{
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_CERTIFICATE_FORMAT_CALLBACK ];

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Format Callback function invoked!\n" );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( 0 );
}

//**********************************************************************************************************************************

size_t MITLS_CALLCONV CertificateSignCallback ( void                         *cb_state,
                                                const void                   *cert_ptr,
                                                const mitls_signature_scheme  sigalg,
                                                const unsigned char          *tbs,
                                                size_t                        tbs_len,
                                                unsigned char                *sig )
{
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement = NULL;
    unsigned int              CallCount              = 0;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_CERTIFICATE_SIGN_CALLBACK ];

    CallCount = FFICallbackMeasurement->NumberOfCalls++;

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->StartTimes [ CallCount ] );
    }

    printf ( "Certificate Sign Callback function invoked!\n" );

    if ( CallCount < MAX_CALLBACK_CALLS_PER_MEASUREMENT )
    {
        QueryPerformanceCounter ( &FFICallbackMeasurement->EndTimes [ CallCount ] );
    }

    return ( 0 );
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
    CALLBACKMEASUREMENTENTRY *FFICallbackMeasurement  = NULL;
    unsigned int              CallCount               = 0;
    int                       Result                  = 0;
    size_t                    VerifiedSignatureLength = SignatureLength;

    FFICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].FFICallbackMeasurements [ FFI_MITLS_CERTIFICATE_VERIFY_CALLBACK ];

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

    int ChainNumber = Tester->Component->ParseChain ( (mipki_state *) State, (const char *) ChainOfTrust, ChainLength );

    if ( Tester->Component->CertificateChains [ ChainNumber ] != NULL )
    {
        Result = Tester->Component->ValidateChain ( Tester->Component->CertificateChains [ ChainNumber ] );

        if ( ! Result )
        {
            if ( Tester->ConsoleDebugging )
            {
                if ( Tester->ConsoleDebugging ) printf ( "Chain Validation failed!\n" ); // comment on result but otherwise ignore it
            }
        }

         Result = Tester->Component->VerifyCertificate ( (mipki_state *) State,
                                                        Tester->Component->CertificateChains [ ChainNumber ],
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

        Tester->Component->FreeChain ( Tester->Component->CertificateChains [ ChainNumber ] );

        Tester->Component->CertificateChains [ ChainNumber ] = NULL;
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

    PKICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].PKICallbackMeasurements [ MIPKI_PASSWORD_CALLBACK ];

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

    PKICallbackMeasurement = &MeasurementResultsArray [ CurrentTestRunNumber ]->Measurements [ CurrentMeasurementNumber ].PKICallbackMeasurements [ MIPKI_ALLOC_CALLBACK ];

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
// COMPONENT Methods
//
//**********************************************************************************************************************************

COMPONENT::COMPONENT ( TLSTESTER *Parent,  FILE *NewDebugFile )
{
    Tester = Parent;

    DebugFile = NewDebugFile;

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

    TestRunNumber = 0;

    MeasurementNumber = 0;

    NumberOfMeasurementsMade = 0;

    // initialise certificate chain variables

    NumberOfChainsAllocated = 0; // index into CertificateChains

    for ( int ChainNumber = 0; ChainNumber < MAX_CERTIFICATE_CHAINS; ChainNumber++ )
    {
        CertificateChains [ ChainNumber ] = NULL;
    }

    // initialise measurement results global variables

    CurrentTestRunNumber = 0;

    CurrentMeasurementNumber = 0;

    CurrentComponentMeasurement = &MeasurementResultsArray [ 0 ]->Measurements [ 0 ]; // set to the first test and measurement

    InitialiseMeasurementResults ();
}

//**********************************************************************************************************************************

COMPONENT::~COMPONENT ( void )
{
    FreeMeasurementResults ();
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

    CurrentTestRunNumber = TestRunNumber;

    // when we change the test run number, the measurements should start at 0 again

    SetMeasurementNumber ( 0 );
}

//**********************************************************************************************************************************

void COMPONENT::SetMeasurementNumber ( int NewMeasurementNumber )
{
    MeasurementNumber = NewMeasurementNumber;

    CurrentMeasurementNumber = MeasurementNumber;

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

void COMPONENT::RecordStartTime ( void )
{
    QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->Measurements [ MeasurementNumber ].StartTime );
}

//**********************************************************************************************************************************

void COMPONENT::RecordEndTime ( void )
{
    QueryPerformanceCounter ( &MeasurementResultsArray [ TestRunNumber ]->Measurements [ MeasurementNumber ].EndTime );
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

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_configure ( &TLSState, TLSVersion, HostName ); // note that this one requires a state double pointer!

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->EndTimes [ CallCount ] );

    return ( Result );
}

//**********************************************************************************************************************************

int COMPONENT::Configure ( char *UseThisHostName ) // configure using the specified host name
{
    COMPONENTMEASUREMENTENTRY *FFIComponentMeasurement = &CurrentComponentMeasurement->FFIMeasurements [ FFI_MITLS_CONFIGURE ];

    int CallCount = FFIComponentMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "FFI_mitls_configure () called\n" );

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

void COMPONENT::CloseConnection ( void )
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

    CurrentMeasurementNumber = MeasurementNumber; // record the measurement number used for the connect call for use in callbacks

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &FFIComponentMeasurement->StartTimes [ CallCount ] );

    int Result = FFI_mitls_connect ( ( void * ) this, SendCallback, ReceiveCallback, TLSState );

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

    int Result = FFI_mitls_accept_connected ( ( void * ) this, SendCallback, ReceiveCallback, TLSState  );

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

mipki_chain COMPONENT::SelectCertificate ( void )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_SELECT_CERTIFICATE ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_select_certificate () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    // mipki_chain Chain = mipki_select_certificate ( PKIState, const char *sni, size_t sni_len, const mipki_signature *algs, size_t algs_len, mipki_signature *selected );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( NULL );
}

//**********************************************************************************************************************************

int COMPONENT::SignCertificate ( mipki_chain CertificatePointer )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_SIGN_VERFIY ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_sign_verify () called in Sign Mode\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    // int Result = mipki_sign_verify ( PKIState, CertificatePointer, const mipki_signature sigalg, const char *tbs, size_t tbs_len, char *sig, size_t *sig_len, MIPKI_SIGN );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( 0 );
}

//**********************************************************************************************************************************

int COMPONENT::VerifyCertificate ( mipki_state           *State,               // use the state provided by the callback!
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

    int Result = mipki_sign_verify ( State,
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

int COMPONENT::FormatChain ( mipki_chain Chain )
{
    COMPONENTMEASUREMENTENTRY *PKILibraryMeasurement = &CurrentComponentMeasurement->PKIMeasurements [ MIPKI_FORMAT_CHAIN ];

    int CallCount = PKILibraryMeasurement->NumberOfCalls++;

    fprintf ( DebugFile, "mipki_format_chain () called\n" );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->StartTimes [ CallCount ] );

    // size_t Result = mipki_format_chain ( PKIState, Chain, char *buffer, size_t buffer_len );

    if ( CallCount < MAX_COMPONENT_CALLS_PER_MEASUREMENT ) QueryPerformanceCounter ( &PKILibraryMeasurement->EndTimes [ CallCount ] );

    return ( 0 );
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
