
//**********************************************************************************************************************************
//
//   Purpose: TLSTESTER OBJECT source code file
//
//   Project: Everest
//
//  Filename: TLSTester.cpp
//
//   Authors: Caroline.M.Mathieson (CMM)
//
//**********************************************************************************************************************************
//
//  Description
//  -----------
//
//! \file TLSTester.cpp
//! \brief Contains the complete implementation of the TLSTESTER Object. This covers TLS tester attributes and functions.
//!
//**********************************************************************************************************************************

#include "Tester.h" // pulls in everything else

//**********************************************************************************************************************************

// see https://github.com/project-everest/mitls-fstar/blob/e2490b839c46beac96c0900beee4d19111355b21/src/tls/FFI.fst#L244

static const int NumberOfCipherSuites = 14;

static const char *SupportedCipherSuites [ NumberOfCipherSuites ] =
{
    // these are the cipher suites offered by default in the ClientHello

    "TLS_AES_128_GCM_SHA256",
    "TLS_AES_256_GCM_SHA384",
    "TLS_CHACHA20_POLY1305_SHA256",
    "TLS_AES_128_CCM_SHA256",
    "TLS_AES_128_CCM_8_SHA256",
    "ECDHE-RSA-AES256-GCM-SHA384",
    "ECDHE-RSA-AES128-GCM-SHA256",
    "ECDHE-RSA-CHACHA20-POLY1305-SHA256",
    "ECDHE-ECDSA-AES256-GCM-SHA384",
    "ECDHE-ECDSA-AES128-GCM-SHA256",
    "ECDHE-ECDSA-CHACHA20-POLY1305-SHA256",
    "DHE-RSA-AES256-GCM-SHA384",
    "DHE-RSA-AES128-GCM-SHA256",
    "DHE-RSA-CHACHA20-POLY1305-SHA256",
};

//**********************************************************************************************************************************

// See https://github.com/project-everest/mitls-fstar/blob/master/src/tls/TLSConstants.fst and
// https://github.com/project-everest/mitls-fstar/blob/e2490b839c46beac96c0900beee4d19111355b21/src/tls/FFI.fst#L244

static const int NumberOfSignatureAlgorithms = 11;

static const char *SupportedSignatureAlgorithms [ NumberOfSignatureAlgorithms ] =
{
    "RSAPSS+SHA512",
    "RSAPSS+SHA384",
    "RSAPSS+SHA256",
    "RSA+SHA512",
    "RSA+SHA384",
    "RSA+SHA256",
    "RSA+SHA1",
    "ECDSA+SHA512",
    "ECDSA+SHA384",
    "ECDSA+SHA256",
    "ECDSA+SHA1",

    // these are the signature algorithms offered by default in the ClientHello Signature Algorithms Extension

    // legacy algorithms
//  "RSA_PKCS1_SHA1",    // no longer supported in kremlin code
//  "RSA_PKCS1_MD5SHA1", // only used internally for now
//  "ECDSA_SHA1",        // no longer supported in kremlin code

    // Not sure what these are (nothing in header file
//  "RSA_PKCS1_SHA256",
//  "RSA_PKCS1_SHA384",
//  "RSA_PKCS1_SHA512",

    // RSASSA-PSS Algorithms
//  "RSA_PSS_SHA256",
//  "RSA_PSS_SHA384",
//  "RSA_PSS_SHA512",

    // ECDSA Algorithms
//  "ECDSA_SECP256R1_SHA256:",
//  "ECDSA_SECP384R1_SHA384",
//  "ECDSA_SECP521R1_SHA512",

    // EDDSA Algorithms
//  "ED25519_SHA512",
//  "ED448_SHAKE256",

    // Reserved code points
//  "DSA_SHA1",
//  "DSA_SHA256",
//  "DSA_SHA384",
//  "DSA_SHA512",

    // old list
//  "ECDSA+SHA256",
//  "ECDSA+SHA384",
//  "ECDSA+SHA512",

};

//**********************************************************************************************************************************

// see https://github.com/project-everest/mitls-fstar/blob/master/src/tls/CommonDH.fst and
// https://github.com/project-everest/mitls-fstar/blob/e2490b839c46beac96c0900beee4d19111355b21/src/tls/FFI.fst#L244

static const int NumberOfNamedGroups = 8;

static const char *SupportedNamedGroups [ NumberOfNamedGroups ] =
{
    "P-521",
    "P-384",
    "P-256",
    "X25519",
    "X448",
    "FFDHE4096",
    "FFDHE3072",
    "FFDHE2048",
};

//**********************************************************************************************************************************

TLSTESTER::TLSTESTER (  FILE *DebugFile,
                        FILE *TestResultsFile,
                        FILE *RecordedClientMeasurementsFile,
                        FILE *RecordedServerMeasurementsFile ) :  TESTER ( DebugFile,
                                                                           TestResultsFile,
                                                                           RecordedClientMeasurementsFile,
                                                                           RecordedServerMeasurementsFile )
{
    ClientComponent = NULL; // we instantiate it in the client config method
    ServerComponent = NULL; // we instantiate it in the server config method

    // set the default values here in case they are not over-ridden by command line arguments

    strcpy ( HostFileName, "\0" );

    NumberOfHostsRead = 0;

    memset ( HostNames, 0, sizeof ( HostNames ) );

    strcpy ( TLSVersion, "1.3" );

    strcpy ( HostName, "google.com" );

    PortNumber = 443;

    // certificate attributes

    strcpy ( ClientCertificateFilename,    "server-ecdsa.crt" );
    strcpy ( ClientCertificateKeyFilename, "server-ecdsa.key" );
    strcpy ( ServerCertificateFilename,    "server-ecdsa.crt" );
    strcpy ( ServerCertificateKeyFilename, "server-ecdsa.key" );

    strcpy ( CertificateAuthorityChainFilename, "CAFile.pem" );

    // command line over-ride flags

    GenerateImageFiles = FALSE;

    UseHostList = FALSE;

    UseHostName = FALSE;

    UsePortNumber = FALSE;

    DoTLSTests    = FALSE;
    DoQUICTests   = FALSE;
    DoClientTests = FALSE;
    DoServerTests = FALSE;

    DoDefaultTests     = FALSE;
    DoCombinationTests = FALSE;

    DoClientInteroperabilityTests = FALSE;
    DoServerInteroperabilityTests = FALSE;

    // thread attributes

    ClientTLSTestsThreadIdentifier = 0;
    ServerTLSTestsThreadIdentifier = 0;

    ClientTLSTestsThreadHandle = INVALID_HANDLE_VALUE;
    ServerTLSTestsThreadHandle = INVALID_HANDLE_VALUE;
}

//**********************************************************************************************************************************

void TLSTESTER::ConfigureClient ( void )
{
    bool Result;

    ClientComponent = new COMPONENT ( this, DebugFile, FALSE );

    // configure the ClientComponent attributes using the command line arguments if any given or the defaults otherwise

    if ( ClientComponent != NULL )
    {
        ClientComponent->IsServer = FALSE;

        ClientComponent->SetVersion ( TLSVersion );

        ClientComponent->SetHostName ( HostName );

        ClientComponent->SetPortNumber ( PortNumber );

        ClientComponent->SetClientCertificateFilename ( ClientCertificateFilename );

        ClientComponent->SetClientCertificateKeyFilename ( ClientCertificateKeyFilename );

        ClientComponent->SetServerCertificateFilename ( ServerCertificateFilename );

        ClientComponent->SetServerCertificateKeyFilename ( ServerCertificateKeyFilename );
    }
}

//**********************************************************************************************************************************

void TLSTESTER::ConfigureServer ( void )
{
    bool Result;

    ServerComponent = new COMPONENT ( this, DebugFile, TRUE );

    // configure the ServerComponent attributes using the command line arguments if any given or the defaults otherwise

    if ( ServerComponent != NULL )
    {
        ServerComponent->IsServer = TRUE;

        ServerComponent->SetVersion ( TLSVersion );

        ServerComponent->SetHostName ( HostName );

        ServerComponent->SetPortNumber ( PortNumber );

        ServerComponent->SetClientCertificateFilename ( ClientCertificateFilename );

        ServerComponent->SetClientCertificateKeyFilename ( ClientCertificateKeyFilename );

        ServerComponent->SetServerCertificateFilename ( ServerCertificateFilename );

        ServerComponent->SetServerCertificateKeyFilename ( ServerCertificateKeyFilename );
    }
}

//**********************************************************************************************************************************

TLSTESTER::~TLSTESTER ( void )
{
    if ( ClientComponent != NULL )
    {
        ClientComponent->PrintMeasurementResults ( RecordedClientMeasurementsFile );

        delete ClientComponent;
    }

    if ( ServerComponent != NULL )
    {
        ServerComponent->PrintMeasurementResults ( RecordedServerMeasurementsFile );

        delete ServerComponent;
    }
}

//**********************************************************************************************************************************

void TLSTESTER::RunClientTLSTests ( char *TestDateAndTimeString )
{
    DateAndTimeString = TestDateAndTimeString; // record the date and time of the test

    ClientTestsFinished = FALSE;

    ClientTLSTestsThreadHandle = CreateThread ( NULL,                              // default security attributes
                                                0,                                 // use default stack size
                                                ClientTLSTestsThread,              // thread function name
                                                this,                              // argument to thread function is class instance
                                                0,                                 // use default creation flags
                                                &ClientTLSTestsThreadIdentifier ); // returns the thread identifier

    while ( ! ClientTestsFinished ) Sleep ( 1000 ); // wait for thread to finish
}

//**********************************************************************************************************************************

void TLSTESTER::RunServerTLSTests ( char *TestDateAndTimeString )
{
    DateAndTimeString = TestDateAndTimeString; // record the date and time of the test

    ClientTestsFinished = FALSE;
    ServerTestsFinished = FALSE;

    ServerTLSTestsThreadHandle = CreateThread ( NULL,                              // default security attributes
                                                0,                                 // use default stack size
                                                ServerTLSTestsThread,              // thread function name
                                                this,                              // argument to thread function is class instance
                                                0,                                 // use default creation flags
                                                &ServerTLSTestsThreadIdentifier ); // returns the thread identifier

    // now that the server thread is running, start the client thread after a while

    Sleep ( 1000 );

    ClientTLSTestsThreadHandle = CreateThread ( NULL,                              // default security attributes
                                                0,                                 // use default stack size
                                                ClientServerTLSTestsThread,        // thread function name
                                                this,                              // argument to thread function is class instance
                                                0,                                 // use default creation flags
                                                &ClientTLSTestsThreadIdentifier ); // returns the thread identifier

    while ( ( ! ServerTestsFinished ) && ( ! ClientTestsFinished ) )
    {
        Sleep ( 1000 ); // wait for both threads to finish
    }
}

//**********************************************************************************************************************************

DWORD WINAPI ClientTLSTestsThread ( LPVOID lpParam )
{
    TLSTESTER *Tester = (TLSTESTER *) lpParam;

    Tester->ClientTLSTests ();

    Tester->ClientTestsFinished = TRUE;

    ExitThread ( 0 );
}

//**********************************************************************************************************************************

DWORD WINAPI ClientServerTLSTestsThread ( LPVOID lpParam )
{
    TLSTESTER *Tester = (TLSTESTER *) lpParam;

    Tester->ClientServerTLSTests ();

    Tester->ClientTestsFinished = TRUE;

    ExitThread ( 0 );
}

//**********************************************************************************************************************************

DWORD WINAPI ServerTLSTestsThread ( LPVOID lpParam )
{
    TLSTESTER *Tester = (TLSTESTER *) lpParam;

    Tester->ServerTLSTests ();

    Tester->ServerTestsFinished = TRUE;

    ExitThread ( 0 );
}

//**********************************************************************************************************************************

void TLSTESTER::ClientTLSTests ( void )
{
    int  MeasurementNumber = 0;
    long ExecutionTime     = 0;
    int  Result            = 0;
    int  ErrorIndex        = 0;
    bool Success           = FALSE;

    ClientComponent->SetTestRunNumber ( TLS_CLIENT_MEASUREMENTS );

    ClientComponent->RecordTestRunStartTime ();

    Result = ClientComponent->InitialiseTLS ();

    if ( ! Result ) { printf ( "Failed to Initialise TLS for client!\n" ); return; }

    ClientComponent->ConfigureTraceCallback ();

    ErrorIndex = ClientComponent->InitialisePKI ();

    if ( ErrorIndex != 0 ) { printf ( "Failed to Initialise PKI for client!\n" ); return; }

    if ( DoDefaultTests )
    {
        //
        // Run a measurement for just the default host, cipher suite, signature algorithm and named group
        //

        QueryPerformanceCounter ( &MeasurementStartTime ); // just for this measurement to give a quick result below

        Success = RunSingleClientDefaultsTLSTest ( MeasurementNumber );

        QueryPerformanceCounter ( &MeasurementEndTime );

        ExecutionTime = CalculateExecutionTime ( MeasurementStartTime, MeasurementEndTime );

        if ( Success )
        {
            fprintf ( ComponentStatisticsFile,
                      "%s, %d, %d, %s, Default, Default, Default, PASS, %u\n",
                      DateAndTimeString,
                      ClientComponent->TestRunNumber,
                      MeasurementNumber,
                      ClientComponent->GetHostName (),
                      ExecutionTime );
        }
        else
        {
            fprintf ( ComponentStatisticsFile,
                      "%s, %d, %d, %s, Default, Default, Default, FAIL, %u\n",
                      DateAndTimeString,
                      ClientComponent->TestRunNumber,
                      MeasurementNumber,
                      ClientComponent->GetHostName (),
                      ExecutionTime );
        }

        MeasurementNumber++;
    }

    if ( DoCombinationTests )
    {
        //
        // Then run a measurement for each combination of supported cipher suite, signature algorithm and named groups
        // for all specified hosts.
        //
        if ( UseHostList )
        {
            for ( int HostNumber = 0; HostNumber < NumberOfHostsRead; HostNumber++ )
            {
                ClientComponent->SetHostName ( HostNames [ HostNumber ] );

                MeasurementNumber = RunCombinationTest ( MeasurementNumber, HostNames [ HostNumber ] );
            }
        }
        else
        {
            MeasurementNumber = RunCombinationTest ( MeasurementNumber, HostName );
        }
    }

    ClientComponent->TerminatePKI ();

    ClientComponent->Cleanup ();

    ClientComponent->RecordTestRunEndTime ();

    // add this set of tests to the total run

    ClientComponent->NumberOfMeasurementsMade += MeasurementNumber;
}

void TLSTESTER::ClientServerTLSTests ( void )
{
    int  MeasurementNumber = 0;
    long ExecutionTime     = 0;
    int  Result            = 0;
    int  ErrorIndex        = 0;
    bool Success           = FALSE;

    ClientComponent->SetTestRunNumber ( TLS_SERVER_MEASUREMENTS );

    ClientComponent->RecordTestRunStartTime ();
    ServerComponent->RecordTestRunStartTime ();

    // server tests mean that the servers are all local

    ClientComponent->SetHostName ( "localhost" );
    ServerComponent->SetHostName ( "localhost" );

    Result = ClientComponent->InitialiseTLS ();

    if ( ! Result ) { printf ( "Failed to Initialise TLS for clientserver tests!\n" ); return; }

    ClientComponent->ConfigureTraceCallback ();

    ErrorIndex = ClientComponent->InitialisePKI ();

    if ( ErrorIndex != 0 ) { printf ( "Failed to Initialise PKI for clientserver tests!\n" ); return; }

    if ( DoDefaultTests )
    {
        //
        // Run a measurement for just the default host, cipher suite, signature algorithm and named group
        //

        QueryPerformanceCounter ( &MeasurementStartTime ); // just for this measurement to give a quick result below

        Success = RunSingleServerDefaultsTLSTest ( MeasurementNumber );

        QueryPerformanceCounter ( &MeasurementEndTime );

        ExecutionTime = CalculateExecutionTime ( MeasurementStartTime, MeasurementEndTime );

        if ( Success )
        {
            fprintf ( ComponentStatisticsFile,
                      "%s, %d, %s, Default, Default, Default, PASS, %u\n",
                      DateAndTimeString,
                      /*ClientComponent->NumberOfMeasurementsMade +*/ MeasurementNumber,
                      ClientComponent->GetHostName (),
                      ExecutionTime );
        }
        else
        {
            fprintf ( ComponentStatisticsFile,
                      "%s, %d, %s, Default, Default, Default, FAIL, %u\n",
                      DateAndTimeString,
                      /*ClientComponent->NumberOfMeasurementsMade +*/ MeasurementNumber,
                      ClientComponent->GetHostName (),
                      ExecutionTime );
        }

        MeasurementNumber++;
    }

    if ( DoCombinationTests )
    {
        MeasurementNumber = RunCombinationTest ( MeasurementNumber, HostName );
    }

    ClientComponent->TerminatePKI ();

    ClientComponent->Cleanup ();

    ClientComponent->RecordTestRunEndTime ();
    ServerComponent->RecordTestRunEndTime ();

    // add this set of tests to the total run

    ClientComponent->NumberOfMeasurementsMade += MeasurementNumber;
    ServerComponent->NumberOfMeasurementsMade += MeasurementNumber;
}

//**********************************************************************************************************************************

void TLSTESTER::ServerTLSTests ( void )
{
    int  MeasurementNumber = 0;
    long ExecutionTime     = 0;
    int  Result            = 0;
    int  ErrorIndex        = 0;
    bool Success           = FALSE;

    ConfigureServer (); // create and initialise a component for server dll access

    ServerComponent->SetTestRunNumber ( TLS_SERVER_MEASUREMENTS );

    //ServerComponent->RecordTestRunStartTime ();

    Result = ServerComponent->InitialiseTLS ();

    if ( ! Result ) { printf ( "Failed to Initialise TLS!\n" ); return; }

    ServerComponent->ConfigureTraceCallback ();

    ErrorIndex = ServerComponent->InitialisePKI ();

    if ( ErrorIndex != 0 ) { printf ( "Failed to Initialise PKI for server!\n" ); return; }

    // run client tests with the server running

    Result = ServerComponent->AddRootFileOrPath ( CertificateAuthorityChainFilename ); // must be done before the configure

    if ( Result )
    {
        // server is local in these tests so set host names accordingly

        ClientComponent->SetHostName ( "localhost" );
        ServerComponent->SetHostName ( "localhost" );

        Result = ServerComponent->Configure (); // set default TLS version

        if ( Result )
        {
            Result = ServerComponent->ConfigureCertificateCallbacks ();

            if ( Result )
            {
                Result = ServerComponent->ConfigureNegotiationCallback ();

                if ( Result )
                {
                    while ( ! ClientTestsFinished ) // keep repeating while the client tests are stil running
                    {
                        fprintf ( stderr, "Server waiting for incoming connect () from client\n" );

                        Result = ServerComponent->AcceptConnected ();

                        //
                        // The component will call the send() and receive() callback functions to perform the handshake and the
                        // AcceptConnected () function call returns only when the handshake is complete.
                        //

                        if ( Result )
                        {
                            if ( VerboseConsoleOutput ) printf ( "ServerComponent->ConnectAccepted() was successful!\n" );

                            // don't do any data transfer in this particular test

                            // ServerComponent->Receive (); // get any data sent

                            // ServerComponent->Free; // free the received item

                            // ServerComponent->Send (); // send any data

                            // ServerComponent->CloseConnection (); //its hard to know how long to wait for this before we call it.

                            Success = TRUE;
                        }
                        else
                        {
                           fprintf ( stderr, "ServerComponent->AcceptConnected() failed!\n" );
                        }

                    } // end while
                }
                else
                {
                    fprintf ( stderr, "ServerComponent->ConfigureNegotiationCallback () failed!\n" );
                }
            }
            else
            {
                fprintf ( stderr, "ServerComponent->ConfigureCertificateCallbacks () failed!\n" );
            }
        }
        else
        {
            fprintf ( stderr, "ServerComponent->Configure() failed!\n" );
        }
    }
    else
    {
        fprintf ( stderr, "ServerComponent->AddRootFileOrPath () failed!\n" );
    }

    ServerComponent->TerminatePKI ();

    //ServerComponent->Cleanup ();

    //ServerComponent->RecordTestRunEndTime ();
}

//**********************************************************************************************************************************

int TLSTESTER::RunCombinationTest ( int   MeasurementNumber,
                                    char *HostName )
{
    int  CipherSuiteNumber        = 0;
    int  SignatureAlgorithmNumber = 0;
    int  NamedGroupNumber         = 0;
    int  Success                  = 0;
    long ExecutionTime            = 0;
    char *TestResult              = "FAIL"; // or "PASS"

    for ( CipherSuiteNumber = 0; CipherSuiteNumber < NumberOfCipherSuites; CipherSuiteNumber++ )
    {
        for ( SignatureAlgorithmNumber = 0; SignatureAlgorithmNumber < NumberOfSignatureAlgorithms; SignatureAlgorithmNumber++ )
        {
            for ( NamedGroupNumber = 0; NamedGroupNumber < NumberOfNamedGroups; NamedGroupNumber++ )
            {
                QueryPerformanceCounter ( &MeasurementStartTime ); // just for this measurement to give a quick result below

                Success = RunSingleClientTLSTest ( MeasurementNumber,
                                                   SupportedCipherSuites        [ CipherSuiteNumber        ],
                                                   SupportedSignatureAlgorithms [ SignatureAlgorithmNumber ],
                                                   SupportedNamedGroups         [ NamedGroupNumber         ] );

                QueryPerformanceCounter ( &MeasurementEndTime );

                ExecutionTime = CalculateExecutionTime ( MeasurementStartTime, MeasurementEndTime );

                if ( Success ) TestResult = "PASS";

                fprintf ( ComponentStatisticsFile,
                          "%s, %d, %s, %s, %s, %s, %s, %u\n",
                          DateAndTimeString,
                          ClientComponent->NumberOfMeasurementsMade + MeasurementNumber,
                          HostName,
                          SupportedCipherSuites        [ CipherSuiteNumber        ],
                          SupportedSignatureAlgorithms [ SignatureAlgorithmNumber ],
                          SupportedNamedGroups         [ NamedGroupNumber         ],
                          TestResult,
                          ExecutionTime );

                OperatorConfidence ();

                MeasurementNumber++;
            }
        }
    }

    return ( MeasurementNumber );
}

//**********************************************************************************************************************************

void TLSTESTER::RunClientQUICTests ( char * DateAndTimeString )
{
    int  CipherSuiteNumber        = 0;
    int  SignatureAlgorithmNumber = 0;
    int  NamedGroupNumber         = 0;
    int  MeasurementNumber        = 0;
    long ExecutionTime            = 0;
    int  Result                   = 0;
    int  ErrorIndex               = 0;

    ClientComponent->SetTestRunNumber ( QUIC_CLIENT_MEASUREMENTS );

    ClientComponent->RecordTestRunStartTime ();

    Result = ClientComponent->InitialiseTLS ();

    if ( Result )
    {
        ClientComponent->ConfigureTraceCallback ();

        ErrorIndex = ClientComponent->InitialisePKI ();

        if ( ErrorIndex == 0 )
        {
            Result = ClientComponent->QuicCreate ();

            if ( Result )
            {
                //
                // run a measurement for each combination of cipher suite, algorithm and named group
                //

                for ( CipherSuiteNumber = 0; CipherSuiteNumber < NumberOfCipherSuites; CipherSuiteNumber++ )
                {
                    for ( SignatureAlgorithmNumber = 0; SignatureAlgorithmNumber < NumberOfSignatureAlgorithms; SignatureAlgorithmNumber++ )
                    {
                        for ( NamedGroupNumber = 0; NamedGroupNumber < NumberOfNamedGroups; NamedGroupNumber++ )
                        {
                            QueryPerformanceCounter ( &TestStartTime );

                            RunSingleClientQUICTest ( MeasurementNumber,
                                                      SupportedCipherSuites        [ CipherSuiteNumber        ],
                                                      SupportedSignatureAlgorithms [ SignatureAlgorithmNumber ],
                                                      SupportedNamedGroups         [ NamedGroupNumber         ] );

                            QueryPerformanceCounter ( &TestEndTime );

                            ExecutionTime = CalculateExecutionTime ( TestStartTime, TestEndTime );

                            fprintf ( ComponentStatisticsFile,
                                      "%s, %d, %s, %s, %s, %s, %u\n",
                                      DateAndTimeString,
                                      MeasurementNumber,
                                      SupportedCipherSuites        [ CipherSuiteNumber        ],
                                      SupportedSignatureAlgorithms [ SignatureAlgorithmNumber ],
                                      SupportedNamedGroups         [ NamedGroupNumber         ],
                                      "FAIL",
                                      ExecutionTime );

                            OperatorConfidence ();

                            MeasurementNumber++;
                        }
                    }
                }
            }
            else
            {
                printf ( "ClientComponent->QuicCreate() call failed!\n" );
            }

            ClientComponent->TerminatePKI ();
        }
        else
        {
            printf ( "ClientComponent->InitialisePKI() call failed with error %d!\n", ErrorIndex );
        }

        ClientComponent->Cleanup ();
    }
    else
    {
        printf ( "ClientComponent->InitialiseTLS() call failed!\n" );
    }

    ClientComponent->RecordTestRunEndTime ();

    // add this set of tests to the total run

    ClientComponent->NumberOfMeasurementsMade += MeasurementNumber;
}

//**********************************************************************************************************************************

void TLSTESTER::RunServerQUICTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************
//
// Client Interoperability TLS Tests
//
//**********************************************************************************************************************************

void TLSTESTER::RunOpenSSLClientTLSTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunBoringClientTLSTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunMbedTLSClientTLSTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunWolfSSLClientTLSTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunFizzClientTLSTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************
//
// Client Interoperability QUIC Tests
//
//**********************************************************************************************************************************

void TLSTESTER::RunOpenSSLClientQUICTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunBoringClientQUICTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunMbedTLSClientQUICTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunWolfSSLClientQUICTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunFizzClientQUICTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************
//
// Server Interoperability TLS Tests
//
//**********************************************************************************************************************************

void TLSTESTER::RunOpenSSLServerTLSTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunBoringServerTLSTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunMbedTLSServerTLSTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunWolfSSLServerTLSTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunFizzServerTLSTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************
//
// Server Interoperability QUIC Tests
//
//**********************************************************************************************************************************

void TLSTESTER::RunOpenSSLServerQUICTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunBoringServerQUICTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunMbedTLSServerQUICTests ( char * DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunWolfSSLServerQUICTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************

void TLSTESTER::RunFizzServerQUICTests ( char *DateAndTimeString )
{
}

//**********************************************************************************************************************************
//
// In a client test, only one socket is required, a socket for the connection to the peer (server) as the component uses send and
// receive callbacks to communicate with the environment. This makes the component platform and transport agnostic.
//
// <pre><code>
//                 ..
//    --------    .  .     ----------  Receive() -------------
//    |      |------------>|        |----------->|           |
//    | Peer |    .  .     | Tester |            | Component |
//    |      |<------------|        |<-----------|           |
//    --------    .  .     ----------   Send()   -------------
//                 ..
//                Peer
//               Socket
//
// </code></pre>
//
bool TLSTESTER::RunSingleClientTLSTest ( int         MeasurementNumber,
                                         const char *CipherSuite,
                                         const char *SignatureAlgorithm,
                                         const char *NamedGroup )
{
    bool Success = FALSE;

    fprintf ( DebugFile,
              "Running single client TLS test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
              MeasurementNumber,
              CipherSuite,
              SignatureAlgorithm,
              NamedGroup );

    if ( VerboseConsoleOutput )
    {
        printf ( "Running single client TLS test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
                 MeasurementNumber,
                 CipherSuite,
                 SignatureAlgorithm,
                 NamedGroup );
    }

    // open socket to communicate with peer (server)

    PeerSocket = OpenPeerSocket ();

    if ( PeerSocket != INVALID_SOCKET )
    {
        Success = SingleClientTLSTest ( MeasurementNumber, CipherSuite, SignatureAlgorithm, NamedGroup );

        closesocket ( PeerSocket );
    }

    return ( Success );
}

//**********************************************************************************************************************************

SOCKET TLSTESTER::OpenPeerSocket ( void )
{
    struct sockaddr_in   PeerAddress;
    struct hostent      *Peer        = NULL;
    int                  Response    = 0;
    SOCKET               PeerSocket  = INVALID_SOCKET;

    // open socket to communicate with peer (server)

    PeerSocket = socket ( AF_INET, SOCK_STREAM, 0 ); // we need a TCP socket as this is TLS!

    if ( PeerSocket != INVALID_SOCKET )
    {
        Peer = gethostbyname ( ClientComponent->GetHostName () );

        memset ( &PeerAddress, 0, sizeof ( PeerAddress ) );

        PeerAddress.sin_family = AF_INET;

        memcpy ( &PeerAddress.sin_addr.s_addr, Peer->h_addr, Peer->h_length );

        PeerAddress.sin_port = htons ( ClientComponent->GetPortNumber () );

        Response = connect ( PeerSocket, ( struct sockaddr* ) &PeerAddress, sizeof ( PeerAddress ) );

        if ( Response != 0 )
        {
            fprintf ( DebugFile, "Cannot connect to peer \"%s\" for test!\n", ClientComponent->GetHostName () );

            PrintSocketError ();

            closesocket ( PeerSocket ); // we can't use this socket so just close it

            PeerSocket = INVALID_SOCKET;
        }
    }
    else
    {
        fprintf ( DebugFile, "Cannot open TCP socket for peer!\n" );

        PrintSocketError ();
    }

    return ( PeerSocket );
}

//**********************************************************************************************************************************
//
// This test uses just the default configuration for the cipher suites, signature algorithms and named groups. The actual defaults
// could change from implementation to implementation as work progresses, so don't actually list them here.
//

bool TLSTESTER::RunSingleClientDefaultsTLSTest ( int MeasurementNumber )
{
    int    Response;
    int    Result;
    bool   Success    = FALSE;
    SOCKET PeerSocket = INVALID_SOCKET;

    fprintf ( DebugFile, "Running single client defaults TLS test %d\n", MeasurementNumber );

    if ( VerboseConsoleOutput )
    {
        printf ( "Running single client defaults TLS test %d\n", MeasurementNumber );
    }

    // open socket to communicate with peer (server)

    PeerSocket = OpenPeerSocket ();

    if ( PeerSocket != INVALID_SOCKET )
    {
        ClientComponent->SetMeasurementNumber ( MeasurementNumber );

        ClientComponent->RecordMeasurementStartTime (); // start time for this measurement

        ClientComponent->SetSocket ( PeerSocket );

        Result = ClientComponent->AddRootFileOrPath ( CertificateAuthorityChainFilename ); // must be done before the configure

        if ( Result )
        {
            Result = ClientComponent->Configure (); // set default TLS version

            if ( Result )
            {
                Result = ClientComponent->ConfigureCertificateCallbacks ();

                if ( Result )
                {
                    Result = ClientComponent->ConfigureNegotiationCallback ();

                    if ( Result )
                    {
                        Result = ClientComponent->Connect ();

                        //
                        // The component will call the send() and receive() callback functions to perform the handshake and the
                        // Connect () function call returns only when the handshake is complete.
                        //

                        if ( Result )
                        {
                            if ( VerboseConsoleOutput ) printf ( "ClientComponent->Connect() was successful!\n" );

                            // don't do any data transfer in this particular test

                            ClientComponent->Close ();

                            Success = TRUE;
                        }
                        else
                        {
                            printf ( "ClientComponent->Connect() failed!\n" );
                        }
                    }
                    else
                    {
                        printf ( "ClientComponent->ConfigureNegotiationCallback () failed!\n" );
                    }
                }
                else
                {
                    printf ( "ClientComponent->ConfigureCertificateCallbacks () failed!\n" );
                }
            }
            else
            {
                printf ( "ClientComponent->Configure() failed!\n" );
            }
        }
        else
        {
            printf ( "ClientComponent->AddRootFileOrPath () failed!\n" );
        }

        ClientComponent->RecordMeasurementEndTime ();

        if ( VerboseConsoleOutput ) printf ( "Last Error Code = %d\n", GetLastError () );
    }

    return ( Success );
}

//**********************************************************************************************************************************

bool TLSTESTER::RunSingleServerDefaultsTLSTest ( int MeasurementNumber )
{
    int  Response;
    int  Result;
    bool Success = FALSE;

    fprintf ( DebugFile, "Running single server defaults TLS test %d\n", MeasurementNumber );

    if ( VerboseConsoleOutput )
    {
        printf ( "Running single server defaults TLS test %d\n", MeasurementNumber );
    }

    ClientComponent->SetMeasurementNumber ( MeasurementNumber );
    ServerComponent->SetMeasurementNumber ( MeasurementNumber );

    ClientComponent->RecordMeasurementStartTime (); // start time for this measurement
    ServerComponent->RecordMeasurementStartTime (); // start time for this measurement

    Result = ClientComponent->AddRootFileOrPath ( CertificateAuthorityChainFilename ); // must be done before the configure

    if ( Result )
    {
        Result = ClientComponent->Configure (); // set default TLS version

        if ( Result )
        {
            Result = ClientComponent->ConfigureCertificateCallbacks ();

            if ( Result )
            {
                Result = ClientComponent->ConfigureNegotiationCallback ();

                if ( Result )
                {
                    Result = ClientComponent->Connect ();

                    //
                    // The component will call the send() and receive() callback functions to perform the handshake and the
                    // Connect () function call returns only when the handshake is complete.
                    //

                    if ( Result )
                    {
                        if ( VerboseConsoleOutput ) printf ( "ClientComponent->Connect() was successful!\n" );

                        // don't do any data transfer in this particular test

                        ClientComponent->Close ();

                        Success = TRUE;
                    }
                    else
                    {
                        printf ( "ClientComponent->Connect() failed!\n" );
                    }
                }
                else
                {
                    printf ( "ClientComponent->ConfigureNegotiationCallback () failed!\n" );
                }
            }
            else
            {
                printf ( "ClientComponent->ConfigureCertificateCallbacks () failed!\n" );
            }
        }
        else
        {
            printf ( "ClientComponent->Configure() failed!\n" );
        }
    }
    else
    {
        printf ( "ClientComponent->AddRootFileOrPath () failed!\n" );
    }

    ClientComponent->RecordMeasurementEndTime ();
    ServerComponent->RecordMeasurementEndTime ();

    if ( VerboseConsoleOutput ) printf ( "Last Error Code = %d\n", GetLastError () );

    return ( Success );
}

//**********************************************************************************************************************************
//
// In a server test, no sockets are required, buffers are used instead to remove network delay. The client and server components use
// their respective send and receive callbacks to communicate with the tester. These callbacks work with buffers. So the Client send
// callback writes into a buffer and the server receive callback reads from that buffer. Similarly the server send callback writes
// into another buffer and the client receive callback reads from that buffer.
//
// <pre><code>
//
//    ------------     Send()   ----------  Receive() -------------
//    |           |------------>|        |----------->|           |
//    |   Server  |    .  .     | Tester |            |   Client  |
//    | Component |             |        |            | Component |
//    |           |<------------|        |<-----------|           |
//    ------------   Receive()  ----------   Send()   -------------
//
// </code></pre>
//
bool TLSTESTER::RunSingleServerTLSTest ( int         MeasurementNumber,
                                         const char *CipherSuite,
                                         const char *SignatureAlgorithm,
                                         const char *NamedGroup )
{
    int  Result;
    bool Success = FALSE;

    fprintf ( DebugFile,
              "Running single server TLS test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
              MeasurementNumber,
              CipherSuite,
              SignatureAlgorithm,
              NamedGroup );

    if ( VerboseConsoleOutput )
    {
        printf ( "Running single server TLS test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
                 MeasurementNumber,
                 CipherSuite,
                 SignatureAlgorithm,
                 NamedGroup );
    }

    // sockets are not used in the server tests as buffers are used instead to eliminate network delay

    Success = SingleClientTLSTest ( MeasurementNumber, CipherSuite, SignatureAlgorithm, NamedGroup );

    return ( Success );
}

//**********************************************************************************************************************************

bool TLSTESTER::SingleClientTLSTest ( int         MeasurementNumber,
                                      const char *CipherSuite,
                                      const char *SignatureAlgorithm,
                                      const char *NamedGroup )
{
    int  Result;
    bool Success = FALSE;

    ClientComponent->SetMeasurementNumber ( MeasurementNumber );

    ClientComponent->RecordMeasurementStartTime (); // start time for this measurement

    Result = ClientComponent->AddRootFileOrPath ( CertificateAuthorityChainFilename ); // must be done before the configure

    if ( Result )
    {
        Result = ClientComponent->Configure ();

        if ( Result )
        {
            Result = ClientComponent->ConfigureCipherSuites ( CipherSuite );

            if ( Result )
            {
                Result = ClientComponent->ConfigureSignatureAlgorithms ( SignatureAlgorithm );

                if ( Result )
                {
                    Result = ClientComponent->ConfigureNamedGroups ( NamedGroup );

                    if ( Result )
                    {
                        Result = ClientComponent->ConfigureCertificateCallbacks ();

                        if ( Result )
                        {
                            Result = ClientComponent->ConfigureNegotiationCallback ();

                            if ( Result )
                            {
                                Result = ClientComponent->Connect ();

                                //
                                // The Client Component will call the send() and receive() callback functions to perform the
                                // handshake and the Connect () function call returns only when the handshake is complete.
                                //

                                if ( Result )
                                {
                                    if ( VerboseConsoleOutput ) fprintf (stderr, "ClientComponent->Connect() was successful!\n" );

                                    ClientComponent->Close ();

                                    Success = TRUE;
                                }
                                else
                                {
                                    fprintf ( DebugFile, "ClientComponent->Connect() failed!\n" );
                                }
                            }
                            else
                            {
                                fprintf ( DebugFile, "ClientComponent->ConfigureNegotiationCallback () failed!\n" );
                            }
                        }
                        else
                        {
                            fprintf ( DebugFile, "ClientComponent->ConfigureCertificateCallbacks() failed!\n" );
                        }
                    }
                    else
                    {
                        fprintf ( DebugFile, "ClientComponent->ConfigureNamedGroups ( %s ) failed!\n", NamedGroup );
                    }
                }
                else
                {
                    fprintf  (DebugFile, "ClientComponent->ConfigureSignatureAlgorithms ( %s ) failed!\n", SignatureAlgorithm );
                }
            }
            else
            {
                fprintf ( DebugFile, "ClientComponent->ConfigureCipherSuites ( %s ) failed!\n", CipherSuite );
            }
        }
        else
        {
            fprintf ( DebugFile, "ClientComponent->Configure() failed!\n" );
        }
    }
    else
    {
        fprintf ( DebugFile, "ClientComponent->AddRootFileOrPath () failed!\n" );
    }

    ClientComponent->RecordMeasurementEndTime ();

    if ( VerboseConsoleOutput ) fprintf ( stderr, "Last Error Code = %d\n", GetLastError () );

    return ( Success );
}

//**********************************************************************************************************************************

const char *HashNames [] =
{
  "MD5",    // TLS_hash_MD5    = 0,
  "SHA1",   // TLS_hash_SHA1   = 1,
  "SHA224", // TLS_hash_SHA224 = 2,
  "SHA256", // TLS_hash_SHA256 = 3,
  "SHA384", // TLS_hash_SHA384 = 4,
  "SHA512", // TLS_hash_SHA512 = 5
};

const char *AEADNames [] =
{
    "AES_128_GCM",       // TLS_aead_AES_128_GCM       = 0,
    "AES_256_GCM",       // TLS_aead_AES_256_GCM       = 1,
    "CHACHA20_POLY1305", // TLS_aead_CHACHA20_POLY1305 = 2
};

size_t InputBufferSize  = 0;
size_t OutputBufferSize = 0;

unsigned char InputBuffer  [ 8192 ];
unsigned char OutputBuffer [ 8192 ];

void TLSTESTER::RunSingleClientQUICTest ( int         MeasurementNumber,
                                          const char *CipherSuite,
                                          const char *SignatureAlgorithm,
                                          const char *NamedGroup )
{
    struct hostent     *Peer;
    struct sockaddr_in  PeerAddress;
    int                 Response;
    int                 Result;
    int                 AmountSent;
    int                 AmountReceived;
    quic_result         QuicResult;
    quic_secret         EarlySecret;
    quic_secret         MainSecret;
    unsigned char       SecretBuffer [ ( sizeof ( EarlySecret.secret ) * 2 ) + 2 ];


    fprintf ( DebugFile,
              "Running single client QUIC test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
              MeasurementNumber,
              CipherSuite,
              SignatureAlgorithm,
              NamedGroup );

    if ( VerboseConsoleOutput )
    {
        printf ( "Running single client QUIC test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
                 MeasurementNumber,
                 CipherSuite,
                 SignatureAlgorithm,
                 NamedGroup );
    }

    // open socket to communicate with peer (server)

    PeerSocket = socket ( AF_INET, SOCK_STREAM, 0 ); // needs to be TCP as this is not a full implementation of QUIC!

    if ( PeerSocket != 0 )
    {
        Peer = gethostbyname ( ClientComponent->GetHostName () );

        memset ( &PeerAddress, 0, sizeof ( PeerAddress ) );

        PeerAddress.sin_family = AF_INET;

        memcpy ( &PeerAddress.sin_addr.s_addr, Peer->h_addr, Peer->h_length );

        PeerAddress.sin_port = htons ( ClientComponent->GetPortNumber () );

        Response = connect ( PeerSocket, ( struct sockaddr* ) &PeerAddress, sizeof ( PeerAddress ) );

        if ( Response == 0 )
        {
            ClientComponent->SetMeasurementNumber ( MeasurementNumber );

            ClientComponent->RecordMeasurementStartTime ();

            ClientComponent->SetSocket ( PeerSocket ); // use the peer for now but switch to the server thread ASAP

            Result = ClientComponent->QuicCreate ();

            if ( Result )
            {
                //Result = ClientComponent->ConfigureCipherSuites ( CipherSuite );

                if ( Result )
                {
                    //Result = ClientComponent->ConfigureSignatureAlgorithms ( SignatureAlgorithm );

                    if ( Result )
                    {
                        //Result = ClientComponent->ConfigureNamedGroups ( NamedGroup );

                        if ( Result )
                        {
                            QuicResult = TLS_would_block;

                            while ( ( QuicResult != TLS_client_complete ) || ( QuicResult != TLS_client_complete_with_early_data ) )
                            {
                                // rather than using the send and receive callbacks, QUIC uses buffers

                                InputBufferSize = 0;

                                QuicResult = ClientComponent->QuicProcess ( InputBuffer,
                                                                      &InputBufferSize,
                                                                      OutputBuffer,
                                                                      &OutputBufferSize );

                                if ( ! PrintQuicResult ( QuicResult ) ); break; // stop if quic process returned an unknown result

                                // send any message to the peer

                                if ( OutputBufferSize != 0 )
                                {
                                    AmountSent = send ( PeerSocket, ( const char *) OutputBuffer, OutputBufferSize, 0 );

                                    if ( AmountSent != OutputBufferSize )
                                    {
                                        printf ( "network send() to peer failed!\n" ); PrintSocketError (); break;
                                    }
                                    else
                                    {
                                        DumpPacket ( OutputBuffer, OutputBufferSize, 0, 0, "sent to quic peer" );
                                    }
                                }

                                // receive any response from the peer

                                if ( InputBufferSize != 0 )
                                {
                                    AmountReceived = recv ( PeerSocket, (char *) InputBuffer, InputBufferSize, 0 );

                                    if ( AmountReceived != InputBufferSize )
                                    {
                                        printf ( "network recv() from peer failed!\n" ); PrintSocketError (); break;
                                    }
                                    else
                                    {
                                        DumpPacket ( InputBuffer, InputBufferSize, 0, 0, "received from quic peer" );
                                    }
                                }
                            }

                            // get any early secret and print it out

                            if ( ClientComponent->QuicGetExporter ( 0, &EarlySecret ) )
                            {
                                fprintf ( DebugFile,
                                          "EarlySecret: Hash = %d (%s), AEAD = %d (%s), Secret =",
                                          EarlySecret.hash,
                                          HashNames [ EarlySecret.hash ],
                                          EarlySecret.ae,
                                          AEADNames [ EarlySecret.ae ] );

                                for ( int Count = 0; Count < sizeof ( EarlySecret.secret ); Count++ )
                                {
                                    fprintf ( DebugFile, " %02x", EarlySecret.secret [ Count ] );
                                }

                                fprintf ( DebugFile, "\n" );
                            }

                            // get any main secret and print it out

                            if ( ClientComponent->QuicGetExporter ( 1, &MainSecret ) )
                            {
                                fprintf ( DebugFile,
                                          "MainSecret: Hash = %d (%s), AEAD = %d (%s), Secret =",
                                          MainSecret.hash,
                                          HashNames [ MainSecret.hash ],
                                          MainSecret.ae,
                                          AEADNames [ MainSecret.ae ] );

                                for ( int Count = 0; Count < sizeof ( MainSecret.secret ); Count++ )
                                {
                                    fprintf ( DebugFile, " %02x", MainSecret.secret [ Count ] );
                                }

                                fprintf ( DebugFile, "\n" );
                            }
                         }
                        else
                        {
                            printf ( "ClientComponent->ConfigureNamedGroups ( %s ) failed!\n", NamedGroup );
                        }
                    }
                    else
                    {
                        printf ( "ClientComponent->ConfigureSignatureAlgorithms ( %s ) failed!\n", SignatureAlgorithm );
                    }
                }
                else
                {
                    printf ( "ClientComponent->ConfigureCipherSuites ( %s ) failed!\n", CipherSuite );
                }
            }
            else
            {
                printf ( "ClientComponent->Configure() failed!\n" );
            }

            ClientComponent->RecordMeasurementEndTime ();

            if ( VerboseConsoleOutput ) printf ( "Return Code = %d\n", GetLastError () );
        }
        else
        {
            fprintf ( DebugFile, "Cannot connect to peer for test!\n" );

            PrintSocketError ();
        }

        closesocket ( PeerSocket );
    }
    else
    {
        fprintf ( DebugFile, "Cannot open socket for peer!\n" );

        PrintSocketError ();
    }
}

//**********************************************************************************************************************************

void TLSTESTER::RunSingleServerQUICTest ( int         MeasurementNumber,
                                          const char *CipherSuite,
                                          const char *SignatureAlgorithm,
                                          const char *NamedGroup )
{
    fprintf ( DebugFile,
              "Running single server QUIC test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
              MeasurementNumber,
              CipherSuite,
              SignatureAlgorithm,
              NamedGroup );

    printf ( "Running single server QUIC test %d on Cipher Suite %s, Signature Algorithm %s and Named group %s\n",
             MeasurementNumber,
             CipherSuite,
             SignatureAlgorithm,
             NamedGroup );
}

//**********************************************************************************************************************************

bool TLSTESTER::PrintQuicResult ( quic_result QuicResult ) // old knowledge now hidden!
{
    bool Result = TRUE;

    fprintf ( DebugFile, "QuicResult = %d, ", QuicResult );

    switch ( QuicResult )
    {
        case TLS_would_block :                     fprintf ( DebugFile, "Would block\n"                     ); break;
        case TLS_error_local :                     fprintf ( DebugFile, "Error Local\n"                     ); break;
        case TLS_error_alert :                     fprintf ( DebugFile, "Error Alert\n"                     ); break;
        case TLS_client_early :                    fprintf ( DebugFile, "Client Early\n"                    ); break;
        case TLS_client_complete :                 fprintf ( DebugFile, "Client Complete\n"                 ); break;
        case TLS_client_complete_with_early_data : fprintf ( DebugFile, "Client Complete with Early Data\n" ); break;
        case TLS_server_accept :                   fprintf ( DebugFile, "Server Accept\n"                   ); break;
        case TLS_server_accept_with_early_data :   fprintf ( DebugFile, "Server Accept with Early Data\n"   ); break;
        case TLS_server_complete :                 fprintf ( DebugFile, "Server Complete\n"                 ); break;
        case TLS_server_stateless_retry :          fprintf ( DebugFile, "Server Stateless Retry\n"          ); break;
        case TLS_error_other :                     fprintf ( DebugFile, "Error Other\n"                     ); break;

        default: fprintf ( DebugFile, "Unknown Quic Result\n" ); Result = FALSE; break;
    }

    return (  Result );
}

//**********************************************************************************************************************************
