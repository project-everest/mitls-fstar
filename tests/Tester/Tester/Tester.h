
//**********************************************************************************************************************************
//
//   Purpose: Interoperability Tester header file
//
//   Project: Everest
//
//  Filename: InteropTester.h
//
//   Authors: Caroline.M.Mathieson (CMM)
//
//**********************************************************************************************************************************
//
//  Description
//  -----------
//
//! \file InteropTester.h
//! \brief Contains the complete definition  of the TESTER Object.
//!
//**********************************************************************************************************************************

#include "stdafx.h"
#include "windows.h" // for LARGE_INTEGER

#include "mitlsffi.h" // for mitls_state etc
#include "mipki.h"    // for mipki_state etc
//#include "quic_provider.h"

//**********************************************************************************************************************************

/* ansi screen escape sequences */

#define ASES_HOME_CURSOR                       "\033[;f"
#define ASES_CLEAR_SCREEN                      "\033[2J"
#define ASES_CLEAR_TO_END_OF_LINE              "\033[K"
#define ASES_SET_CURSOR_POSITION (row, column) "\033[row;columnH"
#define ASES_MOVE_CURSOR_UP      (rows)        "\033[rowsA"
#define ASES_MOVE_CURSOR_DOWN    (rows)        "\033[rowsB"
#define ASES_MOVE_CURSOR_RIGHT   (columns)     "\033[columnsC"
#define ASES_MOVE_CURSOR_LEFT    (columns)     "\033[columnsD"
#define ASES_SAVE_CURSOR_POSITION              "\033[s"
#define ASES_RESTORE_CURSOR_POSITION           "\033[u"
#define ASES_GET_CURSOR_POSITION               "\033[6n"
#define ASES_SET_NO_SPECIAL_ATTRIBUTES         "\033[0m"
#define ASES_SET_HIGH_INTENSITY                "\033[1m"
#define ASES_SET_LOW_INTENSITY                 "\033[2m"
#define ASES_SET_ITALIC                        "\033[3m"
#define ASES_SET_UNDERLINE                     "\033[4m"
#define ASES_SET_BLINK                         "\033[5m"
#define ASES_SET_RAPID_BLINK                   "\033[6m"
#define ASES_SET_REVERSE_VIDEO                 "\033[7m"
#define ASES_SET_CONCEALED_TEXT                "\033[8m"
#define ASES_SET_FOREGROUND_BLACK              "\033[30m"
#define ASES_SET_FOREGROUND_RED                "\033[31m"
#define ASES_SET_FOREGROUND_GREEN              "\033[32m"
#define ASES_SET_FOREGROUND_YELLOW             "\033[33m"
#define ASES_SET_FOREGROUND_BLUE               "\033[34m"
#define ASES_SET_FOREGROUND_MAGENTA            "\033[35m"
#define ASES_SET_FOREGROUND_CYAN               "\033[36m"
#define ASES_SET_FOREGROUND_WHITE              "\033[37m"
#define ASES_SET_BACKGROUND_BLACK              "\033[40m"
#define ASES_SET_BACKGROUND_RED                "\033[41m"
#define ASES_SET_BACKGROUND_GREEN              "\033[42m"
#define ASES_SET_BACKGROUND_YELLOW             "\033[43m"
#define ASES_SET_BACKGROUND_BLUE               "\033[44m"
#define ASES_SET_BACKGROUND_MAGENTA            "\033[45m"
#define ASES_SET_BACKGROUND_CYAN               "\033[46m"
#define ASES_SET_BACKGROUND_WHITE              "\033[47m"
#define ASES_SET_DISPLAY_MODE_0                "\033[=0h"
#define ASES_SET_DISPLAY_MODE_1                "\033[=1h"
#define ASES_SET_DISPLAY_MODE_2                "\033[=2h"
#define ASES_SET_DISPLAY_MODE_3                "\033[=3h"
#define ASES_SET_DISPLAY_MODE_4                "\033[=4h"
#define ASES_SET_DISPLAY_MODE_5                "\033[=5h"
#define ASES_SET_DISPLAY_MODE_6                "\033[=6h"
#define ASES_SET_DISPLAY_MODE_14               "\033[=14h"
#define ASES_SET_DISPLAY_MODE_15               "\033[=15h"
#define ASES_SET_DISPLAY_MODE_16               "\033[=16h"
#define ASES_SET_DISPLAY_MODE_17               "\033[=17h"
#define ASES_SET_DISPLAY_MODE_18               "\033[=18h"
#define ASES_SET_DISPLAY_MODE_19               "\033[=19h"
#define ASES_ENABLE_LINE_WRAP                  "\033[=7h"
#define ASES_DISABLE_LINE_WRAP                 "\033[=7l"

//**********************************************************************************************************************************

typedef enum filemodes
{
    TEXT_MODE    = 0x01, // create plain text files
    CSV_MODE     = 0x02, // create CSV files
    XML_MODE     = 0x04, // create XML files
    HTML_MODE    = 0x08, // create HTML files
    GNUPLOT_MODE = 0x10, // create GNUPLOT files
    PNG_MODE     = 0x20, // create PNG files

    ALL_MODES = 0xFF  // create all file types

} FILE_MODES;

//**********************************************************************************************************************************

typedef enum measurementtypes
{
    TLS_CLIENT_MEASUREMENTS = 0,
    QUIC_CLIENT_MEASUREMENTS,

    TLS_SERVER_MEASUREMENTS,
    QUIC_SERVER_MEASUREMENTS,

    OPENSSL_SERVER_MEASUREMENTS,
    BORINGSSL_SERVER_MEASUREMENTS,
    MBEDTLS_SERVER_MEASUREMENTS,
    WOLFSSL_SERVER_MEASUREMENTS,
    FIZZ_SERVER_MEASUREMENTS,

    OPENSSL_CLIENT_MEASUREMENTS,
    BORINGSSL_CLIENT_MEASUREMENTS,
    MBEDTLS_CLIENT_MEASUREMENTS,
    WOLFSSL_CLIENT_MEASUREMENTS,
    FIZZ_CLIENT_MEASUREMENTS,

    MAX_MEASUREMENT_TYPES // the last one and gives the quantity

} MEASUREMENTTYPES;

//**********************************************************************************************************************************

typedef enum ffifunctions
{
    // TLS API functions

    FFI_MITLS_INIT = 0,
    FFI_MITLS_CONFIGURE,
    FFI_MITLS_SET_TICKET_KEY,
    FFI_MITLS_CONFIGURE_TICKET,
    FFI_MITLS_CONFIGURE_CIPHER_SUITES,
    FFI_MITLS_CONFIGURE_SIGNATURE_ALGORITHMS,
    FFI_MITLS_CONFIGURE_NAMED_GROUPS,
    FFI_MITLS_CONFIGURE_ALPN,
    FFI_MITLS_CONFIGURE_EARLY_DATA,
    FFI_MITLS_CONFIGURE_CUSTOM_EXTENSIONS,
    FFI_MITLS_CONFIGURE_TICKET_CALLBACK,
    FFI_MITLS_CONFIGURE_NEGO_CALLBACK,
    FFI_MITLS_CONFIGURE_CERT_CALLBACKS,
    FFI_MITLS_CLOSE,
    FFI_MITLS_CONNECT,
    FFI_MITLS_ACCEPT_CONNECTED,
    FFI_MITLS_GET_EXPORTER,
    FFI_MITLS_GET_CERT,
    FFI_MITLS_SEND,
    FFI_MITLS_RECEIVE,
    FFI_MITLS_FREE,
    FFI_MITLS_CLEANUP,
    FFI_MITLS_SET_TRACE_CALLBACK,

    // QUIC API functions

    FFI_MITLS_QUIC_CREATE,
    FFI_MITLS_QUIC_PROCESS,
    FFI_MITLS_QUIC_GET_EXPORTER,
    FFI_MITLS_QUIC_CLOSE,
    FFI_MITLS_GET_HELLO_SUMMARY,
    FFI_MITLS_FIND_CUSTOM_EXTENSION,
    FFI_MITLS_GLOBAL_FREE,

    MAX_FFI_FUNCTIONS // the last one and gives the quantity

} FFI_FUNCTIONS;

typedef enum fficallbacks
{
    // TLS API callback functions (these can be called more than once by the component)

    FFI_MITLS_SEND_CALLBACK = 0,
    FFI_MITLS_RECEIVE_CALLBACK,

    FFI_MITLS_CERTIFICATE_SELECT_CALLBACK,
    FFI_MITLS_CERTIFICATE_FORMAT_CALLBACK,
    FFI_MITLS_CERTIFICATE_SIGN_CALLBACK,
    FFI_MITLS_CERTIFICATE_VERIFY_CALLBACK,

    FFI_MITLS_TICKET_CALLBACK,
    FFI_MITLS_NEGOTIATION_CALLBACK,
    FFI_MITLS_TRACE_CALLBACK,

    MAX_FFI_CALLBACK_FUNCTIONS // the last one and gives the quantity

} FFI_CALLBACK_FUNCTIONS;

typedef enum pkifunctions
{
    MIPKI_INIT = 0,
    MIPKI_FREE,
    MIPKI_ADD_ROOT_FILE_OR_PATH,
    MIPKI_SELECT_CERTIFICATE,
    MIPKI_SIGN_VERFIY,
    MIPKI_PARSE_CHAIN,
    MIPKI_PARSE_LIST,
    MIPKI_FORMAT_CHAIN,
    MIPKI_FORMAT_ALLOC,
    MIPKI_VALIDATE_CHAIN,
    MIPKI_FREE_CHAIN,

    MAX_PKI_FUNCTIONS // the last one and gives the quantity

} PKI_FUNCTIONS;

typedef enum pkicallbackfunctions
{
    MIPKI_PASSWORD_CALLBACK = 0,
    MIPKI_ALLOC_CALLBACK,

    MAX_PKI_CALLBACK_FUNCTIONS // the last one and gives the quantity

} PKI_CALLBACK_FUNCTIONS;

//**********************************************************************************************************************************

typedef struct componentmeasuremententry
{
    const char    *EntryName;
    LARGE_INTEGER  StartTime; // when the function was called
    LARGE_INTEGER  EndTime;   // when the function returned

} COMPONENTMEASUREMENTENTRY;

#define MAX_CALLS_PER_MEASUREMENT (1000)

typedef struct callbackmeasuremententry
{
    const char   *EntryName;
    unsigned int  NumberOfCalls;

    LARGE_INTEGER StartTimes [ MAX_CALLS_PER_MEASUREMENT ]; // when the function was called
    LARGE_INTEGER EndTimes   [ MAX_CALLS_PER_MEASUREMENT ]; // when the function returned

} CALLBACKMEASUREMENTENTRY;

typedef struct componentmeasurement
{
    LARGE_INTEGER StartTime; // when the measurement started
    LARGE_INTEGER EndTime;   // when the measurement finished

    COMPONENTMEASUREMENTENTRY FFIMeasurements [ MAX_FFI_FUNCTIONS ]; // one for each FFI function

    COMPONENTMEASUREMENTENTRY PKIMeasurements [ MAX_PKI_FUNCTIONS ];       // one for each PKI function

    CALLBACKMEASUREMENTENTRY FFICallbackMeasurements [ MAX_FFI_CALLBACK_FUNCTIONS ]; // one for each call back function

    CALLBACKMEASUREMENTENTRY PKICallbackMeasurements [ MAX_PKI_CALLBACK_FUNCTIONS ]; // one for each call back function

} COMPONENTMEASUREMENT;

#define MAX_MEASUREMENTS (1000)

typedef struct measurementresults
{
    const char *MeasurementTypeName;

    LARGE_INTEGER StartTime; // when the testing run actually started
    LARGE_INTEGER EndTime;   // when the testing run actually finished

    COMPONENTMEASUREMENT Measurements [ MAX_MEASUREMENTS ]; // individual component measurements

} MEASUREMENTRESULTS;

//**********************************************************************************************************************************

typedef enum
{
    TLS_CT_CHANGE_CIPHER_SPEC = 20,
    TLS_CT_ALERT              = 21,
    TLS_CT_HANDSHAKE          = 22,
    TLS_CT_APPLICATION_DATA   = 23,
    TLS_CT_HEARTBEAT          = 24

} TLS_CONTENT_TYPE;

typedef enum
{
    TLS_MT_HELLO_REQUEST        = 0,
    TLS_MT_CLIENT_HELLO         = 1,
    TLS_MT_SERVER_HELLO         = 2,
    TLS_MT_NEW_SESSION_TICKET   = 4,
    TLS_MT_END_OF_EARLY_DATA    = 5,
    TLS_MT_HELLO_RETRY_REQUEST  = 6,
    TLS_MT_ENCRYPTED_EXTENSIONS = 8,
    TLS_MT_CERTIFICATE          = 11,
    TLS_MT_SERVER_KEY_EXCHANGE  = 12,
    TLS_MT_CERTIFICATE_REQUEST  = 13,
    TLS_MT_SERVER_HELLO_DONE    = 14,
    TLS_MT_CERTIFICATE_VERIFY   = 15,
    TLS_MT_CLIENT_KEY_EXCHANGE  = 16,
    TLS_MT_FINISHED             = 20,
    TLS_MT_KEY_UPDATE           = 24,
    TLS_MT_MESSAGE_HASH         = 254

} TLS_MESSAGE_TYPE;

typedef enum
{
    TLS_ET_SERVER_NAME                            = 0,
    TLS_ET_MAX_FRAGMENT_LENGTH                    = 1,
    TLS_ET_CLIENT_CERTIFICATE_URL                 = 2,
    TLS_ET_TRUSTED_CA_KEYS                        = 3,
    TLS_ET_TRUNCATED_HMAC                         = 4,
    TLS_ET_STATUS_REQUEST                         = 5,
    TLS_ET_USER_MAPPING                           = 6,
    TLS_ET_CLIENT_AUTHZ                           = 7,
    TLS_ET_SERVER_AUTHZ                           = 8,
    TLS_ET_CERT_TYPE                              = 9,
    TLS_ET_SUPPORTED_GROUPS                       = 10,
    TLS_ET_EC_POINT_FORMATS                       = 11,
    TLS_ET_SRP                                    = 12,
    TLS_ET_SIGNATURE_ALGORITHMS                   = 13,
    TLS_ET_USE_SRTP                               = 14,
    TLS_ET_HEARTBEAT                              = 15,
    TLS_ET_APPLICATION_LAYER_PROTOCOL_NEGOTIATION = 16,
    TLS_ET_STATUS_REQUEST_V2                      = 17,
    TLS_ET_SIGNED_CERTIFICATE_TIMESTAMP           = 18,
    TLS_ET_CLIENT_CERTIFICATE_TYPE                = 19,
    TLS_ET_SERVER_CERTIFICATE_TYPE                = 20,
    TLS_ET_PADDING                                = 21,
    TLS_ET_ENCRYPT_THEN_MAC                       = 22,
    TLS_ET_EXTENDED_MASTER_SECRET                 = 23,
    TLS_ET_TOKEN_BINDING                          = 24,
    TLS_ET_CACHED_INFO                            = 25,
    TLS_ET_QUIC_TRANSPORT_PARAMETERS              = 26, // new
    TLS_ET_COMPRESS_CERTIFICATE                   = 27,
    TLS_ET_RECORD_SIZE_LIMIT                      = 28,
    TLS_ET_SESSIONTICKET                          = 35,
    TLS_ET_PRE_SHARED_KEY                         = 41,
    TLS_ET_EARLY_DATA                             = 42,
    TLS_ET_SUPPORTED_VERSIONS                     = 43,
    TLS_ET_COOKIE                                 = 44,
    TLS_ET_PSK_KEY_EXCHANGE_MODES                 = 45,
    TLS_ET_CERTIFICATE_AUTHORITIES                = 47,
    TLS_ET_OID_FILTERS                            = 48,
    TLS_ET_POST_HANDSHAKE_AUTH                    = 49,
    TLS_ET_SIGNATURE_ALGORITHMS_CERT              = 50,
    TLS_ET_KEY_SHARE                              = 51,
    TLS_ET_RESERVED_GREASE_0                      = 0x0A0A,  // Generate Random Extensions And Sustain Extensibility (Google).
    TLS_ET_RESERVED_GREASE_1                      = 0x1A1A,
    TLS_ET_RESERVED_GREASE_2                      = 0x2A2A,
    TLS_ET_RESERVED_GREASE_3                      = 0x3A3A,
    TLS_ET_RESERVED_GREASE_4                      = 0x4A4A,
    TLS_ET_RESERVED_GREASE_5                      = 0x5A5A,
    TLS_ET_RESERVED_GREASE_6                      = 0x6A6A,
    TLS_ET_RESERVED_GREASE_7                      = 0x7A7A,
    TLS_ET_RESERVED_GREASE_8                      = 0x8A8A,
    TLS_ET_RESERVED_GREASE_9                      = 0x9A9A,
    TLS_ET_RESERVED_GREASE_A                      = 0xAAAA,
    TLS_ET_RESERVED_GREASE_B                      = 0xBABA,
    TLS_ET_RESERVED_GREASE_C                      = 0xCACA,
    TLS_ET_RESERVED_GREASE_D                      = 0xDADA,
    TLS_ET_RESERVED_GREASE_E                      = 0xEAEA,
    TLS_ET_RESERVED_GREASE_F                      = 0xFAFA,
    TLS_ET_RENEGOTIATION_INFO                     = 65281,
    TLS_ET_UNDEFINED_EXTENSION_TYPE               = 0xFFFF,

} TLS_EXTENSION_TYPE;

typedef struct extensiontypeentry
{
     TLS_EXTENSION_TYPE  Value;
     const char         *Name;
     const char         *Text;

} EXTENSION_TYPE_ENTRY;

//**********************************************************************************************************************************

typedef enum alertdescription
{
    TLS_AD_CLOSE_NOTIFY                    = (0),
    TLS_AD_UNEXPECTED_MESSAGE              = (10),
    TLS_AD_BAD_RECORD_MAC                  = (20),
    TLS_AD_DECRYPTION_FAILED_RESERVED      = (21),
    TLS_AD_RECORD_OVERFLOW                 = (22),
    TLS_AD_DECOMPRESSION_FAILURE           = (30),
    TLS_AD_HANDSHAKE_FAILURE               = (40),
    TLS_AD_NO_CERTIFICATE_RESERVED         = (41),
    TLS_AD_BAD_CERTIFICATE                 = (42),
    TLS_AD_UNSUPPORTED_CERTIFICATE         = (43),
    TLS_AD_CERTIFICATE_REVOKED             = (44),
    TLS_AD_CERTIFICATE_EXPIRED             = (45),
    TLS_AD_CERTIFICATE_UNKNOWN             = (46),
    TLS_AD_ILLEGAL_PARAMETER               = (47),
    TLS_AD_UNKNOWN_CA                      = (48),
    TLS_AD_ACCESS_DENIED                   = (49),
    TLS_AD_DECODE_ERROR                    = (50),
    TLS_AD_DECRYPT_ERROR                   = (51),
    TLS_AD_EXPORT_RESTRICTION_RESERVED     = (60),
    TLS_AD_PROTOCOL_VERSION                = (70),
    TLS_AD_INSUFFICIENT_SECURITY           = (71),
    TLS_AD_INTERNAL_ERROR                  = (80),
    TLS_AD_USER_CANCELED                   = (90),
    TLS_AD_NO_RENEGOTIATION                = (100),
    TLS_AD_UNSUPPORTED_EXTENSION           = (110),
    TLS_AD_CERTIFICATE_UNOBTAINABLE        = (111),
    TLS_AD_UNRECOGNIZED_NAME               = (112),
    TLS_AD_BAD_CERTIFICATE_STATUS_RESPONSE = (113),
    TLS_AD_BAD_CERTIFICATE_HASH_VALUE      = (114),
    TLS_AD_UNKNOWN                         = (255)

} TLS_ALERT_DESCRIPTION;

typedef struct alertdescriptionentry
{
     TLS_ALERT_DESCRIPTION  Value;
     const char            *Name;
     const char            *Text;

} ALERT_DESCRIPTION_ENTRY;

//**********************************************************************************************************************************

typedef enum ciphersuites
{
    TLS_RSA_WITH_RC4_128_SHA                = 0x0005,
    TLS_RSA_WITH_3DES_EDE_CBC_SHA           = 0x000A,
    TLS_RSA_WITH_AES_128_CBC_SHA            = 0x002F,
    TLS_DH_DSS_WITH_AES_128_CBC_SHA         = 0x0030,
    TLS_DH_RSA_WITH_AES_128_CBC_SHA         = 0x0031,
    TLS_DHE_DSS_WITH_AES_128_CBC_SHA        = 0x0032,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA        = 0x0033,
    TLS_DH_ANON_WITH_AES_128_CBC_SHA        = 0x0034,
    TLS_RSA_WITH_AES_256_CBC_SHA            = 0x0035,
    TLS_DH_DSS_WITH_AES_256_CBC_SHA         = 0x0036,
    TLS_DH_RSA_WITH_AES_256_CBC_SHA         = 0x0037,
    TLS_DHE_DSS_WITH_AES_256_CBC_SHA        = 0x0038,
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA        = 0x0039,
    TLS_DH_ANON_WITH_AES_256_CBC_SHA        = 0x003A,
    TLS_RSA_WITH_AES_128_CBC_SHA256         = 0x003C,
    TLS_RSA_WITH_AES_128_GCM_SHA256         = 0x009C,
    TLS_RSA_WITH_AES_256_GCM_SHA384         = 0x009D,
    TLS_DHE_DSS_WITH_AES_128_GCM_SHA256     = 0x00A2,
    TLS_DHE_RSA_WITH_AES_128_GCM_SHA256     = 0x009E,
    TLS_DHE_RSA_WITH_AES_256_GCM_SHA384     = 0x009F,
    TLS_EMPTY_RENEGOTIATION_INFO_SCSV       = 0x00FF,
    TLS_AES_128_GCM_SHA256                  = 0x1301,
    TLS_AES_256_GCM_SHA384                  = 0x1302,
    TLS_CHACHA20_POLY1305_SHA256            = 0x1303,
    TLS_AES_128_CCM_SHA256                  = 0x1304,
    TLS_AES_128_CCM_8_SHA256                = 0x1305,
    TLS_RESERVED_GREASE                     = 0x6A6A,
    TLS_ECDHE_ECDSA_WITH_RC4_128_SHA        = 0xC007,
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA    = 0xC009,
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA    = 0xC00A,
    TLS_ECDHE_RSA_WITH_RC4_128_SHA          = 0xC011,
    TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA     = 0xC012,
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA      = 0xC013,
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA      = 0xC014,
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 = 0xC023,
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256   = 0xC027,
    TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256   = 0xC02F,
    TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = 0xC02B,
    TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384   = 0xC030,
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = 0xC02C,
    TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305    = 0xCCA8,
    TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305  = 0xCCA9,
    TLS_DHE_RSA_WITH_CHACHA20_POLY1305      = 0xCCAA,

    TLS_CIPHER_SUITE_UNDEFINED              = 0xFFFF

} TLS_CIPHER_SUITES;

typedef struct ciphersuitedescriptionentry
{
     TLS_CIPHER_SUITES  Value;
     const char        *Name;
     bool               Supported; // in component

} CIPHER_SUITE_DESCRIPTION_ENTRY;

//**********************************************************************************************************************************

typedef enum signaturealgorithms // grouped by type but numerical values over-ride normal assignment
{
    // theoretically supported by mitls

    TLS_SA_RSA_PKCS1_SHA256       = 0x0401,
    TLS_SA_RSA_PKCS1_SHA384       = 0x0501,
    TLS_SA_RSA_PKCS1_SHA512       = 0x0601,

    // ECDSA Algorithms
    TLS_SA_ECDSA_SECP256R1_SHA256 = 0x0403,
    TLS_SA_ECDSA_SECP384R1_SHA384 = 0x0503,
    TLS_SA_ECDSA_SECP521R1_SHA512 = 0x0603,

    // RSASSA-PSS Algorithms
    TLS_SA_RSA_PSS_SHA256         = 0x0804,
    TLS_SA_RSA_PSS_SHA384         = 0x0805,
    TLS_SA_RSA_PSS_SHA512         = 0x0806,

    // ECDSA Algorithms
    TLS_SA_ED25519                = 0x0807,
    TLS_SA_ED448                  = 0x0808,

    // Legacy Algorithms (not supported by mitls)
    TLS_SA_RSA_PKCS1_SHA1         = 0x0201,
    TLS_SA_ECDSA_SHA1             = 0x0203,

    TLS_SA_DSA_SHA256             = 0x0402,
    TLS_SA_DSA_SHA384             = 0x0502,
    TLS_SA_DSA_SHA512             = 0x0602,
    TLS_SA_DSA_SHA224             = 0x0302,
    TLS_SA_DSA_SHA1               = 0x0202,

    TLS_SA_UNDEFINED              = 0xFFFF

} TLS_SIGNATURE_ALGORITHMS;

typedef struct signaturealgorithmdescriptionentry
{
    TLS_SIGNATURE_ALGORITHMS  Value;
    const char               *Name;
    bool                      Supported; // in component

} SIGNATURE_ALGORITHM_DESCRIPTION_ENTRY;

//**********************************************************************************************************************************

typedef enum namedgroups
{
    TLS_NG_SECP256R1 = 0x0017, // "secp256r1"
    TLS_NG_SECP384R1 = 0x0018, // "secp384r1"
    TLS_NG_SECP521R1 = 0x0019, // "secp521r1"
    TLS_NG_X25519    = 0x001D, // "x25519"
    TLS_NG_X448      = 0x001E, // "x448"
    TLS_NG_FFDHE2048 = 0x0100, // "ffdhe2048"
    TLS_NG_FFDHE3072 = 0x0101, // "ffdhe3072"
    TLS_NG_FFDHE4096 = 0x0102, // "ffdhe4096"
    TLS_NG_FFDHE6144 = 0x0103, // "ffdhe6144"
    TLS_NG_FFDHE8192 = 0x0104, // "ffdhe8192"

    TLS_NG_UNDEFINED = 0xFFFF

} TLS_NAMED_GROUPS;

typedef struct namedgroupdescriptionentry
{
     TLS_NAMED_GROUPS Value;
     const char       *LoggingName;
     const char       *ExpectedName;
     bool              Supported; // in component

} NAMED_GROUP_DESCRIPTION_ENTRY;

//**********************************************************************************************************************************
// TLS Records
//**********************************************************************************************************************************

typedef struct tlsalertrecord
{
//  type          Field                    offset
//-----------------------------------------------------------------
    unsigned char AlertLevel;            // 5
    unsigned char AlertDescription;      // 6

} TLS_ALERT_RECORD;

#define TLS_RECORD_HEADER_SIZE (5)

typedef struct protocolversion
{
    unsigned char MajorVersion;
    unsigned char MinorVersion;

} TLS_PROTOCOL_VERSION;

typedef struct tlsmessageheader
{
//  type          Field                    offset
//-----------------------------------------------------------------
    unsigned char MessageType;         // 5
    unsigned char MessageLengthHigh;   // 6
    unsigned char MessageLengthMiddle; // 7
    unsigned char MessageLengthLow;    // 8

} TLS_MESSAGE_HEADER;

#define RANDOM_BYTES_LENGTH (28)

typedef struct tlsgenericrecord
{
    TLS_MESSAGE_HEADER MessageHeader; // 5 to 8

} TLS_GENERIC_RECORD;

#define MAX_SESSION_IDENTIFIER_LENGTH ( 255 ) // it's a single octet field

typedef struct tlsclienthellorecord
{
    TLS_MESSAGE_HEADER MessageHeader;  // 5 to 8

    // message content

    TLS_PROTOCOL_VERSION HelloVersion; // 9 & 10

    struct
    {
        unsigned char UnixTime    [                   4 ]; // 11 to 14
        unsigned char RandomBytes [ RANDOM_BYTES_LENGTH ]; // 15 to 43

    } Random;

    unsigned char SessionIdentifierLength;

    unsigned char SessionIdentifier [ 1 ]; // first variable length field (maybe be 0 length)

} TLS_CLIENT_HELLO_RECORD;

typedef struct tlsserverhellorecord
{
    TLS_MESSAGE_HEADER MessageHeader;  // 5 to 8

    // message content

    TLS_PROTOCOL_VERSION HelloVersion; // 9 & 10

    struct
    {
        unsigned char UnixTime    [                   4 ]; // 11 to 14
        unsigned char RandomBytes [ RANDOM_BYTES_LENGTH ]; // 15 to 43

    } Random;

    unsigned char SessionIdentifierLength;

    unsigned char SessionIdentifier [ 1 ]; // first variable length field (maybe be 0 length)

} TLS_SERVER_HELLO_RECORD;

typedef struct tlscertificate
{
    unsigned char CertificateLengthHigh;
    unsigned char CertificateLengthMiddle;
    unsigned char CertificateLengthLow;

    unsigned char Certificate [ 1 ]; // size is CertificateLength

} TLS_CERTIFICATE;

typedef struct tlscertificaterecord
{
    TLS_MESSAGE_HEADER MessageHeader;  // 5 to 8

    // message content

    unsigned char CertificatesFieldLengthHigh;   // 6
    unsigned char CertificatesFieldLengthMiddle; // 7
    unsigned char CertificatesFieldLengthLow;    // 8

    // there can be one or more certificates

    TLS_CERTIFICATE Certificates [ 1 ]; // total size is CertificatesFieldLength

} TLS_CERTIFICATE_RECORD;

typedef struct tlsrecordheader
{
//  type                 Field                 offset
//-----------------------------------------------------------------
    unsigned char        ContentType;       // 0
    TLS_PROTOCOL_VERSION ProtocolVersion;   // 1 & 2 aka LegacyVersion for TLS 1.3+
    unsigned char        ContentLengthHigh; // 3
    unsigned char        ContentLengthLow;  // 4

} TLS_RECORD_HEADER;

typedef struct tlsrecord
{
    TLS_RECORD_HEADER RecordHeader; // 0 to 4

    union // note that there can be multiple records, each of a different type
    {
        TLS_GENERIC_RECORD        TLSGenericRecord;
        TLS_CLIENT_HELLO_RECORD   TLSClientHelloRecord;
        TLS_SERVER_HELLO_RECORD   TLSServerHelloRecord;
        TLS_CERTIFICATE_RECORD    TLSCertificateRecord;
        TLS_ALERT_RECORD          TLSAlertRecord;

    } HandshakeRecords; // "fragment" + in RFC 5246

} TLS_RECORD;

//**********************************************************************************************************************************

typedef enum asnclass
{
    ASN_CLASS_UNIVERSAL        = 0, // 0 0
    ASN_CLASS_APPLICATION      = 1, // 0 1
    ASN_CLASS_CONTEXT_SPECIFIC = 2, // 1 0
    ASN_CLASS_PRIVATE          = 3  // 1 1

} ASNCLASS;

typedef enum asntagnumber
{
    ASN_TAG_UNUSED_0        = 0,
    ASN_TAG_BOOLEAN         = 1,
    ASN_TAG_INTEGER         = 2,
    ASN_TAG_BIT_STRING      = 3,
    ASN_TAG_OCTET_STRING    = 4,
    ASN_TAG_NULL            = 5,
    ASN_TAG_OBJECT_ID       = 6,
    ASN_TAG_REAL            = 9,
    ASN_TAG_SEQUENCE        = 16,
    ASN_TAG_SET             = 17,
    ASN_TAG_PRINATBE_STRING = 19,
    ASN_TAG_T61STRING       = 20,
    ASN_TAG_IA5STRING       = 22,
    ASN_TAG_UTC_TIME        = 23,
    ASN_TAG_EXTENDED        = 31

} ASNTAGNUMBER;

typedef struct asnentry
{
    bool         InUse;

    // TAG
    ASNCLASS     Class;
    bool         IsPrimitive = FALSE;
    ASNTAGNUMBER TagNumber;

    // LENGTH
    unsigned long Length; // in octets

    // VALUE
    unsigned char Value [ 1 ]; // actually Length octets

} ASNENTRY;

#define MAX_ASN_ENTRIES (100000)

//**********************************************************************************************************************************

class TESTER
{
    protected:

        FILE *DebugFile;
        FILE *ComponentStatisticsFile;
        FILE *RecordedMeasurementsFile;

        // measurement variables

        LARGE_INTEGER StartTime;
        LARGE_INTEGER EndTime;
        LARGE_INTEGER Frequency;

    public:

        // console output over-ride flags

        bool ConsoleDebugging;     // if TRUE, produce console debug output (in addition to component's logging)

        bool VerboseConsoleOutput; // if TRUE, print out all information messages on the console, errors are always output

        FILE *RedirectedStandardOutputFile; // contains the output from the dll and any other stdout

        char RedirectedStandardOutputFilename [ MAX_PATH ]; // the filename of the redirected output file

    public:

        TESTER ( FILE *NewDebugFile, FILE * NewComponentStatisticsFile, FILE *NewRecordedMeasurementsFile );

        ~TESTER ( void );

        FILE *GetDebugFile ( void );

        bool Setup ( char *DateAndTimeString );

        bool TearDown ( void );

        long CalculateExecutionTime ( LARGE_INTEGER StartingTime, LARGE_INTEGER EndingTime );

    private:

};

//**********************************************************************************************************************************

class TLSTESTER : public TESTER
{
    protected:

        LARGE_INTEGER TestStartTime;
        LARGE_INTEGER TestEndTime;

        SOCKET PeerSocket;
        SOCKET ComponentSocket;

    public:

        class COMPONENT *Component; // callback functions need access to this to do measurements

        char HostFileName [ MAX_PATH ]; // the name of the file containing the list of hosts, if any

        char TLSVersion [ 4 ];

        char HostName [ MAX_PATH ]; // the default hostname

        int PortNumber; // the default port number

        char ClientCertificateFilename    [ MAX_PATH ];
        char ClientCertificateKeyFilename [ MAX_PATH ];

        char ServerCertificateFilename    [ MAX_PATH ];
        char ServerCertificateKeyFilename [ MAX_PATH ];

        char CertificateAuthorityChainFilename [ MAX_PATH ];

        // command line over-ride flags

        bool UseHostList;                   // if TRUE, user has specified a list of hostnames in a file

        bool UseHostName;                   // if TRUE, then the host name is specified on the command line

        bool UsePortNumber;                 // if TRUE, then the port n umber is specified on the command line

        bool DoTLSTests;                    // if TRUE, do the TLS tests part of a measurement or test run

        bool DoQUICTests;                   // if TRUE, do the QUIC tests part of a measurement or test run

        bool DoClientTests;                 // if TRUE, do the client only TLS and DTLS tests

        bool DoServerTests;                 // if TRUE, do the client/server TLS and DTLS tests

        bool DoClientInteroperabilityTests; // if TRUE, do the client mode interoperability TLS and DTLS tests

        bool DoServerInteroperabilityTests; // if TRUE, do the server mode interoperability TLS and DTLS tests

    public:

        TLSTESTER ( FILE *DebugFile, FILE *TestResultsFile, FILE *RecordedMeasurementsFile );

        ~TLSTESTER ( void );

        void Configure ( void ); // configure the component settings from the tester settings

        void RunClientTLSTests ( char *DateAndTimeString ); // mitls running in TLS client mode

        void RunServerTLSTests ( char *DateAndTimeString ); // mitls running in TLS server mode

        void RunClientQUICTests ( char *DateAndTimeString ); // mitls running in QUIC client mode

        void RunServerQUICTests ( char *DateAndTimeString ); // mitls running in QUIC server mode

        // client interoperability TLS tests

        void RunOpenSSLClientTLSTests ( char *DateAndTimeString ); // mitls as TLS client with OpenSSL Server

        void RunBoringClientTLSTests ( char *DateAndTimeString );  // mitls as TLS client with BoringSSL Server

        void RunMbedTLSClientTLSTests ( char *DateAndTimeString ); // mitls as TLS client with MbedTLS Server

        void RunWolfSSLClientTLSTests ( char *DateAndTimeString ); // mitls as TLS client with WolfSSL Server

        void RunFizzClientTLSTests ( char *DateAndTimeString );    // mitls as TLS client with Fizz Server

        // client interoperability QUIC tests

        void RunOpenSSLClientQUICTests ( char *DateAndTimeString ); // mitls as QUIC client with OpenSSL Server

        void RunBoringClientQUICTests ( char *DateAndTimeString );  // mitls as QUIC client with BoringSSL Server

        void RunMbedTLSClientQUICTests ( char *DateAndTimeString ); // mitls as QUIC client with MbedTLS Server

        void RunWolfSSLClientQUICTests ( char *DateAndTimeString ); // mitls as QUIC client with WolfSSL Server

        void RunFizzClientQUICTests ( char *DateAndTimeString );    // mitls as QUIC client with Fizz Server

        // server interoperability TLS tests

        void RunOpenSSLServerTLSTests ( char *DateAndTimeString ); // mitls as TLS server with OpenSSL Client

        void RunBoringServerTLSTests ( char *DateAndTimeString );  // mitls as TLS server with BoringSSL Client

        void RunMbedTLSServerTLSTests ( char *DateAndTimeString ); // mitls as TLS server with MbedTLS Client

        void RunWolfSSLServerTLSTests ( char *DateAndTimeString ); // mitls as TLS server with WolfSSL Client

        void RunFizzServerTLSTests ( char *DateAndTimeString );    // mitls as TLS server with Fizz Client

        // server interoperability QUIC tests

        void RunOpenSSLServerQUICTests ( char *DateAndTimeString ); // mitls as QUIC server with OpenSSL Client

        void RunBoringServerQUICTests ( char *DateAndTimeString );  // mitls as QUIC server with BoringSSL Client

        void RunMbedTLSServerQUICTests ( char *DateAndTimeString ); // mitls as QUIC server with MbedTLS Client

        void RunWolfSSLServerQUICTests ( char *DateAndTimeString ); // mitls as QUIC server with WolfSSL Client

        void RunFizzServerQUICTests ( char *DateAndTimeString );    // mitls as QUIC server with Fizz Client

private:

        void RunSingleClientTLSTest ( int         MeasurementNumber,
                                      const char *CipherSuite,
                                      const char *SignatureAlgorithm,
                                      const char *NamedGroup );

        void RunSingleServerTLSTest ( int         MeasurementNumber,
                                      const char *CipherSuite,
                                      const char *SignatureAlgorithm,
                                      const char *NamedGroup );

        void RunSingleClientQUICTest ( int         MeasurementNumber,
                                       const char *CipherSuite,
                                       const char *SignatureAlgorithm,
                                       const char *NamedGroup );

        void RunSingleServerQUICTest ( int         MeasurementNumber,
                                       const char *CipherSuite,
                                       const char *SignatureAlgorithm,
                                       const char *NamedGroup );

        bool PrintQuicResult ( quic_result QuicResult );
};

//**********************************************************************************************************************************

#define MAX_CERTIFICATE_CHAINS (100)

class COMPONENT
{
    protected:

        TLSTESTER *Tester = NULL;

        mitls_state *TLSState = NULL; // should be set by the first mitls_init function to the internal state address

        quic_state  *QUICState = NULL; // should be set by the quic_create function to the internal state address

        mipki_state *PKIState = NULL; // should be set by the mipki_init function to the internal state address

        quic_config Configuration =
        {
            Configuration.is_server = 0, // should be boolean FALSE but defined as an int

            Configuration.alpn                 = NULL,
            Configuration.cipher_suites        = NULL,
            Configuration.signature_algorithms = NULL,
            Configuration.named_groups         = NULL,
            Configuration.enable_0rtt          = 1, // should be boolean TRUE but defined as an int

            // client only
            Configuration.host_name     = NULL,
            Configuration.server_ticket = NULL,
            Configuration.exts          = NULL,
            Configuration.exts_count    = 0,

            Configuration.callback_state  = NULL,
            Configuration.ticket_callback = NULL,
            Configuration.nego_callback   = NULL,
            Configuration.cert_callbacks  = NULL,

            // server only
            Configuration.ticket_enc_alg = NULL,
            Configuration.ticket_key     = NULL,
            Configuration.ticket_key_len = 0,
        };

        char ClientCertificateFilename    [ MAX_PATH ];
        char ClientCertificateKeyFilename [ MAX_PATH ];

        char ServerCertificateFilename    [ MAX_PATH ];
        char ServerCertificateKeyFilename [ MAX_PATH ];

        // kremlin generated code will abort if this is set to > "1.3". If set to "1.3" then the hello messages use "1.2" and use
        // the extensions to specify the right version. If set to "1.2" then the hello messages use "1.2". If set to "1.1" then the
        // hello messages use "1.1".

        char TLSVersion [ 4 ]; // "1.X" plus termiating zero

        char HostName [ MAX_PATH ];

        int PortNumber;

        int TestRunNumber;

        int MeasurementNumber;

        int NumberOfMeasurementsMade;

    public: // so callbacks can access them quickly

        SOCKET Socket = 0;

        FILE *DebugFile = NULL;

        COMPONENTMEASUREMENT *CurrentComponentMeasurement = NULL; // for test run number and measurement number

        int NumberOfChainsAllocated = 0; // index into CertificateChains

        mipki_chain CertificateChains [ MAX_CERTIFICATE_CHAINS ];

    public:

        COMPONENT ( TLSTESTER *Parent,  FILE *NewDebugFile );

        ~COMPONENT ( void );

        void RecordStartTime ( void );

        void RecordEndTime ( void );

        // setters

        void SetClientCertificateFilename ( char *NewClientCertificateFilename );

        void SetClientCertificateKeyFilename ( char *NewClientCertificateKeyFilename );

        void SetServerCertificateFilename ( char *NewServerCertificateFilename );

        void SetServerCertificateKeyFilename ( char *NewServerCertificateKeyFilename );

        void SetVersion  ( char *NewVersion );

        void SetHostName ( char *NewHostName );

        void SetPortNumber ( int NewPortNumber );

        void SetTestRunNumber ( int NewTestRunNumber );

        void SetMeasurementNumber ( int NewMeasurementNumber );

        void SetNumberOfMeasurementsMade ( int NewNUmberOfMeasurementsMade );

        void SetSocket ( SOCKET Socket );

        // getters

        char *GetClientCertificateFilename ( void );

        char *GetClientCertificateKeyFilename ( void );

        char *GetServerCertificateFilename ( void );

        char *GetServerCertificateKeyFilename ( void );

        char *GetVersion ( void );

        char *GetHostName ( void );

        int GetPortNumber ( void );

        int GetTestRunNumber ( void );

        int GetMeasurementNumber ( void );

        int GetNumberOfMeasurementsMade ( void );

        SOCKET GetSocket ( void );

    public:

        // TLS API Functions

        int InitialiseTLS ( void );

        void Cleanup ( void );

        int Configure ( void );

        int SetTicketKey ( const char          *Algorithm,
                           const unsigned char *TicketKey,
                           size_t               TicketKeyLength );

        int ConfigureCipherSuites ( const char *CipherSuites ) ;

        int ConfigureSignatureAlgorithms ( const char *SignatureAlgorithms );

        int ConfigureNamedGroups ( const char *NamedGroups );

        int ConfigureApplicationLayerProtocolNegotiation ( const char *ApplicationLayerProtocolNegotiation );

        int ConfigureEarlyData ( uint32_t MaximumEarlyData );

        void ConfigureTraceCallback ( void );

        int ConfigureTicketCallback ( void              *CallbackState,
                                      pfn_FFI_ticket_cb  TicketCallback );

        int ConfigureNegotiationCallback ( void ); // uses the callback functions in component.cpp

        int ConfigureCertificateCallbacks ( void ); // uses the callback functions in component.cpp

        void CloseConnection ( void );

        int Connect ( void ); // client side

        int AcceptConnected ( void ); // server side

        int GetExporter ( int           early,
                          mitls_secret *secret );

        void *GetCertificate ( size_t *cert_size );

        int Send ( const unsigned char *buffer,
                   size_t               buffer_size );

        void *Receive ( size_t *packet_size );

        // QUIC API Functions

        int QuicCreate ( void );

        quic_result QuicProcess ( const unsigned char *inBuf,
                                  size_t              *pInBufLen,
                                  unsigned char       *outBuf,
                                  size_t              *pOutBufLen );

        int QuicGetExporter ( int          early,
                              quic_secret *secret );

        void QuicClose ( void );

        int GetHelloSummary ( const unsigned char  *buffer,
                              size_t                buffer_len,
                              mitls_hello_summary  *summary,
                              unsigned char       **cookie,
                              size_t               *cookie_len );

        int FindCustomExtension ( int                   is_server,
                                  const unsigned char  *exts,
                                  size_t                exts_len,
                                  uint16_t              ext_type,
                                  unsigned char       **ext_data,
                                  size_t               *ext_data_len );

        void GlobalFree ( void *pv );

        // PKI API Functions

        int InitialisePKI ( void );

        void TerminatePKI ( void );

        int AddRootFileOrPath ( const char *CertificateAuthorityFile );

        mipki_chain SelectCertificate ( void );

        int SignCertificate ( mipki_chain CertificatePointer );

        int VerifyCertificate ( mipki_state           *State,               // use the state provided by the callback!
                                mipki_chain            CertificatePointer,
                                const mipki_signature  SignatureAlgorithm,
                                const char            *Certificate,
                                size_t                 CertificateLength,
                                char                  *Signature,
                                size_t                *SignatureLength );

        int ParseChain ( mipki_state *State,         // use the state provided by the callback!
                         const char  *ChainOfTrust,
                         size_t       ChainLength ); // returns index into CertificateChains []

        mipki_chain ParseList ( void );

        int FormatChain ( mipki_chain Chain );

        void FormatAllocation ( mipki_chain Chain );

        int ValidateChain ( mipki_chain Chain );

        void FreeChain ( mipki_chain Chain );

    private:
};

void InitialiseMeasurementResults ( void );

void AllocateMeasurementResult ( int TestRunNumber );

void FreeMeasurementResults ( void );

void InitialiseMeasurementResult ( MEASUREMENTRESULTS *MeasurementResult );

void PrintMeasurementResults ( FILE *MeasurementsResultFile );

void PrintMeasurementResult ( FILE               *MeasurementsResultFile,
                              MEASUREMENTRESULTS *MeasurementResult );

void RecordTestRunStartTime ( int TestRunNumber );

void RecordTestRunEndTime ( int TestRunNumber );

//**********************************************************************************************************************************

#pragma once
