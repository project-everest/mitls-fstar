import logging
import sys
import time
import struct

from ctypes import  CDLL, \
                    c_long, \
                    c_int, \
                    c_float, \
                    c_double, \
                    c_char_p, \
                    create_string_buffer, \
                    byref, \
                    c_voidp, \
                    c_uint8, \
                    c_uint32, \
                    CFUNCTYPE, \
                    POINTER   

LOG_TRANSMITTED_BYTES       = False

class TLSParserError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

class COLORS():
    BLACK       = 0
    RED         = 1
    GREEN       = 2
    YELLOW      = 3
    BLUE        = 4
    MAGENTA     = 5
    CYAN        = 6
    WHITE       = 7
    DEFAULT     = 8

    #Attributes: 
    NORMAL      = 0
    BRIGHT      = 1

class Terminal():
    @staticmethod
    def GetColorSequence( foreground, background = COLORS.DEFAULT, attribute = COLORS.NORMAL ):
        return "\x1b[%d;%d;%dm" % ( COLORS.BRIGHT, foreground + 30, background + 40 );

    @staticmethod
    def ColorText( color, text, originalColor = COLORS.WHITE ):
        return Terminal.GetColorSequence( color ) + text + Terminal.GetColorSequence( originalColor )
    # @staticmethod
    # def SetColor( foreground, background = COLORS.DEFAULT, attribute = COLORS.NORMAL ):
    #     sys.stdout.write( Terminal.GetColorSequence( foreground, background, attribute ) )

def Green( text, originalColor = COLORS.WHITE ):
    return Terminal.ColorText( COLORS.GREEN, text, originalColor )

def Yellow( text, originalColor = COLORS.WHITE ):
    return Terminal.ColorText( COLORS.YELLOW, text, originalColor )

def Magenta( text, originalColor = COLORS.WHITE ):
    return Terminal.ColorText( COLORS.MAGENTA, text, originalColor )

def Blue( text, originalColor = COLORS.WHITE ):
    return Terminal.ColorText( COLORS.BLUE, text, originalColor )



SIZE_OF_TYPE            = 1
SIZE_OF_PROTOCOL        = 2
SIZE_OF_UINT8           = 1
SIZE_OF_UINT16          = 2
SIZE_OF_UINT24          = 3
TLS_RECORD_HEADER_SIZE  = SIZE_OF_TYPE + SIZE_OF_PROTOCOL + SIZE_OF_UINT16

TLS_RECORD_TYPE_HANDSHAKE  = 22
TLS_RECORD_TYPE_APP_DATA   = 23

HANDSHAKE_TYPE_CLIENT_HELLO         = 1
HANDSHAKE_TYPE_SERVER_HELLO         = 2
HANDSHAKE_TYPE_NEW_SESSION_TICKET   = 4
HANDSHAKE_TYPE_END_OF_EARLY_DATA    = 5
HANDSHAKE_TYPE_HELLO_RETRY_REQUEST  = 6
HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS = 8
HANDSHAKE_TYPE_CERTIFICATE          = 11
HANDSHAKE_TYPE_CERTIFICATE_REQUEST  = 13
HANDSHAKE_TYPE_CERTIFICATE_VERIFY   = 15
HANDSHAKE_TYPE_FINISHED             = 20
HANDSHAKE_TYPE_KEY_UPDATE           = 24
HANDSHAKE_TYPE_MESSAGE_HASH         = 254

HANDSHAKE_TYPE_NAME = {
    HANDSHAKE_TYPE_CLIENT_HELLO         : "client_hello",
    HANDSHAKE_TYPE_SERVER_HELLO         : "server_hello",
    HANDSHAKE_TYPE_NEW_SESSION_TICKET   : "new_session_ticket",
    HANDSHAKE_TYPE_END_OF_EARLY_DATA    : "end_of_early_data",
    HANDSHAKE_TYPE_HELLO_RETRY_REQUEST  : "hello_retry_request",
    HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS : "encrypted_extensions",
    HANDSHAKE_TYPE_CERTIFICATE          : "certificate",
    HANDSHAKE_TYPE_CERTIFICATE_REQUEST  : "certificate_request",
    HANDSHAKE_TYPE_CERTIFICATE_VERIFY   : "certificate_verify",
    HANDSHAKE_TYPE_FINISHED             : "finished",
    HANDSHAKE_TYPE_KEY_UPDATE           : "key_update",
    HANDSHAKE_TYPE_MESSAGE_HASH         : "message_hash",
}

TLS_RECORD_TYPE_NAME = {    TLS_RECORD_TYPE_HANDSHAKE : "handshake", 
                            TLS_RECORD_TYPE_APP_DATA  : "application_data" } 

TLS_RSA_WITH_RC4_128_SHA                = 0x0005
TLS_RSA_WITH_3DES_EDE_CBC_SHA           = 0x000a
TLS_RSA_WITH_AES_128_CBC_SHA            = 0x002f
TLS_RSA_WITH_AES_256_CBC_SHA            = 0x0035
TLS_RSA_WITH_AES_128_CBC_SHA256         = 0x003c
TLS_RSA_WITH_AES_128_GCM_SHA256         = 0x009c
TLS_RSA_WITH_AES_256_GCM_SHA384         = 0x009d
TLS_ECDHE_ECDSA_WITH_RC4_128_SHA        = 0xc007
TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA    = 0xc009
TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA    = 0xc00a
TLS_ECDHE_RSA_WITH_RC4_128_SHA          = 0xc011
TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA     = 0xc012
TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA      = 0xc013
TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA      = 0xc014
TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 = 0xc023
TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256   = 0xc027
TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256   = 0xc02f
TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = 0xc02b
TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384   = 0xc030
TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = 0xc02c
TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305    = 0xcca8
TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305  = 0xcca9
TLS_AES_128_GCM_SHA256                  = 0x1301
TLS_AES_256_GCM_SHA384                  = 0x1302
TLS_CHACHA20_POLY1305_SHA256            = 0x1303

TLS_RSA_WITH_AES_128_CBC_SHA            = 0x002F
TLS_DH_DSS_WITH_AES_128_CBC_SHA         = 0x0030
TLS_DH_RSA_WITH_AES_128_CBC_SHA         = 0x0031
TLS_DHE_DSS_WITH_AES_128_CBC_SHA        = 0x0032
TLS_DHE_RSA_WITH_AES_128_CBC_SHA        = 0x0033
TLS_DH_anon_WITH_AES_128_CBC_SHA        = 0x0034
TLS_RSA_WITH_AES_256_CBC_SHA            = 0x0035
TLS_DH_DSS_WITH_AES_256_CBC_SHA         = 0x0036
TLS_DH_RSA_WITH_AES_256_CBC_SHA         = 0x0037
TLS_DHE_DSS_WITH_AES_256_CBC_SHA        = 0x0038
TLS_DHE_RSA_WITH_AES_256_CBC_SHA        = 0x0039
TLS_DH_anon_WITH_AES_256_CBC_SHA        = 0x003A

TLS_DHE_DSS_WITH_AES_128_GCM_SHA256     = 0x00A2
TLS_DHE_RSA_WITH_AES_128_GCM_SHA256     = 0x009E

CIPHER_SUITES_NAMES = {
    TLS_RSA_WITH_RC4_128_SHA                : "TLS_RSA_WITH_RC4_128_SHA",
    TLS_RSA_WITH_3DES_EDE_CBC_SHA           : "TLS_RSA_WITH_3DES_EDE_CBC_SHA",
    TLS_RSA_WITH_AES_128_CBC_SHA            : "TLS_RSA_WITH_AES_128_CBC_SHA",
    TLS_RSA_WITH_AES_256_CBC_SHA            : "TLS_RSA_WITH_AES_256_CBC_SHA",
    TLS_RSA_WITH_AES_128_CBC_SHA256         : "TLS_RSA_WITH_AES_128_CBC_SHA256",
    TLS_RSA_WITH_AES_128_GCM_SHA256         : "TLS_RSA_WITH_AES_128_GCM_SHA256",
    TLS_RSA_WITH_AES_256_GCM_SHA384         : "TLS_RSA_WITH_AES_256_GCM_SHA384",
    TLS_ECDHE_ECDSA_WITH_RC4_128_SHA        : "TLS_ECDHE_ECDSA_WITH_RC4_128_SHA",
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA    : "TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA",
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA    : "TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA",
    TLS_ECDHE_RSA_WITH_RC4_128_SHA          : "TLS_ECDHE_RSA_WITH_RC4_128_SHA",
    TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA     : "TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA",
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA      : "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA",
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA      : "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA",
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 : "TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256",
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256   : "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256",
    TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256   : "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256",
    TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 : "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256",
    TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384   : "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384",
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 : "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384",
    TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305    : "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305",
    TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305  : "TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305",
    TLS_AES_128_GCM_SHA256                  : "TLS_AES_128_GCM_SHA256",
    TLS_AES_256_GCM_SHA384                  : "TLS_AES_256_GCM_SHA384",
    TLS_CHACHA20_POLY1305_SHA256            : "TLS_CHACHA20_POLY1305_SHA256",
    TLS_RSA_WITH_AES_128_CBC_SHA            : "TLS_RSA_WITH_AES_128_CBC_SHA",
    TLS_DH_DSS_WITH_AES_128_CBC_SHA         : "TLS_DH_DSS_WITH_AES_128_CBC_SHA",
    TLS_DH_RSA_WITH_AES_128_CBC_SHA         : "TLS_DH_RSA_WITH_AES_128_CBC_SHA",
    TLS_DHE_DSS_WITH_AES_128_CBC_SHA        : "TLS_DHE_DSS_WITH_AES_128_CBC_SHA",
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA        : "TLS_DHE_RSA_WITH_AES_128_CBC_SHA",
    TLS_DH_anon_WITH_AES_128_CBC_SHA        : "TLS_DH_anon_WITH_AES_128_CBC_SHA",
    TLS_RSA_WITH_AES_256_CBC_SHA            : "TLS_RSA_WITH_AES_256_CBC_SHA",
    TLS_DH_DSS_WITH_AES_256_CBC_SHA         : "TLS_DH_DSS_WITH_AES_256_CBC_SHA",
    TLS_DH_RSA_WITH_AES_256_CBC_SHA         : "TLS_DH_RSA_WITH_AES_256_CBC_SHA",
    TLS_DHE_DSS_WITH_AES_256_CBC_SHA        : "TLS_DHE_DSS_WITH_AES_256_CBC_SHA",
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA        : "TLS_DHE_RSA_WITH_AES_256_CBC_SHA",
    TLS_DH_anon_WITH_AES_256_CBC_SHA        : "TLS_DH_anon_WITH_AES_256_CBC_SHA", 
    TLS_DHE_DSS_WITH_AES_128_GCM_SHA256     : "TLS_DHE_DSS_WITH_AES_128_GCM_SHA256",
    TLS_DHE_RSA_WITH_AES_128_GCM_SHA256     : "TLS_DHE_RSA_WITH_AES_128_GCM_SHA256",
}

# https://www.iana.org/assignments/tls-extensiontype-values/tls-extensiontype-values.xhtml
EXTENSION_TYPE_MAX_FRAGMENT_LENGTH                      = 1
EXTENSION_TYPE_CLIENT_CERTIFICATE_URL                   = 2
EXTENSION_TYPE_TRUSTED_CA_KEYS                          = 3
EXTENSION_TYPE_TRUNCATED_HMAC                           = 4
EXTENSION_TYPE_STATUS_REQUEST                           = 5
EXTENSION_TYPE_USER_MAPPING                             = 6
EXTENSION_TYPE_CLIENT_AUTHZ                             = 7
EXTENSION_TYPE_SERVER_AUTHZ                             = 8
EXTENSION_TYPE_CERT_TYPE                                = 9
EXTENSION_TYPE_SUPPORTED_GROUPS                         = 10
EXTENSION_TYPE_EC_POINT_FORMATS                         = 11
EXTENSION_TYPE_SRP                                      = 12
EXTENSION_TYPE_SIGNATURE_ALGORITHMS                     = 13
EXTENSION_TYPE_USE_SRTP                                 = 14
EXTENSION_TYPE_HEARTBEAT                                = 15
EXTENSION_TYPE_APPLICATION_LAYER_PROTOCOL_NEGOTIATION   = 16
EXTENSION_TYPE_STATUS_REQUEST_V2                        = 17
EXTENSION_TYPE_SIGNED_CERTIFICATE_TIMESTAMP             = 18
EXTENSION_TYPE_CLIENT_CERTIFICATE_TYPE                  = 19
EXTENSION_TYPE_SERVER_CERTIFICATE_TYPE                  = 20
EXTENSION_TYPE_PADDING                                  = 21
EXTENSION_TYPE_ENCRYPT_THEN_MAC                         = 22
EXTENSION_TYPE_EXTENDED_MASTER_SECRET                   = 23
EXTENSION_TYPE_TOKEN_BINDING                            = 24
EXTENSION_TYPE_CACHED_INFO                              = 25
EXTENSION_TYPE_SESSIONTICKET                            = 35
EXTENSION_TYPE_KEY_SHARE                                = 40
EXTENSION_TYPE_PRE_SHARED_KEY                           = 41
EXTENSION_TYPE_EARLY_DATA                               = 42
EXTENSION_TYPE_SUPPORTED_VERSIONS                       = 43
EXTENSION_TYPE_COOKIE                                   = 44
EXTENSION_TYPE_PSK_KEY_EXCHANGE_MODES                   = 45
EXTENSION_TYPE_CERTIFICATE_AUTHORITIES                  = 47
EXTENSION_TYPE_OID_FILTERS                              = 48
EXTENSION_TYPE_POST_HANDSHAKE_AUTH                      = 49
EXTENSION_TYPE_RENEGOTIATION_INFO                       = 65281

EXTENSION_TYPE_NAMES = {
    1  : "MAX_FRAGMENT_LENGTH",
    2  : "CLIENT_CERTIFICATE_URL",
    3  : "TRUSTED_CA_KEYS",
    4  : "TRUNCATED_HMAC",
    5  : "STATUS_REQUEST",
    6  : "USER_MAPPING",
    7  : "CLIENT_AUTHZ",
    8  : "SERVER_AUTHZ",
    9  : "CERT_TYPE",
    10 : "SUPPORTED_GROUPS",
    11 : "EC_POINT_FORMATS",
    12 : "SRP",
    13 : "SIGNATURE_ALGORITHMS",
    14 : "USE_SRTP",
    15 : "HEARTBEAT",
    16 : "APPLICATION_LAYER_PROTOCOL_NEGOTIATION",
    17 : "STATUS_REQUEST_V2",
    18 : "SIGNED_CERTIFICATE_TIMESTAMP",
    19 : "CLIENT_CERTIFICATE_TYPE",
    20 : "SERVER_CERTIFICATE_TYPE",
    21 : "PADDING",
    22 : "ENCRYPT_THEN_MAC",
    23 : "EXTENDED_MASTER_SECRET",
    24 : "TOKEN_BINDING",
    25 : "CACHED_INFO",
    35 : "SESSIONTICKET",
    40 : "KEY_SHARE",
    41 : "PRE_SHARED_KEY",
    42 : "EARLY_DATA",
    43 : "SUPPORTED_VERSIONS",
    44 : "COOKIE",
    45 : "PSK_KEY_EXCHANGE_MODES",
    47 : "CERTIFICATE_AUTHORITIES",
    48 : "OID_FILTERS",
    49 : "POST_HANDSHAKE_AUTH",
    65281 : "RENEGOTIATION_INFO",
}

class TLSParser():
    TLS_1_3_MAGIC   = b"\x03\x01"

    def __init__( self, name ):
        self.recentBytes = b""
        self.name = name

    def ExpectedMsgSize():
        pass

    def GetTLSRecordMsgType( self, typeNumber ):
        if typeNumber in TLS_RECORD_TYPE_NAME.keys():
            return TLS_RECORD_TYPE_NAME[ typeNumber ]

        return "unknown_type"

    def GetHandshakeType( self, typeNumber ):
        if typeNumber in HANDSHAKE_TYPE_NAME.keys():
            return HANDSHAKE_TYPE_NAME[ typeNumber ]

        return "unknown_type"

    def GetExtensionName( self, typeNumber ):
        if typeNumber in EXTENSION_TYPE_NAMES.keys():
            return EXTENSION_TYPE_NAMES[ typeNumber ]

        return "unknown_extension"
    
    def GetCipherSuiteName( self, suiteID ):
        if suiteID in CIPHER_SUITES_NAMES.keys():
            return CIPHER_SUITES_NAMES[ suiteID ]

        return "unknown_type"
    
    def ParseMsgHeader( self ):
        curretPosition = 0

        msg = {}
        msg[ 'type'    ]    =  struct.unpack( "B", self.recentBytes[ curretPosition: curretPosition + SIZE_OF_TYPE ] )[0]
        curretPosition     += SIZE_OF_TYPE

        msg[ 'protocol' ]   =  self.recentBytes[ curretPosition : curretPosition + SIZE_OF_PROTOCOL ] 
        curretPosition     += SIZE_OF_PROTOCOL 

        msg[ 'length'    ]  =  struct.unpack( ">H", self.recentBytes[ curretPosition: curretPosition + SIZE_OF_UINT16 ] )[0]
        curretPosition     += SIZE_OF_UINT16
        
        if msg[ 'protocol' ] != self.TLS_1_3_MAGIC:
            raise TLSParserError( "Protocol magic is %s instead of expected %s" % ( msg[ 'protocol' ], TLS_1_3_MAGIC ) )

        return msg

    def ParseExtensionContent( self, extensionType, extensionContent ):
        curretPosition = 0
        if extensionType == EXTENSION_TYPE_SUPPORTED_VERSIONS:
            numVersions     = int( extensionContent[ curretPosition ] / SIZE_OF_UINT16 )
            curretPosition += SIZE_OF_UINT8
            for versionIdx in range( numVersions ):
                versionID       = extensionContent[ curretPosition  : curretPosition + SIZE_OF_UINT16 ]
                curretPosition += SIZE_OF_UINT16

                sys.stdout.write( Magenta(" 0x%02x%02x," % ( versionID[ 0 ] , versionID[ 1 ]  ) )  )

    def ParseClientHello_Extensions( self, msg, rawExtensions ):
        curretPosition = 0

        print( "" )
        extensions = []
        while curretPosition < len( rawExtensions ):
            extensionType       = struct.unpack( ">H", rawExtensions[ curretPosition: curretPosition + SIZE_OF_UINT16 ] )[0]
            curretPosition     += SIZE_OF_UINT16

            extensionSize       = struct.unpack( ">H", rawExtensions[ curretPosition: curretPosition + SIZE_OF_UINT16 ] )[0]
            curretPosition     += SIZE_OF_UINT16

            if curretPosition + extensionSize > len( rawExtensions ):
                raise TLSParserError( "Extension size too big: %d" % extensionSize )

            extensionContent = rawExtensions[ curretPosition : curretPosition + extensionSize ]
            curretPosition  += extensionSize
            extensions.append( ( extensionType, extensionContent ) )

            sys.stdout.write(   Green( "Found extension " ) + 
                                Yellow( "%-30s" % self.GetExtensionName( extensionType ) + "(%d)" % extensionType ) +
                                Green( " Extension size: " ) + Blue( "%d" % extensionSize ) )

            self.ParseExtensionContent( extensionType, extensionContent )
            print( "" )

        msg[ 'extensions' ] = extensions

    def ParseServerHello( self, msg ):
        SIZE_OF_RANDOM = 32
        curretPosition = SIZE_OF_TYPE + SIZE_OF_UINT24

        msg[ 'handshake_protocol' ]  = msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT16 ]
        curretPosition              += SIZE_OF_UINT16

        msg[ 'random' ]              = msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_RANDOM ]
        curretPosition              += SIZE_OF_RANDOM

        cipherSuite                 = struct.unpack( ">H", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT16 ] )[0]
        curretPosition              += SIZE_OF_UINT16

        ################# Extensions:
        sizeOfExtensions           = struct.unpack( ">H", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT16 ] )[0]
        curretPosition            += SIZE_OF_UINT16

        if curretPosition + sizeOfExtensions != len( msg[ 'body' ] ):
            raise TLSParserError( "Extensions size is %d instead of %d" %  
                                    (sizeOfExtensions, len( msg[ 'body' ] ) - curretPosition)  )

        extensions = msg[ 'body' ][ curretPosition : curretPosition + sizeOfExtensions ]
        self.ParseClientHello_Extensions( msg, extensions )
        
        ################ Print parsed ServerHello:
        sys.stdout.write( "\n--> " )  
        sys.stdout.write( Green( " handshake_protocol: ") + Magenta( str( msg[ 'handshake_protocol' ] ) ) + " " )
        sys.stdout.write( Green( "random: \n") + Magenta( self.FormatBuffer( msg[ 'random' ] ) ) + " " )
        sys.stdout.write( Green( "cipherSuite: ") + Blue( "0x%x: " % cipherSuite ) + Yellow( self.GetCipherSuiteName( cipherSuite ) ) + "\n" ) 


    def ParseClientHello( self, msg ):
        SIZE_OF_RANDOM = 32
        curretPosition = SIZE_OF_TYPE + SIZE_OF_UINT24

        msg[ 'handshake_protocol' ]  = msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT16 ]
        curretPosition              += SIZE_OF_UINT16

        msg[ 'random' ]              = msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_RANDOM ]
        curretPosition              += SIZE_OF_RANDOM

        legacySessionIDSize          =  struct.unpack( "B", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT8 ] )[0]
        curretPosition              += SIZE_OF_UINT8
        
        msg[ 'legacy_session_id' ]   = msg[ 'body' ][ curretPosition : curretPosition + legacySessionIDSize ]
        curretPosition              += legacySessionIDSize
        
        ############### Cipher suites: 
        sizeOfCipherSuites           = struct.unpack( ">H", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT16 ] )[0]
        curretPosition              += SIZE_OF_UINT16

        numCipherSuites = int( sizeOfCipherSuites / SIZE_OF_UINT16 )
        cipherSuites    = []
        for suiteIdx in range( numCipherSuites ):
            suite           = struct.unpack( ">H", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT16 ] )[0]
            curretPosition += SIZE_OF_UINT16
            cipherSuites.append( suite )

        msg[ 'cipher_suites' ] = cipherSuites
        
        ################ Legacy compression method. Should contain 1 byte with value 0
        legacyCompressionMethodSize      = struct.unpack( "B", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT8 ] )[0]
        curretPosition                  += SIZE_OF_UINT8
        if legacyCompressionMethodSize != 1:
            raise TLSParserError( "legacy_compression_method SIZE is %d instead of 1" % legacyCompressionMethodSize )

        legacy_compression_method        = struct.unpack( "B", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT8 ] )[0]
        curretPosition                  += SIZE_OF_UINT8
        if legacy_compression_method != 0:
            raise TLSParserError( "legacy_compression_method VALUE is %d instead of 0" % legacy_compression_method )

        ################# Extensions:
        sizeOfExtensions           = struct.unpack( ">H", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_UINT16 ] )[0]
        curretPosition            += SIZE_OF_UINT16

        if curretPosition + sizeOfExtensions != len( msg[ 'body' ] ):
            raise TLSParserError( "Extension size is %d instead of %d" %  
                                    (sizeOfExtensions, len( msg[ 'body' ] ) - curretPosition)  )

        extensions = msg[ 'body' ][ curretPosition : curretPosition + sizeOfExtensions ]
        self.ParseClientHello_Extensions( msg, extensions )

        ################ Print parsed ClientHello:
        sys.stdout.write( "\n--> " )  
        sys.stdout.write( Green( " handshake_protocol: ") + Magenta( str( msg[ 'handshake_protocol' ] ) ) + " " )
        sys.stdout.write( Green( "random: \n") + Magenta( self.FormatBuffer( msg[ 'random' ] ) ) + " " )
        sys.stdout.write( Green( "legacySessionIDSize: ") + Blue( "%d" % legacySessionIDSize ) + " " )
        sys.stdout.write( Green( "legacy_session_id: ") + Magenta( str( msg[ 'legacy_session_id' ] ) ) + " " )
        sys.stdout.write( Green( "sizeOfCipherSuites: ") + Blue( "%d" % sizeOfCipherSuites ) + " " )
        
        sys.stdout.write( Green( "cipher_suits: [\n")  ) 
        for suite in msg[ 'cipher_suites' ]:
            sys.stdout.write( Blue( "0x%x: " % suite ) + Yellow( self.GetCipherSuiteName( suite ) ) + "\n" )
        sys.stdout.write( Green( "] ")  ) 


    def ParseHandshakeMsg( self, msg ):
        curretPosition = 0

        msg[ 'handshake_type' ] = struct.unpack( "B", msg[ 'body' ][ curretPosition : curretPosition + SIZE_OF_TYPE ] )[0]
        curretPosition     += SIZE_OF_TYPE

        msg[ 'handshake_length' ] = struct.unpack( ">I", b"\x00" + msg[ 'body' ][ curretPosition: curretPosition + SIZE_OF_UINT24 ] )[0]
        curretPosition     += SIZE_OF_UINT24

        sys.stdout.write( Green( "Handshake type: ") + Yellow( "%-15s (0x%x)" ) % ( self.GetHandshakeType( msg[ 'handshake_type' ] ), msg[ 'handshake_type' ]  ) )
        sys.stdout.write( Green( " Handshake size: ") + Blue( "%5d" % msg[ 'handshake_length' ] ) )

        if msg[ 'handshake_type' ] == HANDSHAKE_TYPE_CLIENT_HELLO:
            self.ParseClientHello( msg )

        if msg[ 'handshake_type' ] == HANDSHAKE_TYPE_SERVER_HELLO:
            self.ParseServerHello( msg )

        return msg

    def ParseMsgBody( self, msg ):
        totalMsgSize        = TLS_RECORD_HEADER_SIZE + msg[ 'length' ]
        msg[ 'body' ]       = self.recentBytes[ TLS_RECORD_HEADER_SIZE : totalMsgSize] 
        self.recentBytes    = self.recentBytes[ totalMsgSize : ]

        sys.stdout.write(   Green( self.name + ": ")   + 
                            Green( "Msg type: " ) + Yellow( "%-18s (0x%x)" ) % ( self.GetTLSRecordMsgType( msg[ 'type' ] ), msg[ 'type' ] ) + 
                            Green( " length: ")   + Blue( "%5d" % msg[ 'length' ] ) + 
                            Green( " protocol: ") + Magenta( str( msg[ 'protocol' ] ) ) + "; ")

        if msg[ 'type' ] == TLS_RECORD_TYPE_HANDSHAKE:
            self.ParseHandshakeMsg( msg )
            
        print( "" )
        return msg

    def Digest( self, bytes, printPacket = True ):
        if printPacket:
            sys.stdout.write( Green( self.FormatBuffer( bytes ) )  + "\n" )

        self.recentBytes += bytes
        if len( self.recentBytes ) < TLS_RECORD_HEADER_SIZE:
            return

        msg = self.ParseMsgHeader()
        if len( self.recentBytes ) >= TLS_RECORD_HEADER_SIZE + msg[ 'length' ]:
            self.ParseMsgBody( msg )

        # pprint.pprint( msg )

    @staticmethod
    def FormatBuffer( buffer ):
        humanReadableBuffer = ""
        for i, byte in enumerate( buffer ):
          humanReadableBuffer += "0x%2X, " % byte 
          if ( i + 1 ) % 8 == 0:
              humanReadableBuffer += "\n"

        return humanReadableBuffer

class MemorySocket():
    SLEEP_INTERVAL_SECONDS = 0.05

    def __init__( self, readTimeout = 5, logMsgs = LOG_TRANSMITTED_BYTES ):
        self.clientToServerPipe = bytearray()
        self.serverToClientPipe = bytearray()
        self.readTimeout        = readTimeout
        self.logMsgs            = logMsgs
        self.clientParser       = TLSParser( "Client parser" )
        self.serverParser       = TLSParser( "Server parser" )

        self.SetupLogger()

    def SetupLogger( self ):
        self.log = logging.getLogger( 'MemorySocket' )
        self.log.setLevel(logging.DEBUG)

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel(logging.DEBUG)
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    #Used by client to send to server:
    def SendToServer( self, ctx, buffer, bufferSize ):
        self.log.debug( "SendToServer bufferSize = %d" % bufferSize ) 
        pyBuffer = bytearray( ( c_uint8 * bufferSize ).from_address( buffer ) )
        
        self.clientParser.Digest( pyBuffer[ : ] )
        if self.logMsgs:
            self.log.debug( "SendToServer -->\n" + TLSParser.FormatBuffer( pyBuffer ) ) 

        self.clientToServerPipe += pyBuffer
        return bufferSize

    #Used by server to read from client:
    def ReadFromClient( self, ctx, buffer, bufferSize ):
        self.log.debug( "ReadFromClient, bufferSize = %d" % bufferSize )

        # Wait for data to be available:
        startTime = time.time()
        while len( self.clientToServerPipe ) == 0:
            time.sleep( self.SLEEP_INTERVAL_SECONDS )
            if( time.time() - startTime > self.readTimeout ):
                self.log.error( "ReadFromClient: timeout expired" )
                return 0

        bytesToReturn = len( self.clientToServerPipe )
        if bufferSize < bytesToReturn:
            bytesToReturn = bufferSize

        pyBuffer = ( c_uint8 * bufferSize ).from_address( buffer )
        pyBuffer[ 0 : bytesToReturn ] = self.clientToServerPipe[ 0 : bytesToReturn ]

        # "flush" bytes read:
        self.clientToServerPipe = self.clientToServerPipe[ bytesToReturn : ]

        self.log.debug( "ReadFromClient: returned %d bytes" % bytesToReturn )
        return bytesToReturn

    #Used by server to send to client:
    def SendToClient( self, ctx, buffer, bufferSize ):
        self.log.debug( "SendToClient bufferSize = %d" % bufferSize ) 
        pyBuffer = bytearray( ( c_uint8 * bufferSize ).from_address( buffer ) )
        
        self.serverParser.Digest( pyBuffer[ : ] )
        if self.logMsgs:
            self.log.debug( "SendToClient -->\n" + TLSParser.FormatBuffer( pyBuffer ) ) 

        self.serverToClientPipe += pyBuffer
        return bufferSize

    #Used by client to read from server:
    def ReadFromServer( self, ctx, buffer, bufferSize  ):
        self.log.debug( "ReadFromServer, bufferSize = %d" % bufferSize )

        # Wait for data to be available:
        startTime = time.time()
        while len( self.serverToClientPipe ) == 0:
            time.sleep( self.SLEEP_INTERVAL_SECONDS )
            if( time.time() - startTime > self.readTimeout ):
                self.log.error( "ReadFromServer: timeout expired" )
                return 0

        bytesToReturn = len( self.serverToClientPipe )
        if bufferSize < bytesToReturn:
            bytesToReturn = bufferSize

        pyBuffer = ( c_uint8 * bufferSize ).from_address( buffer )
        pyBuffer[ 0 : bytesToReturn ] = self.serverToClientPipe[ 0 : bytesToReturn ]

        # "flush" bytes:
        self.serverToClientPipe = self.serverToClientPipe[ bytesToReturn : ]

        self.log.debug( "ReadFromServer: returned %d bytes" % bytesToReturn )
        return bytesToReturn
