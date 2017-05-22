import unittest
import logging
import os
import sys
import time
import threading
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
SUCCESS                     = 1
NULL_BYTE                   = b"\0"
TLS_VERSION_1_3             = b"1.3" + NULL_BYTE
MITLS_SO_PATH               = "../../../everest/mitls-fstar/src/tls/libmitls.so"
SERVER_CERT_PATH            = "../../../everest/mitls-fstar/data/server-ecdsa.crt" 
SERVER_KEY_PATH             = "../../../everest/mitls-fstar/data/server-ecdsa.key"
SERVER_SIGNATURE_ALGORITHM  = "ECDSA+SHA384"
# SERVER_NAMED_GROUPS         = ""

class MITLSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

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
        # self.ParseClientHello_Extensions( extensions )

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

    def Digest( self, bytes, printPacket = False ):
        if printPacket:
            sys.stdout.write( Green( self.FormatBuffer( bytes ) )  + "\n" )

        self.recentBytes += bytes
        if len( self.recentBytes ) < TLS_RECORD_HEADER_SIZE:
            return

        msg = self.ParseMsgHeader()
        if len( self.recentBytes ) >= TLS_RECORD_HEADER_SIZE + msg[ 'length' ]:
            self.ParseMsgBody( msg )



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

memorySocket = MemorySocket()

#Used by client to send to server:
def SendToServer( ctx, buffer, bufferSize ):
    # print( "SendToServer" )
    return memorySocket.SendToServer( ctx, buffer, bufferSize )

#Used by server to read from client:
def ReadFromClient( ctx, buffer, bufferSize ):
    # print( "ReadFromClient" )
    return memorySocket.ReadFromClient( ctx, buffer, bufferSize )

#Used by server to send to client:
def SendToClient( ctx, buffer, bufferSize ):
    # print( "SendToClient" )
    return memorySocket.SendToClient( ctx, buffer, bufferSize )

#Used by client to read from server:
def ReadFromServer( ctx, buffer, bufferSize  ):
    # print( "ReadFromServer" )
    return memorySocket.ReadFromServer( ctx, buffer, bufferSize )

GLOBAL_MITLS_INITIALIZED = False

class MITLS():
    def __init__( self, name = "", sharedObjectPath = MITLS_SO_PATH  ):
        self.SetupLogger( name )
        self.log.info( "Initilizaed with sharedObjectPath = %s" % os.path.abspath( sharedObjectPath ) )
        
        self.miTLS          = CDLL( sharedObjectPath ) 
        self.cutils         = CDLL( "cutils/cutils.so" )
        self.mitls_state    = None 

        global GLOBAL_MITLS_INITIALIZED
        if GLOBAL_MITLS_INITIALIZED == False:
            self.FFI_mitls_init() 
            GLOBAL_MITLS_INITIALIZED = True

    def Cleanup( self ):
        self.log.debug( "Cleanup" )
        if self.mitls_state is not None:
            self.log.debug( "FFI_mitls_close")
            self.miTLS.FFI_mitls_close( self.mitls_state )
            self.mitls_state = None

    def SetupLogger( self, name ):
        self.log = logging.getLogger( 'MITLS-%s' % name )
        self.log.setLevel(logging.DEBUG)

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel(logging.DEBUG)
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def VerifyResult( self, functionName, result, expectedValue = SUCCESS ):
        if result != expectedValue:
            logMsg = "%s returned %d, instead of %d" % ( functionName, result, expectedValue )
            self.log.error( logMsg )
            raise MITLSError( logMsg )

    def FFI_mitls_init( self ):
        self.log.debug( "FFI_mitls_init" )
        
        self.miTLS.FFI_mitls_init.restype = c_int
        result = self.miTLS.FFI_mitls_init()
        self.VerifyResult( "FFI_mitls_init", result )
        
        return result

    def FFI_mitls_thread_register( self ):
        self.log.debug( "FFI_mitls_thread_register" )
        
        self.miTLS.FFI_mitls_thread_register.restype = c_int
        result = self.miTLS.FFI_mitls_thread_register()
        self.VerifyResult( "FFI_mitls_thread_register", result )
        
        return result

    def PrintMsgIfNotNull( self, outmsg, errmsg ):
        if outmsg.value != None:
            self.log.error( 'outmsg = "%s"' % outmsg.value )
            self.miTLS.FFI_mitls_free_msg( outmsg )

        if errmsg.value != None:
            self.log.error( 'errmsg = "%s"' % errmsg.value )
            self.miTLS.FFI_mitls_free_msg( errmsg )

    def MITLS_Configure( self, hostName = "" ):
        self.log.debug( "MITLS_Configure" )
        mitls_state = c_voidp()
        tls_version = c_char_p( TLS_VERSION_1_3 )
        host_name   = c_char_p( bytes( hostName, "ascii" ) + NULL_BYTE )
        outmsg      = c_char_p()
        errmsg      = c_char_p()

        self.miTLS.FFI_mitls_configure.restype = c_int
        ret = self.miTLS.FFI_mitls_configure(   byref( mitls_state ),
                                                tls_version,
                                                host_name,
                                                byref( outmsg ),
                                                byref( errmsg ) )
        self.PrintMsgIfNotNull( outmsg, errmsg )
        self.VerifyResult( "FFI_mitls_configure", ret )

        return mitls_state

    def MITLS_configure_cert_chain_file( self, filePath ):
        self.log.debug( "MITLS_configure_cert_chain_file; filePath = %s" % os.path.abspath( filePath ) )
        self.miTLS.FFI_mitls_configure_cert_chain_file.restype = c_int

        serverCertPath = c_char_p( bytes( filePath, "ascii" ) + NULL_BYTE )
        ret            = self.miTLS.FFI_mitls_configure_cert_chain_file( self.mitls_state, serverCertPath )
        self.VerifyResult( "FFI_mitls_configure_cert_chain_file", ret )

    def MITLS_configure_private_key_file( self, filePath ):
        self.log.debug( "MITLS_configure_private_key_file; filePath = %s" % os.path.abspath( filePath ) )
        self.miTLS.FFI_mitls_configure_private_key_file.restype = c_int

        serverKeyPath = c_char_p( bytes( filePath, "ascii" ) + NULL_BYTE )
        ret           = self.miTLS.FFI_mitls_configure_private_key_file( self.mitls_state, serverKeyPath )
        self.VerifyResult( "FFI_mitls_configure_private_key_file", ret )

    def FFI_mitls_configure_signature_algorithms( self, signatureAlgorithm ):
        self.log.debug( 'FFI_mitls_configure_signature_algorithms; signatureAlgorithm = "%s"' % signatureAlgorithm )
        self.miTLS.FFI_mitls_configure_cipher_suites.restype = c_int

        cipherSuite_c = c_char_p( bytes( signatureAlgorithm, "ascii" ) + NULL_BYTE )
        ret           = self.miTLS.FFI_mitls_configure_signature_algorithms( self.mitls_state, cipherSuite_c )
        self.VerifyResult( "FFI_mitls_configure_signature_algorithms", ret )

    # def MITLS_configure_named_groups( self, namedGroups ):
    #     self.log.debug( 'MITLS_configure_cipher_suites; namedGroups = "%s"' )
    #     self.miTLS.FFI_mitls_configure_named_groups.restype = c_int

    #     namedGroups_c = c_char_p( bytes( namedGroups, "ascii" ) + NULL_BYTE )
    #     ret           = self.miTLS.FFI_mitls_configure_named_groups( self.mitls_state, namedGroups_c )
    #     self.VerifyResult( "FFI_mitls_configure_named_groups", ret )

    def InitServer( self ):
        self.log.debug( "InitServer" )

        self.mitls_state = self.MITLS_Configure()
        self.MITLS_configure_cert_chain_file            ( SERVER_CERT_PATH )
        self.MITLS_configure_private_key_file           ( SERVER_KEY_PATH )
        self.FFI_mitls_configure_signature_algorithms   ( SERVER_SIGNATURE_ALGORITHM )
        # self.MITLS_configure_named_groups    ( SERVER_NAMED_GROUPS )

    def InitClient( self, hostName ):
        self.log.debug( "InitClient" )

        self.mitls_state = self.MITLS_Configure( hostName )

    def GetClientCallbacks( self ):
        # Callbacks are defined in mitls.h:
        # typedef int (*pfn_FFI_send)(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size);
        # typedef int (*pfn_FFI_recv)(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size);
        MITLS_CALLBACK      = CFUNCTYPE(c_int, c_voidp, c_voidp, c_long ) 
        self.sendCallback   = MITLS_CALLBACK( SendToServer )
        self.recvCallback   = MITLS_CALLBACK( ReadFromServer )

        self.cutils.getAddress.restype = c_voidp

        FFI_mitls_callbacks = (c_voidp * 2)()
        FFI_mitls_callbacks[ 0 ] = self.cutils.getAddress( self.sendCallback )
        FFI_mitls_callbacks[ 1 ] = self.cutils.getAddress( self.recvCallback )

        return FFI_mitls_callbacks

    def GetServerCallbacks( self ):
        # Callbacks are defined in mitls.h:
        # typedef int (*pfn_FFI_send)(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size);
        # typedef int (*pfn_FFI_recv)(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size);
        MITLS_CALLBACK      = CFUNCTYPE(c_int, c_voidp, c_voidp, c_long ) 
        self.sendCallback   = MITLS_CALLBACK( SendToClient )
        self.recvCallback   = MITLS_CALLBACK( ReadFromClient )

        self.cutils.getAddress.restype = c_voidp

        FFI_mitls_callbacks = (c_voidp * 2)()
        FFI_mitls_callbacks[ 0 ] = self.cutils.getAddress( self.sendCallback )
        FFI_mitls_callbacks[ 1 ] = self.cutils.getAddress( self.recvCallback )

        return FFI_mitls_callbacks

    def AcceptConnection( self ):
        self.log.debug( "AcceptConnection" )
        outmsg              = c_char_p()
        errmsg              = c_char_p() 
        FFI_mitls_callbacks = self.GetServerCallbacks()

        self.miTLS.FFI_mitls_accept_connected.restype  = c_int
        self.miTLS.FFI_mitls_accept_connected.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp ]

        ret = self.miTLS.FFI_mitls_thread_register()
        self.VerifyResult( "FFI_mitls_thread_register", ret )

        ret = self.miTLS.FFI_mitls_accept_connected(FFI_mitls_callbacks,
                                                    self.mitls_state,
                                                    byref( outmsg ),
                                                    byref( errmsg ) )
        self.PrintMsgIfNotNull( outmsg, errmsg )
        self.VerifyResult( "FFI_mitls_accept_connected", ret )
        self.log.debug( "FFI_mitls_accept_connected done!")

    # For client side
    def Connect( self ):
        self.log.debug( "Connect" )
        outmsg              = c_char_p()
        errmsg              = c_char_p() 
        FFI_mitls_callbacks = self.GetClientCallbacks()

        self.miTLS.FFI_mitls_connect.restype = c_int
        self.miTLS.FFI_mitls_connect.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp ]

        ret = self.miTLS.FFI_mitls_connect( FFI_mitls_callbacks,
                                            self.mitls_state,
                                            byref( outmsg ),
                                            byref( errmsg ) )
        self.PrintMsgIfNotNull( outmsg, errmsg )
        self.VerifyResult( "FFI_mitls_connect", ret )

class MITLSTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(MITLSTester, self).__init__(*args, **kwargs)

    def setUp(self):
        self.tlsServer = None
        self.tlsClient = None

    def tearDown(self):
        if self.tlsServer is not None:
            self.tlsServer.Cleanup()
        if self.tlsClient is not None:
            self.tlsClient.Cleanup()

    def testInitMITLS( self ):
        self.tlsServer = MITLS( "server" )
        self.tlsClient = MITLS( "client" )

    def testSetupServer( self ):
        self.tlsServer = MITLS( "server" )
        self.tlsServer.InitServer()

    def testSetupClient( self ):
        hostName = "test_server.com"

        self.tlsServer = MITLS( "client" )
        self.tlsServer.InitClient( hostName )

    def testClientAndServer( self ):
        hostName = "test_server.com"

        self.tlsServer = MITLS( "server" )
        self.tlsServer.InitServer()

        # self.tlsServer.AcceptConnection()
        serverThread = threading.Thread(target = self.tlsServer.AcceptConnection )
        serverThread.start()

        self.tlsClient = MITLS( "client" )
        self.tlsClient.InitClient( hostName )
        self.tlsClient.Connect()
        print( "########################")

        serverThread.join()
if __name__ == '__main__':
	unittest.main()



