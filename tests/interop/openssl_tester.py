import logging
import unittest
import os
import time
import threading
import sys
import glob
import traceback
import argparse

import tlsparser
import cutils
import config

from pprint import pprint
from tlsparser          import MemorySocket, TLSParser, CString
from bio_wrapper        import BIOWrapper
from output_redirector  import stdout_redirector

import mitls_tester

from mitls_tester import memorySocket

WriteToMultipleSinks = mitls_tester.MITLSTester.WriteToMultipleSinks

from ctypes import  CDLL,           \
                    c_long,         \
                    c_int,          \
                    c_float,        \
                    c_double,       \
                    c_char_p,       \
                    create_string_buffer, \
                    byref,          \
                    addressof,      \
                    sizeof,         \
                    c_voidp,        \
                    c_uint8,        \
                    c_uint16,       \
                    c_uint32,        \
                    c_int16,           \
                    c_int32,           \
                    c_uint64,           \
                    CFUNCTYPE,          \
                    POINTER    

globalCUtils            = cutils.GetObject()

OPENSSL_SUCCESS = 1
TLS1_3_VERSION  = 0x0304

DATA_CLIENT_TO_SERVER = b"Client->Server\x00"
DATA_SERVER_TO_CLIENT = b"Server->Client\x00"

EARLY_DATA_CLIENT_TO_SERVER = b"Early-" + DATA_CLIENT_TO_SERVER

class OpenSSLError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

class EarlyDataStatus:
    SSL_EARLY_DATA_NOT_SENT = 0
    SSL_EARLY_DATA_REJECTED = 1
    SSL_EARLY_DATA_ACCEPTED = 2

    SSL_READ_EARLY_DATA_ERROR   = 0
    SSL_READ_EARLY_DATA_SUCCESS = 1
    SSL_READ_EARLY_DATA_FINISH  = 2

class OpenSSL():
    def __init__( self, name = "" ):
        self.SetupLogger( name )
        self.log.warning( "Make sure $LD_LIBRARY_PATH points to %s" % os.path.dirname( config.OPENSSL_PATH ) )
        
        self.libssl    = CDLL( config.OPENSSL_PATH )
        self.cutils     = globalCUtils

        self.clientSSLSocket = None
        self.serverSSLSocket = None 

    def Cleanup( self ):
        pass

    def SetupLogger( self, name ):
        self.log = logging.getLogger( 'OpenSSL-%s' % name )
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL )
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def VerifyResult( self, functionName, result, expectedValue = OPENSSL_SUCCESS ):
        if result != expectedValue:
            logMsg = "%s returned %d, instead of %d" % ( functionName, result, expectedValue )
            self.log.error( logMsg )
            raise OpenSSLError( logMsg )

    def CreateServerContext( self ):
    	self.libssl.TLS_server_method.restype  = c_voidp
    	self.libssl.TLS_server_method.argtypes = []
    	
    	method = self.libssl.TLS_server_method()
    	if method == None:
    		raise OpenSSLError( "TLS_server_method returned NULL" )

    	self.libssl.SSL_CTX_new.restype = c_voidp
    	self.libssl.SSL_CTX_new.argtypes = [ c_voidp ]
    	
    	ctx = self.libssl.SSL_CTX_new(method);
    	if ctx == None:
    		raise OpenSSLError( "SSL_CTX_new returned NULL" )

    	return ctx

    def CreateClientContext( self ):
        self.libssl.TLS_client_method.restype  = c_voidp
        self.libssl.TLS_client_method.argtypes = []
        
        method = self.libssl.TLS_client_method()
        if method == None:
            raise OpenSSLError( "TLS_client_method returned NULL" )

        self.libssl.SSL_CTX_new.restype = c_voidp
        self.libssl.SSL_CTX_new.argtypes = [ c_voidp ]
        
        ctx = self.libssl.SSL_CTX_new(method);
        if ctx == None:
            raise OpenSSLError( "SSL_CTX_new returned NULL" )

        return ctx
    

    def SSL_CTX_set_min_proto_version( self, version ):
    	SSL_CTRL_SET_MIN_PROTO_VERSION    =  c_int( 123 )

    	self.libssl.SSL_CTX_ctrl.restype  = c_long
    	self.libssl.SSL_CTX_ctrl.argtypes = [ c_voidp, c_int, c_long, c_voidp ]

    	result = self.libssl.SSL_CTX_ctrl( self.context, SSL_CTRL_SET_MIN_PROTO_VERSION, c_long( version ), None )
    	self.VerifyResult( "SSL_CTX_set_min_proto_version", result )

    def SSL_CTX_set_max_proto_version( self, version ):
    	SSL_CTRL_SET_MAX_PROTO_VERSION    = c_int( 124 )
    	self.libssl.SSL_CTX_ctrl.restype  = c_long
    	self.libssl.SSL_CTX_ctrl.argtypes = [ c_voidp, c_int, c_long, c_voidp ]

    	result = self.libssl.SSL_CTX_ctrl( self.context, SSL_CTRL_SET_MAX_PROTO_VERSION, c_long( version ), None )
    	self.VerifyResult( "SSL_CTX_set_max_proto_version", result )

    def ConfigureTLS1_3( self ):
    	self.SSL_CTX_set_min_proto_version( TLS1_3_VERSION )
    	self.SSL_CTX_set_max_proto_version( TLS1_3_VERSION )

    def SetCertificateAndPrivateKey( self, serverSignatureAlgorithm ):
        SSL_FILETYPE_PEM 								  = c_int( 1 )
        self.libssl.SSL_CTX_use_certificate_file.restype  = c_int
        self.libssl.SSL_CTX_use_certificate_file.argtypes = [ c_voidp, c_voidp, c_int ]
        self.libssl.SSL_CTX_use_PrivateKey_file.restype   = c_int
        self.libssl.SSL_CTX_use_PrivateKey_file.argtypes  = [ c_voidp, c_voidp, c_int ]

        self.log.debug( "Calling SSL_CTX_use_certificate_file( '%s' )" % config.SERVER_CERT_PATH[ serverSignatureAlgorithm ] )
        result = self.libssl.SSL_CTX_use_certificate_file( self.context, CString( config.SERVER_CERT_PATH[ serverSignatureAlgorithm ] ), SSL_FILETYPE_PEM )
        self.VerifyResult( "SSL_CTX_use_certificate_file", result )

        self.log.debug( "Calling SSL_CTX_use_PrivateKey_file( '%s' )" % config.SERVER_KEY_PATH[ serverSignatureAlgorithm ] )
        result = self.libssl.SSL_CTX_use_PrivateKey_file( self.context, CString( config.SERVER_KEY_PATH[ serverSignatureAlgorithm ] ), SSL_FILETYPE_PEM )
        self.VerifyResult( "SSL_CTX_use_certificate_file", result )

    def SSL_CTX_set_cipher_list( self, supportedCipherSuites ):
        self.libssl.SSL_CTX_set_cipher_list.restype = c_int
        self.libssl.SSL_CTX_set_cipher_list.argtypes = [ c_voidp, c_voidp ]
        
        cipherSuitesString = ":".join( supportedCipherSuites )
        cipherSuitesString = cipherSuitesString.replace( "_", "-" )
        cipherSuitesString = cipherSuitesString.replace( "TLS", "TLS13" )
        
        ret = self.libssl.SSL_CTX_set_cipher_list( self.context, CString( cipherSuitesString ) )
        self.VerifyResult( "SSL_CTX_set_cipher_list", ret )

    def SSL_CTX_set1_groups_list( self, supportedNamedGroups ):
        self.log.debug( "SSL_CTX_set1_groups_list( %s )" % supportedNamedGroups )
        SSL_CTRL_SET_GROUPS_LIST = 92

        self.libssl.SSL_CTX_ctrl.restype = c_long
        self.libssl.SSL_CTX_ctrl.argtypes = [ c_voidp, c_int, c_long, c_voidp ]
        
        namedGroupsString = ":".join( supportedNamedGroups )
        
        ret = self.libssl.SSL_CTX_ctrl( self.context, c_int( SSL_CTRL_SET_GROUPS_LIST ), c_long( 0 ), CString( namedGroupsString ) )
        self.VerifyResult( "SSL_CTX_set1_groups_list (implemented via SSL_CTX_ctrl)", ret )

    def SSL_CTX_set_tlsext_ticket_key_cb( self, callbackAddress ):
        SSL_CTRL_SET_TLSEXT_TICKET_KEY_CB  = 72
        self.log.debug( "SSL_CTX_set_tlsext_ticket_key_cb; callbackAddress = 0x%x" % callbackAddress )

        self.libssl.SSL_CTX_callback_ctrl.restype  = c_long
        self.libssl.SSL_CTX_callback_ctrl.argtypes = [ c_voidp, c_int, c_voidp ]
        result = self.libssl.SSL_CTX_callback_ctrl(     self.context, 
                                                        c_int( SSL_CTRL_SET_TLSEXT_TICKET_KEY_CB ), 
                                                        callbackAddress )
        self.VerifyResult( "SSL_CTX_set_tlsext_ticket_key_cb (via SSL_CTX_callback_ctrl)", result )

    def SSL_CTX_set1_sigalgs_list( self, supportedSignatureAlgorithms ):
        SSL_CTRL_SET_SIGALGS_LIST = 98

        self.libssl.SSL_CTX_ctrl.restype = c_long
        self.libssl.SSL_CTX_ctrl.argtypes = [ c_voidp, c_int, c_long, c_voidp ]
        
        signatureAlgorithmsString = ":".join( supportedSignatureAlgorithms )
        
        ret = self.libssl.SSL_CTX_ctrl( self.context, c_int( SSL_CTRL_SET_SIGALGS_LIST ), c_long( 0 ), CString( signatureAlgorithmsString ) )
        self.VerifyResult( "SSL_CTX_set1_sigalgs_list (implemented via SSL_CTX_ctrl)", ret )

    def InitServer( self, 
                    memorySocket,
                    supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                    serverSignatureAlgorithm        = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS[ 0 ],
                    supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS  ):
        self.log.debug( "InitServer" )

        self.context = self.CreateServerContext()
        self.ConfigureTLS1_3()
        self.SetCertificateAndPrivateKey( serverSignatureAlgorithm )
        self.SSL_CTX_set_cipher_list  ( supportedCipherSuites )
        self.SSL_CTX_set1_groups_list ( supportedNamedGroups )
        self.SSL_CTX_set_tlsext_ticket_key_cb( globalCUtils.getAddress( globalCUtils.ssl_tlsext_ticket_key_cb ) )
        # self.SSL_CTX_set1_sigalgs_list( supportedSignatureAlgorithms )

        self.memorySocket = memorySocket

    def InitClient( self, 
                    memorySocket, 
                    hostName, 
                    supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                    supportedSignatureAlgorithms    = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS,
                    supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS ):
        self.log.debug( "InitClient" )

        self.context = self.CreateClientContext()
        self.ConfigureTLS1_3()
        self.SSL_CTX_set_cipher_list( supportedCipherSuites )
        self.SSL_CTX_set1_groups_list( supportedNamedGroups )
        self.SSL_CTX_set1_sigalgs_list( supportedSignatureAlgorithms )
        

        self.memorySocket = memorySocket

    def InitializeSSLServerSocket( self ):
        self.log.debug( "InitializeSSLServerSocket" )
        self.serverMemorySocket               = BIOWrapper()
        self.serverMemorySocket.ReadCallback  = self.memorySocket.ReadFromClient
        self.serverMemorySocket.WriteCallback = self.memorySocket.SendToClient

        self.libssl.SSL_new.restype  = c_voidp
        self.libssl.SSL_new.argtypes = [ c_voidp ]
        self.serverSSLSocket = self.libssl.SSL_new( self.context )
        if self.serverSSLSocket is None:
            raise OpenSSLError( "SSL_new returned NULL" )

        self.libssl.SSL_set_bio.restype  = None
        self.libssl.SSL_set_bio.argtypes = [ c_voidp, c_voidp, c_voidp ]
        self.libssl.SSL_set_bio( self.serverSSLSocket, self.serverMemorySocket.bioObject, self.serverMemorySocket.bioObject )

    def InitializeSSLClientSocket( self ):
        self.log.debug( "InitializeSSLClientSocket" )
        self.clientMemorySocket               = BIOWrapper()
        self.clientMemorySocket.ReadCallback  = self.memorySocket.ReadFromServer
        self.clientMemorySocket.WriteCallback = self.memorySocket.SendToServer

        self.libssl.SSL_new.restype  = c_voidp
        self.libssl.SSL_new.argtypes = [ c_voidp ]
        self.clientSSLSocket = self.libssl.SSL_new( self.context )
        if self.clientSSLSocket is None:
            raise OpenSSLError( "SSL_new returned NULL" )

        self.libssl.SSL_set_bio.restype  = None
        self.libssl.SSL_set_bio.argtypes = [ c_voidp, c_voidp, c_voidp ]
        self.libssl.SSL_set_bio( self.clientSSLSocket, self.clientMemorySocket.bioObject, self.clientMemorySocket.bioObject )

    def SSL_accept( self ):
        self.log.debug( "SSL_accept" )
        self.libssl.SSL_accept.restype  = c_int
        self.libssl.SSL_accept.argtypes = [ c_voidp ]

        result = self.libssl.SSL_accept( self.serverSSLSocket )
        self.VerifyResult( "SSL_accept", result )

    def GetSession( self ):
        self.log.debug( "GetSession" )

        self.libssl.SSL_get_session.restype  = c_voidp
        self.libssl.SSL_get_session.argtypes = [ c_voidp ]

        if self.clientSSLSocket != None: 
            session = self.libssl.SSL_get_session( self.clientSSLSocket )
        elif self.serverSSLSocket != None:
            session = self.libssl.SSL_get_session( self.serverSSLSocket )
        else:
            raise OpenSSLError( "Neither client nor server" )

        if session == 0:
            raise OpenSSLError( "GetSession returned NULL" )

        self.log.debug( "session = 0x%x" % session )
        return session

    def SerializeSession( self, sslSession ):
        serializedSession       = c_voidp( None )

        self.libssl.i2d_SSL_SESSION.restype = c_int
        self.libssl.i2d_SSL_SESSION.argtypes = [ c_voidp, c_voidp ]
        serializedSessionSize = self.libssl.i2d_SSL_SESSION( sslSession, byref( serializedSession ) )
        if serializedSessionSize <= 0:
            raise OpenSSLError( "i2d_SSL_SESSION returned %d" % serializedSessionSize )

        self.log.debug( "serializedSession = %s; serializedSessionSize = %s" % ( serializedSession, serializedSessionSize ) )
        
        if serializedSession == None:
            raise OpenSSLError( "i2d_SSL_SESSION returned NULL ticket" )

        return bytearray( ( c_uint8 * serializedSessionSize ).from_address( serializedSession.value ) )

    def GetSessionTicket( self ):
        self.log.debug( "GetSessionTicket" )
        if self.clientSSLSocket is None:
            raise OpenSSLError( "Must be client to get session ticket" )

        sslSession              = self.GetSession() #SSL_get_session
        serializedSession       = self.SerializeSession( sslSession )

         # This is not a "ticket" in TLS terms, but rather a "session" in OpenSSL terms.
        ticket = serializedSession

        return ticket

    def ReadEarlyData( self, verifyNoMoreData = False ):
        self.log.debug( "ReadEarlyData" )
        if self.serverSSLSocket is None:
            raise OpenSSLError( "Must be server to read early data. 0.5RTT not imlemented yet." ) #Technically, can also be client for 0.5RTT, but that's not implemented yet

        maxEarlyData = 1024
        cBuffer      = ( c_uint8 * maxEarlyData )()
        bytesRead    = c_long( 0 )

        self.libssl.SSL_read_early_data.restype  = c_int
        self.libssl.SSL_read_early_data.argtypes = [ c_voidp, c_voidp, c_long, c_voidp ]
        result = self.libssl.SSL_read_early_data(   self.serverSSLSocket,
                                                    cBuffer,
                                                    c_long( maxEarlyData ),
                                                    byref( bytesRead ) )
        if result != EarlyDataStatus.SSL_READ_EARLY_DATA_SUCCESS and \
           result != EarlyDataStatus.SSL_READ_EARLY_DATA_FINISH:
                raise OpenSSLError( "SSL_read_early_data returned %d" % result)
        if verifyNoMoreData:
            self.VerifyResult( "SSL_read_early_data", result, expectedValue = EarlyDataStatus.SSL_READ_EARLY_DATA_FINISH )

        earlyData = bytes( cBuffer[ 0 : bytesRead.value ] )
        self.log.debug( "Read %d bytes: %s" % ( bytesRead.value, earlyData ) )
        
        return earlyData
        
      # For server side:
    def AcceptConnection( self, applicationData = None, allowEarlyData = False ):
        self.log.debug( "AcceptConnection" )
        self.acceptConnectionSucceeded = False

        try:
            self.InitializeSSLServerSocket()

            self.dataReceived = b""
            # gotEarlyData      = False
            if allowEarlyData:
                self.dataReceived += self.ReadEarlyData() 
                self.log.debug( "Got early data: %s" % self.dataReceived )
                gotEarlyData = ( len( self.dataReceived ) > 0 )

            self.SSL_accept()
            self.dataReceived += self.Recv()

            if applicationData != None:
                self.Send( applicationData )

            # if gotEarlyData:
            #     earlyDataLeftovers = self.ReadEarlyData( verifyNoMoreData = True )
            #     if len( earlyDataLeftovers ) > 0:
            #         raise OpenSSLError( "Didn't expect to receive additional early data: %s" % earlyDataLeftovers)

            self.acceptConnectionSucceeded = True
        except Exception as err: 
            pprint( traceback.format_tb( err.__traceback__ ) )
            pprint( err )

    def SSL_connect( self ):
        self.log.debug( "SSL_connect" )
        self.libssl.SSL_connect.restype  = c_int
        self.libssl.SSL_connect.argtypes = [ c_voidp ]

        result = self.libssl.SSL_connect( self.clientSSLSocket )
        self.VerifyResult( "SSL_connect", result )

    def DeserializeSession( self, serializedSession ):
        self.log.debug( "DeserializeSession: len( serializedSession ) = %d" % len( serializedSession ) )
        serializedSession_c = c_voidp( addressof( ( c_uint8 * len( serializedSession ) ).from_buffer( serializedSession ) ) )

        session = c_voidp( None )
        self.libssl.d2i_SSL_SESSION.restype  = c_voidp
        self.libssl.d2i_SSL_SESSION.argtypes = [ c_voidp, c_voidp, c_long ] 
        returnedSession = self.libssl.d2i_SSL_SESSION( byref( session ), byref( serializedSession_c ), c_long( len( serializedSession ) ) )
        self.log.debug( "session = %s" % session)
        if returnedSession is None or returnedSession != session.value:
            raise OpenSSLError( "d2i_SSL_SESSION returned invalid value (returnedSession = %s)" % returnedSession )

        return session

    def SetSessionTicket( self, sessionTicket ):
        self.log.debug( "SetSessionTicket" )
        if self.clientSSLSocket is None:
            raise OpenSSLError( "Must be client to set a ticket" )

        sslSession = self.DeserializeSession( sessionTicket )
        
        self.libssl.SSL_set_session.restype  = c_int
        self.libssl.SSL_set_session.argtypes = [ c_voidp, c_voidp ]
        result = self.libssl.SSL_set_session( self.clientSSLSocket, sslSession )
        self.VerifyResult( "SSL_set_session", result ) 

    def GetMaxEarlyData( self ):
        self.log.debug( "GetMaxEarlyData" )
        if self.clientSSLSocket is None:
            raise OpenSSLError( "Must be client to send early data" )

        self.libssl.SSL_SESSION_get_max_early_data.restype  = c_uint32
        self.libssl.SSL_SESSION_get_max_early_data.argtypes = [ c_voidp ]
        maxEarlyData = self.libssl.SSL_SESSION_get_max_early_data( self.GetSession() )
        
        self.log.debug( "maxEarlyData = %s" % maxEarlyData )
        return maxEarlyData

    def GetEarlyDataStatus( self, expectedValue = None ):
        self.log.debug( "GetEarlyDataStatus" )

        sslSocket = self.clientSSLSocket
        if self.clientSSLSocket is None:
            sslSocket = self.serverSSLSocket

        self.libssl.SSL_get_early_data_status.restype  = c_int
        self.libssl.SSL_get_early_data_status.argtypes = [ c_voidp ]
        status = self.libssl.SSL_get_early_data_status( sslSocket )

        if expectedValue != None:
            self.VerifyResult( "SSL_get_early_data_status", status, expectedValue = expectedValue )

    def SendEarlyData( self, earlyData ):
        self.log.debug( "SendEarlyData" )
        if self.clientSSLSocket is None:
            raise OpenSSLError( "Must be client to send early data" )

        if self.GetMaxEarlyData() <= 0:
            raise OpenSSLError( "Can't send early data" )

        buffer  = bytearray( earlyData )
        cBuffer = ( c_uint8 * len( earlyData ) ).from_buffer( buffer )
        written = c_long( 0 )

        self.libssl.SSL_write_early_data.restype  = c_int
        self.libssl.SSL_write_early_data.argtypes = [ c_voidp, c_voidp, c_long, c_voidp ]
        result = self.libssl.SSL_write_early_data(  self.clientSSLSocket,
                                                     cBuffer,
                                                     c_long( len( earlyData ) ),
                                                     byref( written ) )
        self.VerifyResult( "SSL_write_early_data", result )

     # For client side
    def Connect( self, supportedNamedGroups = None, sessionTicket = None, earlyData = None ):
        self.log.debug( "Connect" )
        self.InitializeSSLClientSocket()

        if sessionTicket != None:
            self.SetSessionTicket( sessionTicket )

        if earlyData != None:
            self.SendEarlyData( earlyData )

        self.SSL_connect()

        if earlyData != None:
            self.GetEarlyDataStatus( expectedValue = EarlyDataStatus.SSL_EARLY_DATA_ACCEPTED )

    def Send( self, buffer ):
        self.log.debug( "Send: %s" % buffer )
        buffer      = bytearray( buffer )
        cBuffer     = ( c_uint8 * len( buffer ) ).from_buffer( buffer )
        
        if self.clientSSLSocket != None:
            sslSocket = self.clientSSLSocket
        else:
            sslSocket = self.serverSSLSocket

        self.libssl.SSL_write.restype  = c_int
        self.libssl.SSL_write.argtypes = [ c_voidp, c_voidp, c_int ]

        result = self.libssl.SSL_write( sslSocket, cBuffer, c_int( len( buffer ) ) )
        self.log.info( "SSL_write returned %d" % result)

        return result

    def Recv( self ):
        self.log.debug( "Recv" )

        SSL_ERROR_WANT_READ  = 2
        
        bufferSize  = 1024
        buffer      = bytearray( bufferSize )
        cBuffer     = ( c_uint8 * bufferSize ).from_buffer( buffer )
        
        if self.clientSSLSocket != None:
            sslSocket = self.clientSSLSocket
        else:
            sslSocket = self.serverSSLSocket

        self.libssl.SSL_read.restype  = c_int
        self.libssl.SSL_read.argtypes = [ c_voidp, c_voidp, c_int ]

        errorCode           = SSL_ERROR_WANT_READ;
        numRetries          = 2
        while errorCode == SSL_ERROR_WANT_READ and numRetries > 0: 
            numRetries -= 1

            bytesReceived = self.libssl.SSL_read( sslSocket, cBuffer, c_int( bufferSize ) )
            self.log.info( "SSL_read returned %d" % bytesReceived)
            if bytesReceived > 0:
                break

            errorCode = self.SSL_get_error( sslSocket, bytesReceived );

        if bytesReceived > 0:
            return bytearray( cBuffer[ : bytesReceived ] )
        #else:
        return b""

    def SSL_get_error( self, sslSocket, result ):
        self.libssl.SSL_get_error.restype  = c_int
        self.libssl.SSL_get_error.argtypes = [ c_voidp, c_int ]

        return self.libssl.SSL_get_error( sslSocket, c_int( result ) )

#########################################################################


class OpenSSLTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(OpenSSLTester, self).__init__(*args, **kwargs)
        self.SetupLogger()

    def setUp( self ):
        self.tlsServer = None
        self.tlsClient = None

    def tearDown( self ):
        pass

    def SetupLogger( self ):
        self.log = logging.getLogger( 'OpenSSLTester' )
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL )
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def test_ClientAndServer_sessionResumption_0RTT( self ):
        cipherSuite = "TLS_AES_128_GCM_SHA256"
        algorithm = 'ECDSA+SHA256'
        group     = "X25519"
        sessionTicket = self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                                            supportedSignatureAlgorithms = [ algorithm ],
                                            supportedNamedGroups         = [ group ] )
        transcript1 = memorySocket.tlsParser.transcript[ : ]
        # pprint( "sessionTicket = %s" % sessionTicket )
        self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                            supportedSignatureAlgorithms = [ algorithm ],
                            supportedNamedGroups         = [ group ],
                            sessionTicket                = sessionTicket,
                            allowEarlyData               = True )
        transcript2 = memorySocket.tlsParser.transcript[ : ]

        if config.LOG_LEVEL < logging.ERROR:
            for msg in (transcript1 + transcript2):
                memorySocket.tlsParser.PrintMsg( msg )

    def test_ClientAndServer_sessionResumption( self ):
        cipherSuite = "TLS_AES_128_GCM_SHA256"
        algorithm = 'ECDSA+SHA256'
        group     = "X25519"
        sessionTicket = self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                                            supportedSignatureAlgorithms = [ algorithm ],
                                            supportedNamedGroups         = [ group ] )
        transcript1 = memorySocket.tlsParser.transcript[ : ]
        # pprint( "sessionTicket = %s" % sessionTicket )
        self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                            supportedSignatureAlgorithms = [ algorithm ],
                            supportedNamedGroups         = [ group ],
                            sessionTicket                = sessionTicket )
        transcript2 = memorySocket.tlsParser.transcript[ : ]

        if config.LOG_LEVEL < logging.ERROR:
            for msg in (transcript1 + transcript2):
                memorySocket.tlsParser.PrintMsg( msg )

    def test_ClientAndServer( self ):
        cipherSuite = "TLS_AES_128_GCM_SHA256"
        algorithm = 'ECDSA+SHA256'
        group     = "X25519"
        self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                            supportedSignatureAlgorithms = [ algorithm ],
                            supportedNamedGroups         = mitls_tester.SUPPORTED_NAMED_GROUPS )

        if config.LOG_LEVEL < logging.ERROR:
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )

                # if tlsparser.IV_AND_KEY in msg.keys():
                #     pprint( msg[ tlsparser.IV_AND_KEY ])

        # print( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        # print( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )

    def StartServerThread(  self, 
                            supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                            serverSignatureAlgorithm        = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS[ 0 ],
                            supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS,
                            applicationData                 = None,
                            allowEarlyData                  = False ):
        self.tlsServer = OpenSSL( "server" )
        self.tlsServer.InitServer(  memorySocket,
                                    supportedCipherSuites, 
                                    serverSignatureAlgorithm, 
                                    supportedNamedGroups )
        
        serverThread   = threading.Thread(target = self.tlsServer.AcceptConnection, args = [ applicationData, allowEarlyData ] )
        serverThread.start()

        return serverThread

    def RunSingleTest(  self, 
                        supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                        supportedSignatureAlgorithms    = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS,
                        supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS,
                        msgManipulators                 = [],
                        serverSignatureAlgorithm        = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS[ 0 ],
                        sessionTicket                   = None,
                        allowEarlyData                  = True ):

        memorySocket.FlushBuffers()
        memorySocket.tlsParser = tlsparser.TLSParser()
        memorySocket.tlsParser.SetMsgManipulators( msgManipulators )
        serverThread = self.StartServerThread(  supportedCipherSuites       = supportedCipherSuites,
                                                serverSignatureAlgorithm    = serverSignatureAlgorithm,
                                                supportedNamedGroups        = supportedNamedGroups,
                                                applicationData             = DATA_SERVER_TO_CLIENT,
                                                allowEarlyData              = allowEarlyData     )

        self.tlsClient = OpenSSL( "client" )
        self.tlsClient.InitClient(  memorySocket,
                                    "test_server.com", 
                                    supportedCipherSuites,
                                    supportedSignatureAlgorithms,
                                    supportedNamedGroups )
        earlyData          = None
        serverExpectedData = DATA_CLIENT_TO_SERVER
        if allowEarlyData and sessionTicket != None:
            earlyData          = EARLY_DATA_CLIENT_TO_SERVER
            serverExpectedData = EARLY_DATA_CLIENT_TO_SERVER + DATA_CLIENT_TO_SERVER

        self.tlsClient.Connect( sessionTicket = sessionTicket, earlyData = earlyData )
        self.tlsClient.Send( DATA_CLIENT_TO_SERVER )            
        self.tlsClient.dataReceived = self.tlsClient.Recv()

        sessionTicket = self.tlsClient.GetSessionTicket()

        serverThread.join()
        if self.tlsServer.acceptConnectionSucceeded == False:
            raise Exception( "Server failed to connect" )

        if self.tlsClient.dataReceived != DATA_SERVER_TO_CLIENT:
            raise Exception( "self.tlsClient.dataReceived = %s, instead of expected %s" % ( self.tlsClient.dataReceived, DATA_SERVER_TO_CLIENT ) )           


        if self.tlsServer.dataReceived != serverExpectedData:
            raise Exception( "self.tlsServer.dataReceived = %s, instead of expected %s" % ( self.tlsServer.dataReceived, serverExpectedData ) )
            
        self.log.debug( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        self.log.debug( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        return sessionTicket

    def test_parameters_matrix( self ):
        sys.stderr.write( "Running test_parameters_matrix\n" )

        with open( "parameters_matrix_OPENSSL_OPENSSL.csv", "w" ) as logFile:
            outputSinks = [ sys.stderr, logFile ]
            WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s %-15s%-6s\n" % ("CipherSuite,", "SignatureAlgorithm,", "NamedGroup,", "PassFail,", "Time (seconds)") )

            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                    for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                        WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s " % ( cipherSuite+",", algorithm+",", group+"," ) )

                        memorySocket.tlsParser.DeleteLeakedKeys()
                        try:
                            startTime = time.time()
                            self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                                                supportedSignatureAlgorithms = [ algorithm ],
                                                supportedNamedGroups         = [ group ],
                                                serverSignatureAlgorithm     = algorithm )
                            WriteToMultipleSinks( outputSinks, "%-15s" % ("OK,") )

                            for msg in memorySocket.tlsParser.transcript:
                                memorySocket.tlsParser.PrintMsg( msg )
                        except Exception as err: 
                            pprint( traceback.format_tb( err.__traceback__ ) )
                            pprint( err )
                            WriteToMultipleSinks( outputSinks, "%-15s" % "FAILED," )
                            # raise
                        finally:
                            totalTime = time.time() - startTime
                            WriteToMultipleSinks( outputSinks, "%-6f\n" % totalTime )
                  

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    mitls_tester.ConfigureMITLSArguments( parser )

    args   = parser.parse_args()
    mitls_tester.HandleMITLSArguments( args )

    memorySocket.log.setLevel( config.LOG_LEVEL )    

    suite = unittest.TestSuite()
    suite.addTest( OpenSSLTester( 'test_ClientAndServer' ) )
    # suite.addTest( OpenSSLTester( 'test_ClientAndServer_sessionResumption' ) )
    # suite.addTest( OpenSSLTester( 'test_ClientAndServer_sessionResumption_0RTT' ) )
    # suite.addTest( OpenSSLTester( 'test_parameters_matrix' ) )
    # suite.addTest( NSSTester( '' ) )
    
    runner=unittest.TextTestRunner()
    
    if args.supress_output:
        devNull = open( "/dev/null", "wb" )
        with stdout_redirector( devNull ):
            runner.run(suite)
    else:
        runner.run(suite)

