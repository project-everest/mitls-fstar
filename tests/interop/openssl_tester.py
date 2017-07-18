import logging
import unittest
import os
import time
import threading
import sys
import glob

import tlsparser
import cutils
import config

from pprint import pprint
from tlsparser import MemorySocket, TLSParser, CString
from bio_wrapper import BIOWrapper


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

class OpenSSLError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

class OpenSSL():
    def __init__( self, name = "" ):
        self.SetupLogger( name )
        self.log.warning( "Make sure $LD_LIBRARY_PATH points to %s" % os.path.dirname( config.OPENSSL_PATH ) )
        
        self.libssl    = CDLL( config.OPENSSL_PATH )
        self.cutils     = globalCUtils

        self.clientSSLSocket = None
        self.serverSSLSocket = None 

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

    def SetCertificateAndPrivateKey( self ):
        SSL_FILETYPE_PEM 								  = c_int( 1 )
        self.libssl.SSL_CTX_use_certificate_file.restype  = c_int
        self.libssl.SSL_CTX_use_certificate_file.argtypes = [ c_voidp, c_voidp, c_int ]
        self.libssl.SSL_CTX_use_PrivateKey_file.restype   = c_int
        self.libssl.SSL_CTX_use_PrivateKey_file.argtypes  = [ c_voidp, c_voidp, c_int ]

        result = self.libssl.SSL_CTX_use_certificate_file( self.context, CString( config.SERVER_CERT_PATH ), SSL_FILETYPE_PEM )
        self.VerifyResult( "SSL_CTX_use_certificate_file", result )

        result = self.libssl.SSL_CTX_use_PrivateKey_file( self.context, CString( config.SERVER_KEY_PATH ), SSL_FILETYPE_PEM )
        self.VerifyResult( "SSL_CTX_use_certificate_file", result )

    def InitServer( self, memorySocket ):
        self.log.debug( "InitServer" )

        self.context = self.CreateServerContext()
        self.ConfigureTLS1_3()
        self.SetCertificateAndPrivateKey()
        # self.ConfigureSignatureAlgorithms()

        self.memorySocket = memorySocket

    def InitClient( self, memorySocket, hostName ):
        self.log.debug( "InitClient" )

        self.context = self.CreateClientContext()
        self.ConfigureTLS1_3()
        # self.ConfigureSignatureAlgorithms()

        self.memorySocket = memorySocket

    def InitializeSSLServerSocket( self ):
        self.log.debug( "InitializeSSLServerSocket" )
        self.serverMemorySocket               = BIOWrapper()
        self.serverMemorySocket.ReadCallback  = self.memorySocket.ReadFromClient
        self.serverMemorySocket.WriteCallback = self.memorySocket.SendToClient

        self.libssl.SSL_new.restype  = c_voidp
        self.libssl.SSL_new.argtypes = [ c_voidp ]
        print( "############## SSL_new")
        self.serverSSLSocket = self.libssl.SSL_new( self.context )
        if self.serverSSLSocket is None:
            raise OpenSSLError( "SSL_new returned NULL" )

        print( "############## SSL_set_bio")
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
        print( "############## SSL_new")
        self.clientSSLSocket = self.libssl.SSL_new( self.context )
        if self.clientSSLSocket is None:
            raise OpenSSLError( "SSL_new returned NULL" )

        print( "############## SSL_set_bio")
        self.libssl.SSL_set_bio.restype  = None
        self.libssl.SSL_set_bio.argtypes = [ c_voidp, c_voidp, c_voidp ]
        self.libssl.SSL_set_bio( self.clientSSLSocket, self.clientMemorySocket.bioObject, self.clientMemorySocket.bioObject )

    # def Recv( self ):
    #     self.log.debug( "Recv" )
    #     bufferSize  = 1024
    #     buffer      = bytearray( bufferSize )
    #     cBuffer     = ( c_uint8 * bufferSize ).from_buffer( buffer )
    #     # flags       = c_int32( 0 )
    #     # timeout     = c_int32( 0 )
        
    #     if self.clientSSLSocket != None:
    #         sslSocket = self.clientSSLSocket
    #     else:
    #         sslSocket = self.serverSSLSocket

    #     bytesReceived = self.nspr.PR_Recv( sslSocket, cBuffer, c_int32( bufferSize ), flags, timeout )
    #     self.log.info( "PR_Recv returned %d" % bytesReceived)

    #     if bytesReceived > 0:
    #         return bytearray( cBuffer[ : bytesReceived ] )
    #     #else:
    #     return b""

    def SSL_accept( self ):
        self.log.debug( "SSL_accept" )
        self.libssl.SSL_accept.restype  = c_int
        self.libssl.SSL_accept.argtypes = [ c_voidp ]

        result = self.libssl.SSL_accept( self.serverSSLSocket )
        self.VerifyResult( "SSL_accept", result )

      # For server side:
    def AcceptConnection( self, applicationData = None ):
        self.log.debug( "AcceptConnection" )
        self.acceptConnectionSucceeded = False

        self.InitializeSSLServerSocket()

        self.SSL_accept()
        # self.dataReceived = self.Recv()

        # if applicationData != None:
        #     self.Send( applicationData )

        # self.acceptConnectionSucceeded = True

    def SSL_connect( self ):
        self.log.debug( "SSL_connect" )
        self.libssl.SSL_connect.restype  = c_int
        self.libssl.SSL_connect.argtypes = [ c_voidp ]

        result = self.libssl.SSL_connect( self.clientSSLSocket )
        self.VerifyResult( "SSL_connect", result )

     # For client side
    def Connect( self, supportedNamedGroups = None ):
        self.log.debug( "Connect" )
        self.InitializeSSLClientSocket()

        self.SSL_connect()


#########################################################################


class OpenSSLTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(OpenSSLTester, self).__init__(*args, **kwargs)

    def setUp( self ):
        self.tlsServer = None
        self.tlsClient = None

    def tearDown( self ):
        pass

    def test_ClientAndServer( self ):
        hostName = "test_server.com"

        memorySocket = MemorySocket()

        self.tlsServer = OpenSSL( "server" )
        self.tlsClient = OpenSSL( "client" )

        self.tlsServer.InitServer( memorySocket )
        self.tlsClient.InitClient( memorySocket, hostName )

        serverThread = threading.Thread(target = self.tlsServer.AcceptConnection, args = [ b"Server->Client\x00" ] )
        serverThread.start()

        time.sleep( 0.1 )

        self.tlsClient.Connect()
        # self.tlsClient.Send( b"Client->Server\x00" ) 
        # self.tlsClient.dataReceived = self.tlsClient.Recv()

        serverThread.join()

        # # We're done, report transcript:
        # # pprint( memorySocket.tlsParser.transcript )

        # if config.LOG_LEVEL < logging.ERROR:
        #     for msg in memorySocket.tlsParser.transcript:
        #         memorySocket.tlsParser.PrintMsg( msg )
        #         # if tlsparser.IV_AND_KEY in msg.keys():
        #         #     pprint( msg[ tlsparser.IV_AND_KEY ])

        #     print( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        #     print( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        # # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )

if __name__ == '__main__':
    suite = unittest.TestSuite()
    suite.addTest( OpenSSLTester( 'test_ClientAndServer' ) )
    # suite.addTest( NSSTester( '' ) )
    
    runner=unittest.TextTestRunner()
    runner.run(suite)
