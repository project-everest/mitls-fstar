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

    def SSL_CTX_set_cipher_list( self, supportedCipherSuites ):
        self.libssl.SSL_CTX_set_cipher_list.restype = c_int
        self.libssl.SSL_CTX_set_cipher_list.argtypes = [ c_voidp, c_voidp ]
        
        cipherSuitesString = ":".join( supportedCipherSuites )
        cipherSuitesString = cipherSuitesString.replace( "_", "-" )
        cipherSuitesString = cipherSuitesString.replace( "TLS", "TLS13" )
        print( "############# self.context = %s; cipherSuitesString = %s" % ( self.context, cipherSuitesString ))
        ret = self.libssl.SSL_CTX_set_cipher_list( self.context, CString( cipherSuitesString ) )
        self.VerifyResult( "SSL_CTX_set_cipher_list", ret )


    def InitServer( self, 
                    memorySocket,
                    supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                    supportedSignatureAlgorithms    = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS,
                    supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS  ):
        self.log.debug( "InitServer" )

        self.context = self.CreateServerContext()
        self.ConfigureTLS1_3()
        self.SetCertificateAndPrivateKey()
        self.SSL_CTX_set_cipher_list( supportedCipherSuites )
        # self.ConfigureSignatureAlgorithms()

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
        # self.ConfigureSignatureAlgorithms()

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
        self.dataReceived = self.Recv()

        if applicationData != None:
            self.Send( applicationData )

        self.acceptConnectionSucceeded = True

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
        self.tlsClient.Send( b"Client->Server\x00" ) 
        # time.sleep( 0.1 )
        self.tlsClient.dataReceived = self.tlsClient.Recv()

        serverThread.join()

        # We're done, report transcript:
        # pprint( memorySocket.tlsParser.transcript )

        if config.LOG_LEVEL < logging.ERROR:
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )
                # if tlsparser.IV_AND_KEY in msg.keys():
                #     pprint( msg[ tlsparser.IV_AND_KEY ])

        print( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        print( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        # # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )


    def StartServerThread(  self, 
                            supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                            supportedSignatureAlgorithms    = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS,
                            supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS,
                            applicationData                 = None ):
        self.tlsServer = OpenSSL( "server" )
        self.tlsServer.InitServer(  memorySocket,
                                    supportedCipherSuites, 
                                    supportedSignatureAlgorithms, 
                                    supportedNamedGroups )
        
        serverThread   = threading.Thread(target = self.tlsServer.AcceptConnection, args = [ applicationData ] )
        serverThread.start()

        return serverThread

    def RunSingleTest(  self, 
                        supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                        supportedSignatureAlgorithms    = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS,
                        supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS,
                        msgManipulators                 = [] ):

        memorySocket.FlushBuffers()
        memorySocket.tlsParser = tlsparser.TLSParser()
        memorySocket.tlsParser.SetMsgManipulators( msgManipulators )
        serverThread = self.StartServerThread(  supportedCipherSuites,
                                                supportedSignatureAlgorithms,
                                                supportedNamedGroups,
                                                DATA_SERVER_TO_CLIENT )

        self.tlsClient = OpenSSL( "client" )
        self.tlsClient.InitClient(  memorySocket,
                                    "test_server.com", 
                                    supportedCipherSuites,
                                    supportedSignatureAlgorithms,
                                    supportedNamedGroups )
        self.tlsClient.Connect()
        self.tlsClient.Send( DATA_CLIENT_TO_SERVER )            
        self.tlsClient.dataReceived = self.tlsClient.Recv()

        serverThread.join()
        if self.tlsServer.acceptConnectionSucceeded == False:
            raise Exception( "Server failed to connect" )

        if self.tlsClient.dataReceived != DATA_SERVER_TO_CLIENT:
            raise Exception( "self.tlsClient.dataReceived = %s, instead of expected %s" % ( self.tlsClient.dataReceived, DATA_SERVER_TO_CLIENT ) )           

        if self.tlsServer.dataReceived != DATA_CLIENT_TO_SERVER:
            raise Exception( "self.tlsServer.dataReceived = %s, instead of expected %s" % ( self.tlsServer.dataReceived, DATA_CLIENT_TO_SERVER ) )
            
        # self.log.debug( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        # self.log.debug( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

    def test_parameters_matrix( self ):
        sys.stderr.write( "Running test_parameters_matrix\n" )

        with open( "parameters_matrix_OPENSSL_OPENSSL.csv", "w" ) as logFile:
            outputSinks = [ sys.stderr, logFile ]
            WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s %-15s%-6s\n" % ("CipherSuite,", "SignatureAlgorithm,", "NamedGroup,", "PassFail,", "Time (seconds)") )

            algorithm = 'ECDSA+SHA256'
            group     = "X25519"
            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                # for algorithm in SUPPORTED_SIGNATURE_ALGORITHMS:
                #     for group in SUPPORTED_NAMED_GROUPS:
                WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s " % ( cipherSuite+",", algorithm+",", group+"," ) )

                memorySocket.tlsParser.DeleteLeakedKeys()
                try:
                    startTime = time.time()
                    self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                                        supportedSignatureAlgorithms = [ algorithm ],
                                        supportedNamedGroups         = [ group ] )
                    WriteToMultipleSinks( outputSinks, "%-15s" % ("OK,") )
                except Exception as err: 
                    print( traceback.format_tb( err.__traceback__ ) )
                    WriteToMultipleSinks( outputSinks, "%-15s" % "FAILED," )
                    raise
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
    # suite.addTest( OpenSSLTester( 'test_ClientAndServer' ) )
    suite.addTest( OpenSSLTester( 'test_parameters_matrix' ) )
    # suite.addTest( NSSTester( '' ) )
    
    runner=unittest.TextTestRunner()
    
    if args.supress_output:
        devNull = open( "/dev/null", "wb" )
        with stdout_redirector( devNull ):
            runner.run(suite)
    else:
        runner.run(suite)

