import unittest
import logging
import os
import sys
import time
import threading
import struct
import pprint

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


from tlsparser import MemorySocket

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

    def test_MITLS_ClientAndServer( self ):
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



