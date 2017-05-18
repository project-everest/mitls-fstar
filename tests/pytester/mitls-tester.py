import unittest
import logging
import os

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


SUCCESS             = 1
NULL_BYTE           = b"\0"
TLS_VERSION_1_3     = b"1.3" + NULL_BYTE
MITLS_SO_PATH       = "../../../everest/mitls-fstar/src/tls/libmitls.so"
SERVER_CERT_PATH    = "certs/test_server.crt" 
SERVER_KEY_PATH     = "certs/test_server.key"

class MITLSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

#Used by client to send to server:
def SendToServer( ctx, buffer, bufferSize ):
    print( "SendToServer" )
    return bufferSize

#Used by server to read from client:
def ReadFromClient( ctx, buffer, bufferSize ):
    print( "ReadFromClient" )
    return 0

#Used by server to send to client:
def SendToClient( ctx, buffer, bufferSize ):
    print( "SendToClient" )
    return bufferSize

#Used by client to read from server:
def ReadFromServer( ctx, buffer, bufferSize  ):
    print( "ReadFromServer" )
    return 0

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

    def VerifyResult( self, result, expectedValue = SUCCESS ):
        if result != expectedValue:
            logMsg = "Returned %d, instead of %d" % ( result, expectedValue )
            self.log.error( logMsg )
            raise MITLSError( logMsg )

    def FFI_mitls_init( self ):
        self.log.debug( "FFI_mitls_init" )
        
        self.miTLS.FFI_mitls_init.restype = c_int
        result = self.miTLS.FFI_mitls_init()
        self.VerifyResult( result )
        
        return result

    def FFI_mitls_thread_register( self ):
        self.log.debug( "FFI_mitls_thread_register" )
        
        self.miTLS.FFI_mitls_thread_register.restype = c_int
        result = self.miTLS.FFI_mitls_thread_register()
        self.VerifyResult( result )
        
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
        self.VerifyResult( ret )

        return mitls_state

    def MITLS_configure_cert_chain_file( self, filePath ):
        self.log.debug( "MITLS_configure_cert_chain_file" )
        self.miTLS.FFI_mitls_configure_cert_chain_file.restype = c_int

        serverCertPath = c_char_p( bytes( filePath, "ascii" ) + NULL_BYTE )
        ret            = self.miTLS.FFI_mitls_configure_cert_chain_file( self.mitls_state, serverCertPath )
        self.VerifyResult( ret )

    def MITLS_configure_private_key_file( self, filePath ):
        self.log.debug( "MITLS_configure_private_key_file" )
        self.miTLS.FFI_mitls_configure_cert_chain_file.restype = c_int

        serverCertPath = c_char_p( bytes( filePath, "ascii" ) + NULL_BYTE )
        ret            = self.miTLS.FFI_mitls_configure_private_key_file( self.mitls_state, serverCertPath )
        self.VerifyResult( ret )

    def InitServer( self ):
        self.log.debug( "InitServer" )

        self.mitls_state = self.MITLS_Configure()
        self.MITLS_configure_cert_chain_file( SERVER_CERT_PATH )
        self.MITLS_configure_private_key_file( SERVER_KEY_PATH )

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

    # For client side
    def Connect( self ):
        self.log.debug( "Connect" )
        outmsg              = c_char_p()
        errmsg              = c_char_p() 
        FFI_mitls_callbacks = self.GetClientCallbacks()

        self.miTLS.FFI_mitls_connect.restype = c_int
        self.miTLS.FFI_mitls_connect.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp ]

        print( "self.mitls_state = %s" % self.mitls_state )
        ret = self.miTLS.FFI_mitls_connect( FFI_mitls_callbacks,
                                            self.mitls_state,
                                            byref( outmsg ),
                                            byref( errmsg ) )
        self.PrintMsgIfNotNull( outmsg, errmsg )
        self.VerifyResult( ret )

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

    # def testMultiple( self ):
    #     for i in range( 5 ):
    #         mitls = MITLS( "test-%d" % i )
    #         mitls.Cleanup()

    def testClientAndServer( self ):
        hostName = "test_server.com"

        self.tlsClient = MITLS( "client" )
        self.tlsClient.InitClient( hostName )
        self.tlsClient.Connect()

if __name__ == '__main__':
	unittest.main()



