import unittest
import logging
import os

from ctypes import cdll, CDLL, c_long, c_int, c_float, c_double, c_char_p, create_string_buffer, byref, c_voidp, c_uint8, c_uint32


SUCCESS             = 1
NULL_BYTE           = b"\0"
TLS_VERSION_1_3     = b"1.3" + NULL_BYTE
MITLS_SO_PATH       = "../../../everest/mitls-fstar/src/tls/libmitls.so"
SERVER_CERT_PATH    = "certs/test_server.crt" 
SERVER_KEY_PATH     = "certs/test_server.key"

class MITLSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

class MITLS():
    def __init__( self, sharedObjectPath = MITLS_SO_PATH  ):
        self.SetupLogger()
        self.log.info( "Initilizaed with sharedObjectPath = %s" % os.path.abspath( sharedObjectPath ) )
        
        self.miTLS = CDLL( sharedObjectPath ) 

        self.FFI_mitls_init() 

    def SetupLogger( self ):
        self.log = logging.getLogger( 'MITLS' )
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
            raise MITLSTesterError( logMsg )

    def FFI_mitls_init( self ):
        self.log.debug( "FFI_mitls_init" )
        
        self.miTLS.FFI_mitls_init.restype = c_int
        result = self.miTLS.FFI_mitls_init()
        self.VerifyResult( result )
        
        return result

    def PrintMsgIfNotNull( self, outmsg, errmsg ):
        if outmsg.value != None:
            self.log.error( 'outmsg = "%s"' % outmsg.value )
            self.miTLS.FFI_mitls_free_msg( outmsg )

        if errmsg.value != None:
            self.log.error( 'errmsg = "%s"' % errmsg.value )
            self.miTLS.FFI_mitls_free_msg( errmsg )

    def MITLS_Configure( self ):
        self.log.debug( "MITLS_Configure" )
        mitls_state = c_voidp()
        tls_version = c_char_p( TLS_VERSION_1_3 )
        host_name   = c_char_p( NULL_BYTE )         #server doesn't need host name
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

class MITLSTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(MITLSTester, self).__init__(*args, **kwargs)

    def setUp(self):
        pass

    def tearDown(self):
        pass

    def testInitMITLS( self ):
        self.tlsServer = MITLS()
        self.tlsClient = MITLS()

    def testSetupServer( self ):
        self.tlsServer = MITLS()
        self.tlsServer.InitServer()

    def testClientAndServer( self ):
        pass

if __name__ == '__main__':
	unittest.main()



