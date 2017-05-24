import logging
import unittest
import os

from tlsparser import MemorySocket
from pr_wrapper import PRWrapper

from ctypes import  CDLL,           \
                    c_long,         \
                    c_int,          \
                    c_float,        \
                    c_double,       \
                    c_char_p,       \
                    create_string_buffer, \
                    byref,          \
                    c_voidp,        \
                    c_uint8,        \
                    c_uint32,        \
                    c_int16,           \
                    c_int32,           \
                    CFUNCTYPE,          \
                    POINTER    



SSL_VARIANT_STREAM      = 0
SSL_VARIANT_DATAGRAM    = 1

SECWOULDBLOCK           = -2
SECFAILURE              = -1
SECSUCCESS              = 0

class NSSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

class NSS():
    def __init__( self, name = "", sharedObjectPath = "/home/user/dev/nss-3.30.2/nss/lib/ssl/Linux4.8_x86_64_cc_glibc_PTH_64_DBG.OBJ/libssl3.so"  ):
        self.SetupLogger( name )
        self.log.info( "Initilizaed with sharedObjectPath = %s" % os.path.abspath( sharedObjectPath ) )
        
        self.libssl3          = CDLL( sharedObjectPath ) 

    def SetupLogger( self, name ):
        self.log = logging.getLogger( 'NSS-%s' % name )
        self.log.setLevel(logging.DEBUG)

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel(logging.DEBUG)
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def Cleanup( self ):
        self.log.debug( "Cleanup" )

    def VerifyResult( self, functionName, result, expectedValue = SECSUCCESS ):
        if result != expectedValue:
            logMsg = "%s returned %d, instead of %d" % ( functionName, result, expectedValue )
            self.log.error( logMsg )
            raise NSSError( logMsg )

    def SSL_VersionRangeGetSupported( self, sslVariant ):
        self.libssl3.SSL_VersionRangeGetSupported.restype  = c_int32
        self.libssl3.SSL_VersionRangeGetSupported.argtypes = [ c_int32, c_voidp ]

        enabledVersions = ( c_int16 * 2 )()
        result          = self.libssl3.SSL_VersionRangeGetSupported( c_int32( sslVariant ), enabledVersions )
        self.VerifyResult( "SSL_VersionRangeGetSupported", result )

        self.log.debug( "Min SSL version: 0x%x, Max SSL version: 0x%x" % (enabledVersions[ 0 ], enabledVersions[ 1 ] ))


    def InitClient( self, hostName ):
        self.log.debug( "InitClient" )

        self.versionRange = self.SSL_VersionRangeGetSupported( SSL_VARIANT_STREAM )

    def SSL_ImportFD( self, tcpSocket ):
        self.libssl3.SSL_ImportFD.restype = c_voidp

        NO_MODEL = c_voidp( None ) 
        newSocket = self.libssl3.SSL_ImportFD( NO_MODEL, c_voidp( tcpSocket ) )
        if newSocket == 0:
            raise NSSError( "SSL_ImportFD returned NULL" )

        return newSocket

    # For client side
    def Connect( self ):
        self.log.debug( "Connect" )
        self.memorySocket = MemorySocket()
        
        self.clientMemorySocket               = PRWrapper()
        self.clientMemorySocket.ReadCallback  = self.memorySocket.ReadFromServer
        self.clientMemorySocket.WriteCallback = self.memorySocket.SendToServer
        
        self.clientSSLSocket = self.SSL_ImportFD( self.clientMemorySocket.prFileDesc )
        print( "self.clientSSLSocket = %s" % self.clientSSLSocket)

class NSSTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(NSSTester, self).__init__(*args, **kwargs)

    def setUp(self):
        self.tlsServer = None
        self.tlsClient = None

    def tearDown(self):
        pass
        # if self.tlsServer is not None:
        #     self.tlsServer.Cleanup()
        # if self.tlsClient is not None:
        #     self.tlsClient.Cleanup()

    # def testInitMITLS( self ):
    #     self.tlsServer = NSSTester( "server" )
    #     self.tlsClient = NSSTester( "client" )

    # def testSetupServer( self ):
    #     self.tlsServer = NSSTester( "server" )
    #     self.tlsServer.InitServer()

    def testSetupClient( self ):
        hostName = "test_server.com"

        self.tlsClient = NSS( "client" )
        self.tlsClient.InitClient( hostName )
        self.tlsClient.Connect()

    # def test_MITLS_ClientAndServer( self ):
    #     hostName = "test_server.com"

    #     self.tlsServer = NSSTester( "server" )
    #     self.tlsServer.InitServer()

    #     # self.tlsServer.AcceptConnection()
    #     serverThread = threading.Thread(target = self.tlsServer.AcceptConnection )
    #     serverThread.start()

    #     self.tlsClient = MITLS( "client" )
    #     self.tlsClient.InitClient( hostName )
    #     self.tlsClient.Connect()
    #     print( "########################")

    #     serverThread.join()
if __name__ == '__main__':
	unittest.main()