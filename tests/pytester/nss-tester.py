import logging
import unittest
import os
import time

from tlsparser import MemorySocket
from pr_wrapper import PRWrapper, PRDLL

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

# SSL options, see ssl.h:
SSL_SECURITY                = 1
SSL_HANDSHAKE_AS_CLIENT     = 5
SSL_NO_LOCKS                = 17   
SSL_ENABLE_SESSION_TICKETS  = 18
SSL_ENABLE_FALSE_START      = 22 
SSL_ENABLE_OCSP_STAPLING    = 24

SECWOULDBLOCK           = -2
SECFAILURE              = -1
SECSUCCESS              = 0

globalNSPR            = PRDLL()

class NSSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

#see ssl.h for function signature:
# typedef SECStatus(PR_CALLBACK *SSLAuthCertificate)(void *arg, PRFileDesc *fd,
#                                                    PRBool checkSig,
#                                                    PRBool isServer); 
def AuthenticateCertificateCallback( arg, fd, checkSig, isServer ):
    print( "####################### AuthenticateCertificateCallback" )
    return SECSUCCESS

#see ssl.h for function signature:
# typedef SECStatus(PR_CALLBACK *SSLGetClientAuthData)(void *arg,
#                                                      PRFileDesc *fd,
#                                                      CERTDistNames *caNames,
#                                                      CERTCertificate **pRetCert,  /*return */
#                                                      SECKEYPrivateKey **pRetKey); /* return */
def ClientAuthenticationCallback( arg, fd, caNames, pRetCert, pRetKey):
    print( "####################### ClientAuthenticationCallback" )
    return SECSUCCESS    

#see ssl.h for function signature:
# typedef void(PR_CALLBACK *SSLHandshakeCallback)(PRFileDesc *fd,
#                                                 void *client_data);
def PostHandshakeCallback( fd, client_data ):
    print( "####################### PostHandshakeCallback" )
    return SECSUCCESS    


class NSS():
    def __init__( self, name = "", 
                    libssl3Path = "/home/user/dev/nss-3.30.2/nss/lib/ssl/Linux4.8_x86_64_cc_glibc_PTH_64_DBG.OBJ/libssl3.so",
                    libnss3Path = "/home/user/dev/nss-3.30.2/dist/Linux4.8_x86_64_cc_glibc_PTH_64_DBG.OBJ/lib/libnss3.so"  ):
        self.SetupLogger( name )
        self.log.info( "Initilizaed with libssl3Path = %s" % os.path.abspath( libssl3Path ) )
        self.log.info( "Initilizaed with libnss3Path = %s" % os.path.abspath( libnss3Path ) )
        self.log.warning( "Make sure $LD_LIBRARY_PATH points to %s" % os.path.dirname( libnss3Path ) )
        
        self.libssl3 = CDLL( libssl3Path ) 
        self.libnss3 = CDLL( libnss3Path )
        self.cutils  = CDLL( "cutils/cutils.so" )
        self.cutils.getAddress.restype = c_voidp

        self.nspr   = globalNSPR.nspr

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

    def NSS_NoDB_Init( self ):
        self.libnss3.NSS_NoDB_Init.restype = c_int32
        self.libnss3.NSS_NoDB_Init.argtypes = [ c_voidp ]

        result = self.libnss3.NSS_NoDB_Init( c_voidp( None ) )
        self.VerifyResult( "NSS_NoDB_Init", result )

    def InitClient( self, hostName ):
        self.log.debug( "InitClient" )

        self.versionRange = self.SSL_VersionRangeGetSupported( SSL_VARIANT_STREAM )
        self.NSS_NoDB_Init()
        # Seel also "NSS_Init" if we have a certificate DB

    def SSL_ImportFD( self, tcpSocket ):
        self.libssl3.SSL_ImportFD.restype = c_voidp

        NO_MODEL = c_voidp( None ) 
        newSocket = self.libssl3.SSL_ImportFD( NO_MODEL, c_voidp( tcpSocket ) )
        if newSocket == 0:
            raise NSSError( "SSL_ImportFD returned NULL" )

        return newSocket

    def SSL_OptionSet( self, sslSocket, option, value ):
        self.libssl3.SSL_OptionSet.restype  = c_int32

        result = self.libssl3.SSL_OptionSet( c_voidp( sslSocket ), c_int32( option ), c_int32( value ) )
        self.VerifyResult( "SSL_OptionSet", result )

    def ForceTLS_13( self ):
        TLS_13 = 0x304

        enabledVersions      = ( c_int16 * 2 )()
        enabledVersions[ 0 ] = TLS_13 #min allowed version
        enabledVersions[ 1 ] = TLS_13 #max allowed version

        self.libssl3.SSL_VersionRangeSet.restype = c_int32
        result = self.libssl3.SSL_VersionRangeSet( self.clientSSLSocket, enabledVersions )
        self.VerifyResult( "SSL_VersionRangeSet", result )


    def InitializeSSLClientSocket( self ):
        self.memorySocket = MemorySocket()
        
        self.clientMemorySocket               = PRWrapper()
        self.clientMemorySocket.ReadCallback  = self.memorySocket.ReadFromServer
        self.clientMemorySocket.WriteCallback = self.memorySocket.SendToServer
        
        self.clientSSLSocket = self.SSL_ImportFD( self.clientMemorySocket.prFileDesc )

    def SSL_AuthCertificateHook( self ):
        AUTH_CERT_CALLBACK           = CFUNCTYPE( c_int32, c_voidp, c_int32, c_int32 ) 
        self.authCertCallback        = AUTH_CERT_CALLBACK( AuthenticateCertificateCallback )

        self.libssl3.SSL_AuthCertificateHook.restype    = c_int32
        self.libssl3.SSL_AuthCertificateHook.argtypes   = [ c_voidp, c_voidp, c_voidp ]

        NO_CONTEXT = c_voidp( None )
        result = self.libssl3.SSL_AuthCertificateHook(  self.clientSSLSocket, 
                                                        self.cutils.getAddress( self.authCertCallback ),
                                                        NO_CONTEXT )
        self.VerifyResult( "SSL_AuthCertificateHook", result )

    def SSL_GetClientAuthDataHook( self ):
        CLIENT_AUTH_CALLBACK         = CFUNCTYPE( c_int32, c_voidp, c_voidp, c_voidp, c_voidp, c_voidp ) 
        self.clientAuthCallback      = CLIENT_AUTH_CALLBACK( ClientAuthenticationCallback )

        self.libssl3.SSL_GetClientAuthDataHook.restype    = c_int32
        self.libssl3.SSL_GetClientAuthDataHook.argtypes   = [ c_voidp, c_voidp, c_voidp ]

        NO_CONTEXT = c_voidp( None )
        result = self.libssl3.SSL_GetClientAuthDataHook(    self.clientSSLSocket, 
                                                            self.cutils.getAddress( self.clientAuthCallback ),
                                                            NO_CONTEXT )
        self.VerifyResult( "SSL_GetClientAuthDataHook", result )

    def SSL_HandshakeCallback( self ):
        POST_HANDSHAKE_CALLBACK      = CFUNCTYPE( None, c_voidp, c_voidp ) 
        self.postHandshakeCallback   = POST_HANDSHAKE_CALLBACK( PostHandshakeCallback )

        self.libssl3.SSL_GetClientAuthDataHook.restype    = c_int32
        self.libssl3.SSL_GetClientAuthDataHook.argtypes   = [ c_voidp, c_voidp, c_voidp ]

        NO_CONTEXT = c_voidp( None )
        result = self.libssl3.SSL_HandshakeCallback(    self.clientSSLSocket, 
                                                        self.cutils.getAddress( self.postHandshakeCallback ),
                                                        NO_CONTEXT )
        self.VerifyResult( "SSL_HandshakeCallback", result )

    def CallSSLConnect( self ):
        timeout = c_int32( 0 )
        addr    = c_voidp( None )
        result = self.nspr.PR_Connect( self.clientSSLSocket, addr, timeout )
        self.VerifyResult( "PR_Connect", result )
        
    # For client side
    def Connect( self ):
        self.log.debug( "Connect" )
        self.InitializeSSLClientSocket()
        
        # skipping SSL_SetPKCS11PinArg
        self.SSL_OptionSet( self.clientSSLSocket, SSL_SECURITY,             True );
        self.SSL_OptionSet( self.clientSSLSocket, SSL_HANDSHAKE_AS_CLIENT,  True );
        # skipping SSL_CipherPrefSet
        self.ForceTLS_13()

        disableLocking              = False
        enableSessionTickets        = False
        enableFalseStart            = False
        enableCertStatus            = False # enable cert status (OCSP stapling).
        enableSignedCertTimestamps  = False
        self.SSL_OptionSet( self.clientSSLSocket, SSL_NO_LOCKS,                 disableLocking )
        self.SSL_OptionSet( self.clientSSLSocket, SSL_ENABLE_SESSION_TICKETS,   enableSessionTickets )
        self.SSL_OptionSet( self.clientSSLSocket, SSL_ENABLE_FALSE_START,       enableFalseStart )
        self.SSL_OptionSet( self.clientSSLSocket, SSL_ENABLE_OCSP_STAPLING,     enableCertStatus )
        self.SSL_OptionSet( self.clientSSLSocket, SSL_ENABLE_OCSP_STAPLING,     enableSignedCertTimestamps )
        # Other options:
        # SSL_ENABLE_EXTENDED_MASTER_SECRET
        # SSL_ENABLE_0RTT_DATA
        # SSL_REQUIRE_DH_NAMED_GROUPS
        
        # skipping SSL_NamedGroupConfig
        self.SSL_AuthCertificateHook()
        self.SSL_GetClientAuthDataHook()
        self.SSL_HandshakeCallback()
        # skipping SSL_SetURL
        self.CallSSLConnect()

    def Recv( self ):
        bufferSize  = 1024
        buffer      = bytearray( bufferSize )
        cBuffer     = ( c_uint8 * bufferSize ).from_buffer( buffer )
        flags       = c_int32( 0 )
        timeout     = c_int32( 0 )
        
        result = self.nspr.PR_Recv( self.clientSSLSocket, cBuffer, c_int32( bufferSize ), flags, timeout )
        self.log.info( "PR_Recv returned %d" % result)


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
        buf = self.tlsClient.Recv()

        # time.sleep(3)

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