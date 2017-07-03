import logging
import unittest
import os
import time
import threading
import sys
import glob

import tlsparser
import nss
import cutils
import config

from pprint import pprint
from tlsparser import MemorySocket, TLSParser, FileSocket
from pr_wrapper import PRWrapper, PRDLL


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
                    c_uint32,        \
                    c_int16,           \
                    c_int32,           \
                    c_uint64,           \
                    CFUNCTYPE,          \
                    POINTER    



SERVER_CERT_PATH            = "/home/user/dev/git/everest/mitls-fstar/data/server-ecdsa.crt" 
SERVER_KEY_PATH             = "/home/user/dev/git/everest/mitls-fstar/data/server-ecdsa.key"

KEY_DATABASE_PATH           = "./certificates/db"
CERTIFICATE_NAME            = "ecdsa.cert.mitls.org - Organization"
DATABASE_PASSWORD           = "12345678"

NULL_BYTE                   = b"\0"

SSL_VARIANT_STREAM          = 0
SSL_VARIANT_DATAGRAM        = 1

# SSL options, see ssl.h:
SSL_SECURITY                = 1
SSL_HANDSHAKE_AS_CLIENT     = 5
SSL_ROLLBACK_DETECTION      = 14
SSL_NO_LOCKS                = 17   
SSL_ENABLE_SESSION_TICKETS  = 18
SSL_ENABLE_DEFLATE          = 19
SSL_ENABLE_FALSE_START      = 22 
SSL_ENABLE_OCSP_STAPLING    = 24

SECWOULDBLOCK           = -2
SECFAILURE              = -1
SECSUCCESS              = 0



globalNSPR              = PRDLL()
globalCUtils            = cutils.GetObject()

class NSSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

def CString( pythonString ):
    NULL_BYTE = b"\0"
    return c_char_p( bytes( pythonString, "ascii" ) + NULL_BYTE )

def CStringAsVoidP( pythonString ):
    NULL_BYTE = b"\0"
    buffer = ( c_uint8 * ( len( pythonString ) + 1 ) ).from_buffer( bytearray( pythonString, "ascii" ) + NULL_BYTE )
    return buffer

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

# see lib/pk11wrap/secmodt.h: 
# typedef char *(PR_CALLBACK *PK11PasswordFunc)(PK11SlotInfo *slot, PRBool retry, void *arg);
DATABASE_PASSWORD_C = CStringAsVoidP( DATABASE_PASSWORD )
def GetPasswordCallback( slot, retry, arg ):
    print( "####################### GetPasswordCallback" )
    duplicatedPassword = globalCUtils.duplicateString( DATABASE_PASSWORD_C, len( DATABASE_PASSWORD_C ) )
    return duplicatedPassword

class  SSLAuthType:
    ssl_auth_null           = 0 #
    ssl_auth_rsa_decrypt    = 1 #/* static RSA */
    ssl_auth_dsa            = 2 #
    ssl_auth_kea            = 3 #/* unused */
    ssl_auth_ecdsa          = 4 #
    ssl_auth_ecdh_rsa       = 5 #  /* ECDH cert with an RSA signature */
    ssl_auth_ecdh_ecdsa     = 6 #/* ECDH cert with an ECDSA signature */
    ssl_auth_rsa_sign       = 7 #  /* RSA PKCS#1.5 signing */
    ssl_auth_rsa_pss        = 8 #
    ssl_auth_psk            = 9 #
    ssl_auth_tls13_any      = 10     

class NSS():
    def __init__( self, name = "" ):
        self.SetupLogger( name )
        self.log.warning( "Make sure $LD_LIBRARY_PATH points to %s" % os.path.dirname( nss.NSS_PATH ) )
        
        self.libssl3    = nss.GetObject( "ssl3" )
        self.libnss3    = nss.GetObject( "nss3" )
        self.cutils     = globalCUtils

        self.nspr   = globalNSPR.nspr

        self.clientSSLSocket = None
        self.serverSSLSocket = None 

    def SetupLogger( self, name ):
        self.log = logging.getLogger( 'NSS-%s' % name )
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL )
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

    def SSL_ConfigServerSessionIDCache( self ):
        sessionIDCacheDirectory     = "./session_id_cache"
        maxNumEntries               = c_int32( 1024 )
        timeout                     = c_int32( 0 )
        sessionIDCacheDirectory_c   = CString( sessionIDCacheDirectory )

        if not os.path.exists( sessionIDCacheDirectory ):
            os.makedirs( sessionIDCacheDirectory )

        self.libssl3.SSL_ConfigServerSessionIDCache.restype  = c_int32
        self.libssl3.SSL_ConfigServerSessionIDCache.argtypes = [ c_int32, c_int32, c_int32, c_char_p ]
        result = self.libssl3.SSL_ConfigServerSessionIDCache(   maxNumEntries, 
                                                                timeout, 
                                                                timeout, 
                                                                sessionIDCacheDirectory_c )
        self.VerifyResult( "SSL_ConfigServerSessionIDCache", result )

    def PK11_SetPasswordFunc( self ):
        GET_PASSWORD_CALLBACK        = CFUNCTYPE( c_voidp, c_voidp, c_int32, c_voidp ) 
        self.getPasswordCallback     = GET_PASSWORD_CALLBACK( GetPasswordCallback )

        self.libnss3.PK11_SetPasswordFunc.restype    = None
        self.libnss3.PK11_SetPasswordFunc.argtypes   = [ c_voidp ]

        result = self.libnss3.PK11_SetPasswordFunc( self.cutils.getAddress( self.getPasswordCallback ) )

    def NSS_Initialize( self, dataBasePath ):
        SECMOD_DB           = "secmod.db" 
        NSS_INIT_READONLY   = 0x1
        certPrefix          = c_char_p( None )
        keyPrefix           = c_char_p( None )
        secmodName          = c_char_p( bytes( SECMOD_DB, "ascii" ) + NULL_BYTE )
        flags               = c_int32( NSS_INIT_READONLY )

        self.libnss3.NSS_Initialize.restype  = c_int32
        self.libnss3.NSS_Initialize.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp, c_uint32 ]
        result = self.libnss3.NSS_Initialize(   CString( dataBasePath ), 
                                                certPrefix, 
                                                keyPrefix, 
                                                CString( SECMOD_DB ), 
                                                NSS_INIT_READONLY )
        self.VerifyResult( "NSS_Initialize", result )

    def InitServer( self, memorySocket ):
        self.log.debug( "InitServer" )

        self.SSL_ConfigServerSessionIDCache()
        self.PK11_SetPasswordFunc()
        self.NSS_Initialize( KEY_DATABASE_PATH )

        self.memorySocket = memorySocket
        
    def InitClient( self, memorySocket, hostName ):
        self.log.debug( "InitClient" )

        self.versionRange = self.SSL_VersionRangeGetSupported( SSL_VARIANT_STREAM )
        self.NSS_NoDB_Init()
        # Seel also "NSS_Init" if we have a certificate DB

        self.memorySocket = memorySocket

    def SSL_ImportFD( self, tcpSocket ):
        self.log.debug( "SSL_ImportFD" )
        self.libssl3.SSL_ImportFD.restype = c_voidp

        NO_MODEL = c_voidp( None ) 
        # print( "###1")
        newSocket = self.libssl3.SSL_ImportFD( NO_MODEL, c_voidp( tcpSocket ) )
        # print( "###2")
        if newSocket == 0:
            raise NSSError( "SSL_ImportFD returned NULL" )

        return newSocket

    def SSL_OptionSet( self, sslSocket, option, value ):
        self.log.debug( "SSL_OptionSet; option = %d, value = %s" % ( option, value ) )
        self.libssl3.SSL_OptionSet.restype  = c_int32
        self.libssl3.SSL_OptionSet.argtypes = [ c_voidp, c_int32, c_int32 ]

        result = self.libssl3.SSL_OptionSet( c_voidp( sslSocket ), c_int32( option ), c_int32( value ) )
        self.VerifyResult( "SSL_OptionSet", result )

    def ForceTLS_13( self, sslSocket ):
        self.log.debug( "ForceTLS_13" )
        TLS_13 = 0x304

        enabledVersions      = ( c_int16 * 2 )()
        enabledVersions[ 0 ] = TLS_13 #min allowed version
        enabledVersions[ 1 ] = TLS_13 #max allowed version

        self.libssl3.SSL_VersionRangeSet.restype  = c_int32
        self.libssl3.SSL_VersionRangeSet.argtypes = [ c_voidp, c_voidp ]

        result = self.libssl3.SSL_VersionRangeSet( sslSocket, enabledVersions )
        self.VerifyResult( "SSL_VersionRangeSet", result )

    def InitializeSSLClientSocket( self ):
        # self.memorySocket = MemorySocket()
        
        self.clientMemorySocket               = PRWrapper()
        self.clientMemorySocket.ReadCallback  = self.memorySocket.ReadFromServer
        self.clientMemorySocket.WriteCallback = self.memorySocket.SendToServer
        
        self.clientSSLSocket = self.SSL_ImportFD( self.clientMemorySocket.prFileDesc )

    def InitializeSSLServerSocket( self ):
        self.log.debug( "InitializeSSLServerSocket" )
        # self.memorySocket = MemorySocket()
        
        self.serverMemorySocket               = PRWrapper()
        self.serverMemorySocket.ReadCallback  = self.memorySocket.ReadFromClient
        self.serverMemorySocket.WriteCallback = self.memorySocket.SendToClient
        
        self.serverSSLSocket = self.SSL_ImportFD( self.serverMemorySocket.prFileDesc )

    def SSL_AuthCertificateHook( self ):
        AUTH_CERT_CALLBACK           = CFUNCTYPE( c_int32, c_voidp, c_voidp, c_int32, c_int32 ) 
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

        self.libssl3.SSL_HandshakeCallback.restype    = c_int32
        self.libssl3.SSL_HandshakeCallback.argtypes   = [ c_voidp, c_voidp, c_voidp ]

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
        
    def PK11_FindCertFromNickname( self, certificateName ):
        NULL                = 0
        PW_PLAINTEXT        = 2 # see secutil.h
        certificateName_c   = CString( certificateName )
        passwordSturct      = c_voidp( None ) 

        self.libnss3.PK11_FindCertFromNickname.restype  = c_voidp
        self.libnss3.PK11_FindCertFromNickname.argtypes = [ c_voidp, c_voidp ]

        certificate = self.libnss3.PK11_FindCertFromNickname( certificateName_c, passwordSturct )
        if certificate is None:
            raise NSSError( "PK11_FindCertFromNickname returned NULL")
        return certificate

    def PK11_FindKeyByAnyCert( self, certificate, databasePassword ):
        PW_PLAINTEXT        = 2 # see secutil.h
        databasePassword_c  = CString( databasePassword )  

        self.libnss3.PK11_FindKeyByAnyCert.restype  = c_voidp
        self.libnss3.PK11_FindKeyByAnyCert.argtypes = [ c_voidp, c_voidp ]

        passwordSturct      = ( c_uint64 * 2 )()
        passwordSturct[ 0 ] = PW_PLAINTEXT
        passwordSturct[ 1 ] = self.cutils.getAddress( databasePassword_c )

        privateKey = self.libnss3.PK11_FindKeyByAnyCert( certificate, passwordSturct )
        if privateKey is None:
            raise NSSError( "PK11_FindKeyByAnyCert returned NULL")
        
        return privateKey

    def SSL_ConfigServerCert( self ):
        # SIZE_OF_OSCP_DATA = 32
        SIZE_OF_OSCP_DATA = 16
        # raise NSSError( "shouldnt be here yet" )
        certificate = self.PK11_FindCertFromNickname( CERTIFICATE_NAME )
        privateKey  = self.PK11_FindKeyByAnyCert( c_voidp( certificate ), DATABASE_PASSWORD )

        print( "certificate = %s, privateKey = %s" % (certificate, privateKey ))
        ocspData = ( c_voidp * 4 )()
        ocspData[ 0 ] = SSLAuthType.ssl_auth_null   # SSLAuthType authType;
        ocspData[ 1 ] = None                        # CERTCertificateList* certChain
        ocspData[ 2 ] = None                        # SECItemArray* stapledOCSPResponses
        ocspData[ 3 ] = None                        # SECItem* signedCertTimestamps

        self.libssl3.SSL_ConfigServerCert.restype  = c_int32
        self.libssl3.SSL_ConfigServerCert.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp, c_uint32 ]
        result = self.libssl3.SSL_ConfigServerCert( self.serverSSLSocket, 
                                                    certificate,
                                                    privateKey,
                                                    ocspData,
                                                    c_uint32( sizeof( ocspData ) ) )
        self.VerifyResult( "SSL_ConfigServerCert", result )

    def SSL_ResetHandshake( self ):
        self.libssl3.SSL_ResetHandshake.restype  = c_int32
        self.libssl3.SSL_ResetHandshake.argtypes = [ c_voidp, c_int32 ]

        AS_SERVER = c_int32( 1 )

        result = self.libssl3.SSL_ResetHandshake( self.serverSSLSocket, AS_SERVER )
        self.VerifyResult( "SSL_ResetHandshake", result )

    # For server side:
    def AcceptConnection( self, applicationData = None ):
        self.log.debug( "AcceptConnection" )
        self.acceptConnectionSucceeded = False

        self.InitializeSSLServerSocket()

        self.SSL_OptionSet( self.serverSSLSocket, SSL_SECURITY,                 True )

        self.ForceTLS_13( self.serverSSLSocket )
        
        self.SSL_OptionSet( self.serverSSLSocket, SSL_ROLLBACK_DETECTION,       True )
        self.SSL_OptionSet( self.serverSSLSocket, SSL_NO_LOCKS,                 True )
        self.SSL_OptionSet( self.serverSSLSocket, SSL_ENABLE_SESSION_TICKETS,   False )
        self.SSL_OptionSet( self.serverSSLSocket, SSL_ENABLE_DEFLATE,           False);
        # skipping SSL_SNISocketConfigHook
        # skipping SSL_ENABLE_SERVER_DHE option
        # skipping SSL_REQUIRE_DH_NAMED_GROUPS option
        # skipping SSL_REUSE_SERVER_ECDHE_KEY option
        # skipping SSL_EnableWeakDHEPrimeGroup
        # skipping SSL_ENABLE_EXTENDED_MASTER_SECRET option

        self.SSL_ConfigServerCert()

        # skipping SSL_ENABLE_FDX option
        # skipping SSL_NO_CACHE option
        # skipping SSL_ENABLE_0RTT_DATA option
        # skipping SSL_ENABLE_ALPN option
        # skipping SSL_NamedGroupConfig
        # skipping SSL_CipherPrefSetDefault
        # skipping SSL_HandshakeCallback
        # skipping SSL_AuthCertificateHook
        # skipping SSL_BadCertHook

        self.SSL_ResetHandshake()
        self.dataReceived = self.Recv()

        if applicationData != None:
            self.Send( applicationData )

        self.acceptConnectionSucceeded = True

    # For client side
    def Connect( self ):
        self.log.debug( "Connect" )
        self.InitializeSSLClientSocket()
        
        # skipping SSL_SetPKCS11PinArg
        self.SSL_OptionSet( self.clientSSLSocket, SSL_SECURITY,             True )
        self.SSL_OptionSet( self.clientSSLSocket, SSL_HANDSHAKE_AS_CLIENT,  True )
        # skipping SSL_CipherPrefSet
        self.ForceTLS_13( self.clientSSLSocket )

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
        self.log.debug( "Recv" )
        bufferSize  = 1024
        buffer      = bytearray( bufferSize )
        cBuffer     = ( c_uint8 * bufferSize ).from_buffer( buffer )
        flags       = c_int32( 0 )
        timeout     = c_int32( 0 )
        
        if self.clientSSLSocket != None:
            sslSocket = self.clientSSLSocket
        else:
            sslSocket = self.serverSSLSocket

        bytesReceived = self.nspr.PR_Recv( sslSocket, cBuffer, c_int32( bufferSize ), flags, timeout )
        self.log.info( "PR_Recv returned %d" % bytesReceived)

        if bytesReceived > 0:
            return bytearray( cBuffer[ : bytesReceived ] )
        #else:
        return b""

    def Send( self, buffer ):
        self.log.debug( "Send: %s" % buffer )
        buffer      = bytearray( buffer )
        cBuffer     = ( c_uint8 * len( buffer ) ).from_buffer( buffer )
        flags       = c_int32( 0 )
        timeout     = c_int32( 0 )
        
        if self.clientSSLSocket != None:
            sslSocket = self.clientSSLSocket
        else:
            sslSocket = self.serverSSLSocket

        result = self.nspr.PR_Send( sslSocket, cBuffer, c_int32( len( buffer ) ), flags, timeout )
        self.log.info( "PR_Send returned %d" % result)

        return result

#########################################################################
skipClientServerTest        = False
skipMockClientAndServer     = False
skipFindMsgDifferences      = False

class NSSTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(NSSTester, self).__init__(*args, **kwargs)

    def setUp( self ):
        self.tlsServer = None
        self.tlsClient = None

    def tearDown( self ):
        pass
        # if self.tlsServer is not None:
        #     self.tlsServer.Cleanup()
        # if self.tlsClient is not None:
        #     self.tlsClient.Cleanup()

    def CreateMockSocket( self, memorySocket ):
        mockMemorySocket               = PRWrapper()
        mockMemorySocket.ReadCallback  = memorySocket.ReadFromServer
        mockMemorySocket.WriteCallback = memorySocket.SendToServer

        return mockMemorySocket
                
    # def testSetupClient( self ):
    #     hostName = "test_server.com"

    #     self.tlsClient = NSS( "client" )
    #     self.tlsClient.InitClient( hostName )
    #     self.tlsClient.Connect()
    #     buf = self.tlsClient.Recv()

        # time.sleep(3)

    def test_NSS_ClientAndServer( self ):
        if skipClientServerTest:
            return
        hostName = "test_server.com"

        memorySocket = MemorySocket()

        self.tlsServer = NSS( "server" )
        self.tlsClient = NSS( "client" )

        self.tlsServer.InitServer( memorySocket )
        self.tlsClient.InitClient( memorySocket, hostName )

        serverThread = threading.Thread(target = self.tlsServer.AcceptConnection, args = [ b"Server->Client\x00" ] )
        serverThread.start()

        time.sleep( 0.1 )

        self.tlsClient.Connect()
        self.tlsClient.Send( b"Client->Server\x00" ) 
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

        # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )

    def test_MITLS_MockClientAndServer( self ):
        if skipMockClientAndServer:
            return

        self.tlsServer = NSS( "server" )
        # self.tlsClient = NSS( "client" )

        packetsDir = "transcripts/client_hello/"
        clientToServerTemplate = packetsDir + "msg-%02d-Client-to-Server.bin"
        serverToClientTemplate = packetsDir + "msg-%02d-Server-to-Client.bin"
        fileSocket = FileSocket( clientToServerTemplate, serverToClientTemplate )

        self.tlsServer.InitServer( fileSocket )

        serverThread = threading.Thread(target = self.tlsServer.AcceptConnection )
        serverThread.start()
        time.sleep( 0.1 )

        # mockMsgPath = r"c:\dev\microsoft-git\Everest\tests\pytester\transcripts\2017-06-12_09-00-18/msg-00-Client-to-Server.bin"
        # with open( mockMsgPath, "rb" ) as msgFile:
        #     mockMsg = msgFile.read()

        # print( "will send %s" % mockMsg)
        # self.tlsClient.Write( mockMsg )

        serverThread.join()

        tlsParser = TLSParser()
        for filePath in glob.glob( os.path.dirname( clientToServerTemplate ) + "/*" ):
            print( "Analyzing %s" % filePath )
            
            msg = tlsParser.GetMsgFromFile( filePath )
            pprint( msg ) 
            tlsParser.PrintMsg( msg )

        # We're done, report transcript:
        # pprint( memorySocket.tlsParser.transcript )

        # for msg in memorySocket.tlsParser.transcript:
        #     memorySocket.tlsParser.PrintMsg( msg )

    def test_NSS_FindMsgDifferences( self ):
        if skipFindMsgDifferences:
            return
        hostName = "test_server.com"

        transcripts = []
        for i in range( 2 ):
            memorySocket = MemorySocket()
            
            self.tlsServer = NSS( "server" )
            self.tlsClient = NSS( "client" )

            self.tlsServer.InitServer( memorySocket )
            self.tlsClient.InitClient( memorySocket, hostName )
        
            serverThread = threading.Thread(target = self.tlsServer.AcceptConnection )
            serverThread.start()

            time.sleep( 0.1 )

            self.tlsClient.Connect()
            buf = self.tlsClient.Recv()

            serverThread.join()

            transcripts.append( memorySocket.tlsParser.transcript )

        numMsgs = len( transcripts[ 0 ] )
        for msgIdx in range( numMsgs ):
            msg1 = transcripts[ 0 ][ msgIdx ]
            msg2 = transcripts[ 1 ][ msgIdx ]
            memorySocket.tlsParser.CompareMsgs( msg1, msg2 )

if __name__ == '__main__':
    skipClientServerTest        = True
    skipMockClientAndServer     = True
    skipFindMsgDifferences      = True

    skipClientServerTest        = False
    # skipMockClientAndServer     = False
    # skipFindMsgDifferences      = False



    unittest.main()
