import unittest
import logging
import os
import sys
import time
import threading
import struct
import subprocess
import datetime
import re
import traceback

from functools import partial
from pprint import pprint
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
                    c_uint64, \
                    CFUNCTYPE, \
                    POINTER                  


import argparse 
import config
import tlsparser
from tlsparser import   MemorySocket,                \
                        TLSParser,                   \
                        Direction,                   \
                        AttrDict,                    \
                        HANDSHAKE_TYPE,              \
                        PARENT_NODE,                 \
                        SWAP_ITEMS,                  \
                        HANDSHAKE_TYPE_CLIENT_HELLO, \
                        CIPHER_SUITES,               \
                        DIRECTION,                   \
                        RECORD_TYPE,                 \
                        NAME,                        \
                        HANDSHAKE_MSG,               \
                        RAW_CONTENTS,                \
                        RAW_RECORD,                  \
                        INTERPRETATION,              \
                        RECORD,                      \
                        KEY_SHARE_ENTRY


SUCCESS                     = 1
NULL_BYTE                   = b"\0"
TLS_VERSION_1_3             = b"1.3" + NULL_BYTE
# SERVER_KEY_PATH             = "/home/user/dev/microsoft-git/Everest/tests/pytester/certificates/rsa_certificates/test_server.key"
# SERVER_CA_PATH              = "/home/user/dev/microsoft-git/Everest/tests/pytester/certificates/rsa_certificates/ca.crt"
# SERVER_SIGNATURE_ALGORITHM  = "ECDSA+SHA384"
SUPPORTED_CIPHER_SUITES = [  
                            "TLS_AES_128_GCM_SHA256",               # OK
                            "TLS_AES_256_GCM_SHA384",               # OK
                            "TLS_CHACHA20_POLY1305_SHA256",         # OK
                            # "TLS_AES_128_CCM_SHA256",               # NOT ok: errmsg = "b'Failure("not linked to openSSL yet")'"                                    
                            # "TLS_AES_128_CCM_8_SHA256",             # NOT ok: errmsg = "b'Failure("not linked to openSSL yet")'"                                    
                            # "ECDHE-RSA-AES256-GCM-SHA384",          # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "ECDHE-RSA-AES128-GCM-SHA256",          # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "ECDHE-RSA-CHACHA20-POLY1305-SHA256",   # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "ECDHE-ECDSA-AES256-GCM-SHA384",        # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "ECDHE-ECDSA-AES128-GCM-SHA256",        # NOT OK:  NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "ECDHE-ECDSA-CHACHA20-POLY1305-SHA256", # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "DHE-RSA-AES256-GCM-SHA384",            # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "DHE-RSA-AES128-GCM-SHA256",            # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
                            # "DHE-RSA-CHACHA20-POLY1305-SHA256",     # NOT OK: NGO| negotiation failed: AD_handshake_failure (ciphersuite negotiation failed)    
 ]
SUPPORTED_SIGNATURE_ALGORITHMS = [ 
                                    'ECDSA+SHA512',  # OK 
                                    'ECDSA+SHA384',  # OK     
                                    'ECDSA+SHA256',  # OK     
                                    # 'ECDSA+SHA1',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm
                                    # 'RSA+SHA384',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm     
                                    # 'RSA+SHA512',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm     
                                    # 'RSA+SHA256',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm        
                                    # 'RSA+SHA1',      # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm                            
]
SUPPORTED_NAMED_GROUPS = [
                            "P-521", # a.k.a secp521r1   # OK                         
                            "P-384", # a.k.a secp384r1   # OK                         
                            "P-256", # a.k.a secp256r1   # OK                         
                            "X25519",                    # OK     
                            "X448",                      # NOT OK    TLS| StAE decrypt failed.; TLS| Ignoring the decryption failure (rejected 0-RTT data) 
                            "FFDHE4096",                 # OK         
                            "FFDHE3072",                 # OK         
                            "FFDHE2048",                 # OK         
]

PIECES_THAT_CANT_BE_SHUFFLED = [ KEY_SHARE_ENTRY ]

class MITLSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

def CString( pythonString ):
    NULL_BYTE = b"\0"
    return c_char_p( bytes( pythonString, "ascii" ) + NULL_BYTE )



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
    def __init__( self, name = "", sharedObjectPath = config.MITLS_SO_PATH  ):
        self.SetupLogger( name )
        self.log.info( "Initilizaed with sharedObjectPath = %s" % os.path.abspath( sharedObjectPath ) )
        self.log.info( "")
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
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL )
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

    def FFI_mitls_configure( self, hostName = "" ):
        self.log.debug( "FFI_mitls_configure" )
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

    def FFI_mitls_configure_cert_chain_file( self, filePath ):
        self.log.debug( "FFI_mitls_configure_cert_chain_file; filePath = %s" % os.path.abspath( filePath ) )
        self.miTLS.FFI_mitls_configure_cert_chain_file.restype = c_int

        ret = self.miTLS.FFI_mitls_configure_cert_chain_file( self.mitls_state, CString( filePath ) )
        self.VerifyResult( "FFI_mitls_configure_cert_chain_file", ret )

    def FFI_mitls_configure_private_key_file( self, filePath ):
        self.log.debug( "FFI_mitls_configure_private_key_file; filePath = %s" % os.path.abspath( filePath ) )
        self.miTLS.FFI_mitls_configure_private_key_file.restype = c_int

        ret = self.miTLS.FFI_mitls_configure_private_key_file( self.mitls_state, CString( filePath )  )
        self.VerifyResult( "FFI_mitls_configure_private_key_file", ret )

    def FFI_mitls_configure_ca_file( self, filePath ):
        self.log.debug( "FFI_mitls_configure_ca_file; filePath = %s" % os.path.abspath( filePath ) )
        self.miTLS.FFI_mitls_configure_ca_file.restype = c_int
        
        ret = self.miTLS.FFI_mitls_configure_ca_file( self.mitls_state, CString( filePath ) )
        self.VerifyResult( "FFI_mitls_configure_private_key_file", ret )

    def FFI_mitls_configure_signature_algorithms( self, signatureAlgorithms ):
        self.log.debug( 'FFI_mitls_configure_signature_algorithms; signatureAlgorithms = "%s"' % signatureAlgorithms )
        self.miTLS.FFI_mitls_configure_signature_algorithms.restype = c_int

        signatureAlgorithmsString = ":".join( signatureAlgorithms )
        ret = self.miTLS.FFI_mitls_configure_signature_algorithms( self.mitls_state, CString( signatureAlgorithmsString ) )
        self.VerifyResult( "FFI_mitls_configure_signature_algorithms", ret )

    def FFI_mitls_configure_cipher_suites( self, cipherSuites ):
        self.log.debug( 'FFI_mitls_configure_cipher_suites; cipherSuites = "%s"' % cipherSuites )
        self.miTLS.FFI_mitls_configure_cipher_suites.restype = c_int

        cipherSuitesString = ":".join( cipherSuites )
        ret = self.miTLS.FFI_mitls_configure_cipher_suites( self.mitls_state, CString( cipherSuitesString ) )
        self.VerifyResult( "FFI_mitls_configure_cipher_suites", ret )

    def FFI_mitls_configure_named_groups( self, namedGroups ):
        self.log.debug( 'FFI_mitls_configure_named_groups; namedGroups = "%s"' % namedGroups )
        self.miTLS.FFI_mitls_configure_named_groups.restype = c_int

        namedGroupsString = ":".join( namedGroups )
        ret = self.miTLS.FFI_mitls_configure_named_groups( self.mitls_state, CString( namedGroupsString ) )
        self.VerifyResult( "FFI_mitls_configure_named_groups", ret )

    def InitServer( self, 
                    supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
                    supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
                    supportedNamedGroups            = SUPPORTED_NAMED_GROUPS ):
        self.log.debug( "InitServer" )

        self.mitls_state = self.FFI_mitls_configure()
        self.FFI_mitls_configure_cert_chain_file            ( config.SERVER_CERT_PATH )
        self.FFI_mitls_configure_private_key_file           ( config.SERVER_KEY_PATH )
        self.FFI_mitls_configure_ca_file                    ( config.SERVER_CA_PATH )
        self.FFI_mitls_configure_cipher_suites              ( supportedCipherSuites )
        self.FFI_mitls_configure_signature_algorithms       ( supportedSignatureAlgorithms )
        self.FFI_mitls_configure_named_groups               ( supportedNamedGroups )

    def InitClient( self, 
                    hostName, 
                    supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
                    supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
                    supportedNamedGroups            = SUPPORTED_NAMED_GROUPS ):
        self.log.debug( "InitClient" )

        self.mitls_state = self.FFI_mitls_configure( hostName )
        self.FFI_mitls_configure_cipher_suites              ( supportedCipherSuites )
        self.FFI_mitls_configure_signature_algorithms       ( supportedSignatureAlgorithms )
        self.FFI_mitls_configure_named_groups               ( supportedNamedGroups )

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

    def AcceptConnection( self, applicationData = None ):
        try:
            self.log.debug( "AcceptConnection" )
            self.acceptConnectionSucceeded = False
            outmsg                   = c_char_p()
            errmsg                   = c_char_p() 
            self.FFI_mitls_callbacks = self.GetServerCallbacks()

            self.FFI_mitls_thread_register()

            self.miTLS.FFI_mitls_accept_connected.restype  = c_int
            self.miTLS.FFI_mitls_accept_connected.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp ]
            ret = self.miTLS.FFI_mitls_accept_connected(self.FFI_mitls_callbacks,
                                                        self.mitls_state,
                                                        byref( outmsg ),
                                                        byref( errmsg ) )
            self.PrintMsgIfNotNull( outmsg, errmsg )
            self.VerifyResult( "FFI_mitls_accept_connected", ret )
            self.log.debug( "FFI_mitls_accept_connected done!")
            
            self.acceptConnectionSucceeded = True

            self.dataReceived = self.Receive() #induces sending session ticket
            if applicationData != None:
                self.Send( applicationData )

        except Exception as err: 
            traceback.print_tb(err.__traceback__)
            raise
            # silence exception

    def Receive( self ):
        self.log.debug( "Receive" )
        outmsg              = c_char_p()
        errmsg              = c_char_p() 
        length = c_uint64( 0 )
        self.miTLS.FFI_mitls_receive.restype = c_voidp
        self.miTLS.FFI_mitls_receive.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp ]

        self.log.debug( "self.mitls_state = %s" % self.mitls_state )
        payloadPointer = self.miTLS.FFI_mitls_receive(  self.mitls_state, 
                                                        byref( length ), 
                                                        byref( outmsg ),
                                                        byref( errmsg ) );

        # self.log.debug( "Receive: length = %s" % length)
        # self.log.debug( "Receive: payloadPointer = %s" % payloadPointer)

        pyBuffer = bytearray( ( c_uint8 * length.value ).from_address( payloadPointer ) )
        self.log.debug( "Received from Client: %s\n" % pyBuffer ) 

        return pyBuffer

    # For client side
    def Connect( self ):
        self.log.debug( "Connect" )

        outmsg                   = c_char_p()
        errmsg                   = c_char_p() 
        self.FFI_mitls_callbacks = self.GetClientCallbacks()

        self.miTLS.FFI_mitls_connect.restype  = c_int
        self.miTLS.FFI_mitls_connect.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp ]

        ret = self.miTLS.FFI_mitls_connect( self.FFI_mitls_callbacks,
                                            self.mitls_state,
                                            byref( outmsg ),
                                            byref( errmsg ) )
        self.PrintMsgIfNotNull( outmsg, errmsg )
        self.VerifyResult( "FFI_mitls_connect", ret )

    def Send( self, payload ):
        self.log.debug( "Send: %s" % payload )
        outmsg                              = c_char_p( 0 )
        errmsg                              = c_char_p( 0 ) 
        self.miTLS.FFI_mitls_send.restype   = c_int
        self.miTLS.FFI_mitls_send.argtypes  = [ c_voidp, c_voidp, c_uint64, c_voidp, c_voidp ]
        
        cPayload = ( c_uint8 * len( payload ) ).from_buffer( bytearray( payload ) )
        ret      = self.miTLS.FFI_mitls_send(   self.mitls_state,
                                                cPayload,
                                                c_uint64( len( payload ) ),
                                                byref( outmsg ),
                                                byref( errmsg ) )
        self.PrintMsgIfNotNull( outmsg, errmsg )
        self.VerifyResult( "FFI_mitls_send", ret )

class MonitorLeakedKeys():
    def __init__( self ):
        self.keepLookingForKeys = False

    def MonitorStdoutForLeakedKeys( self ):
        LOG_FILE = "log.txt"
        tee      = subprocess.Popen(["tee", LOG_FILE ], stdin=subprocess.PIPE)
        os.dup2(tee.stdin.fileno(), sys.stdout.fileno())
        # os.dup2(tee.stdin.fileno(), sys.stderr.fileno())

        self.keepLookingForKeys = True

        findKeysThread = threading.Thread(target = self.MonitorStdoutForLeakedKeys_thread, args = [ LOG_FILE ] )
        findKeysThread.start()

    def StopMonitorStdoutForLeakedKeys( self ):
        self.keepLookingForKeys = False

    @staticmethod
    def ChopStringToBytes( hexEncodedInContiniousString ):
        return re.findall('..', hexEncodedInContiniousString )

    def MonitorStdoutForLeakedKeys_thread( self, logFileName ):
        PATTERN = r"key\[(.)\]:(.+), IV=(.+)"

        MSG_FILENAME    = "%s-keys-mitls.%d"
        timestamp       = datetime.datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d_%H-%M-%S.%f')
        keysDir         = tlsparser.LEAKED_KEYS_DIR + "/" + timestamp
        
        if not os.path.exists( keysDir ):
            os.makedirs( keysDir )

        keyFilePath = keysDir + "/" + MSG_FILENAME
        keyIdx = 0
        with open( logFileName ) as logFile:
            while self.keepLookingForKeys:
                line = logFile.readline()
                if len( line ) == 0:
                    time.sleep( 0.1 )
                    continue

                result = re.search( PATTERN, line )
                if result is None:
                    continue

                entity = result.groups()[ 0 ].strip()
                rawKey = result.groups()[ 1 ].strip()
                rawIV  = result.groups()[ 2 ].strip()
                IV  = "".join( map( lambda x: "0x%s, " % x , self.ChopStringToBytes( rawIV ) ) )
                key = "".join( map( lambda x: "0x%s, " % x , self.ChopStringToBytes( rawKey ) ) )

                filePath = keyFilePath % (entity, keyIdx)
                with open( filePath, "w" ) as keyFile:
                    keyFile.write( "IV: %s\n" % IV )
                    keyFile.write( "KEY: %s\n" % key )
                    sys.stderr.write( "Dumped key to %s\n" % filePath )
                    keyIdx += 1


runClientServerTest                  = False
runMockClientAndServer               = False
runFindMsgDifferences                = False
runCipherSuites                      = False
runSignatureAlgorithms               = False
runNamedGroups                       = False
runCipherSuites_commonSuiteIsHighest = False

class MITLSTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(MITLSTester, self).__init__(*args, **kwargs)

        self.SetupLogger()

    def SetupLogger( self ):
        self.log = logging.getLogger( 'MITLSTester' )
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL )
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def setUp(self):
        self.tlsServer = None
        self.tlsClient = None

    def tearDown(self):
        if self.tlsServer is not None:
            self.tlsServer.Cleanup()
        if self.tlsClient is not None:
            self.tlsClient.Cleanup()

        self.tlsServer = None
        self.tlsClient = None

    def testInitMITLS( self ):
        self.tlsServer = MITLS( "server" )
        self.tlsClient = MITLS( "client" )

    def testSetupServer( self ):
        self.tlsServer = MITLS( "server" )
        self.tlsServer.InitServer()

    def testSetupClient( self ):
        hostName = "test_server.com"

        self.tlsClient = MITLS( "client" )
        self.tlsClient.InitClient( hostName )

    def StartServerThread(  self, 
                            supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
                            supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
                            supportedNamedGroups            = SUPPORTED_NAMED_GROUPS,
                            applicationData                 = None ):
        self.tlsServer = MITLS( "server" )
        self.tlsServer.InitServer(  supportedCipherSuites, 
                                    supportedSignatureAlgorithms, 
                                    supportedNamedGroups )
        
        serverThread   = threading.Thread(target = self.tlsServer.AcceptConnection, args = [ applicationData ] )
        serverThread.start()

        return serverThread

    def test_MITLS_ClientAndServer( self ):
        if not runClientServerTest:
            return

        memorySocket.tlsParser  = tlsparser.TLSParser()
        serverThread            = self.StartServerThread( applicationData = b"Server->Client\x00" )

        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        try:
            self.tlsClient = MITLS( "client" )
            self.tlsClient.InitClient( hostName = "test_server.com" )
            self.tlsClient.Connect()
            self.tlsClient.Send( b"Client->Server\x00" )            
            self.tlsClient.dataReceived = self.tlsClient.Receive()
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        self.log.debug( "Joining server thread" )
        serverThread.join()

        if config.LOG_LEVEL < logging.ERROR:
            pprint( memorySocket.tlsParser.transcript )
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )
                # if tlsparser.IV_AND_KEY in msg.keys():
                #     pprint( msg[ tlsparser.IV_AND_KEY ])

        self.log.debug( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        self.log.debug( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )
        return memorySocket.tlsParser.transcript

    def test_ReorderCipherSuites( self ):
        return
        global runClientServerTest
        orig_runClientServerTest = runClientServerTest
        runClientServerTest      = True
        try:
            transcript               = self.test_MITLS_ClientAndServer()
            msg0                     = transcript[ 0 ]
            msg1                     = transcript[ 1 ]

            manipulation = AttrDict( { HANDSHAKE_TYPE : HANDSHAKE_TYPE_CLIENT_HELLO,
                                       PARENT_NODE    : CIPHER_SUITES,
                                       SWAP_ITEMS     : AttrDict( { 'index1' : 0, 'index2' : -1 } ) })
            tlsParser = tlsparser.TLSParser()
            manipulatedMsg = tlsParser.ManipulateMsg( msg1, manipulation )
            self.assertTrue( manipulatedMsg == None )

            manipulatedMsg = tlsParser.ManipulateMsg( msg0, manipulation )

            print( "==================== Original Message =====================")
            tlsParser.PrintMsg( msg0 )

            # print( "==================== Manipulated Message =====================")
            # tlsParser.PrintMsg( manipulatedMsg )

            print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
            rawMsg = tlsParser.ReconstructRecordAndCompareToOriginal( manipulatedMsg, doCompare = False )
            
            # The following will print the message as a side effect
            parsedManipulatedMsg = tlsParser.Digest( rawMsg, manipulatedMsg[ DIRECTION ] )

            # tlsParser.PrintMsg( parsedManipulatedMsg )
        
        finally:
            runClientServerTest = orig_runClientServerTest

    def test_ReorderCipherSuites_onWire( self ):
        return 
        manipulation = AttrDict( { HANDSHAKE_TYPE : HANDSHAKE_TYPE_CLIENT_HELLO,
                                   PARENT_NODE    : CIPHER_SUITES,
                                   SWAP_ITEMS     : AttrDict( { 'index1' : 1, 'index2' : 2 } ) })
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        exceptionThrown = False
        try:
            self.RunSingleTest( msgManipulators = [ manipulation ] )
        except:
            exceptionThrown = True
            traceback.print_exc()

        keysMonitor.StopMonitorStdoutForLeakedKeys()

        self.assertTrue( exceptionThrown == True )

        for msg in  memorySocket.tlsParser.transcript:
            print( "Direction: %s, type = %s" % (msg[ DIRECTION ], msg[ RECORD_TYPE ] ) )

    def CreateShuffleChildrenManipulations( self, node, handshakeType ):
        shuffleManipulations = []
        if node.Name in PIECES_THAT_CANT_BE_SHUFFLED:
            return shuffleManipulations

        numberOfChildren = len( node.Interpretation )
        for i in range( numberOfChildren - 1 ):
            shuffleManipulations.append( AttrDict( {   HANDSHAKE_TYPE : handshakeType,
                                                       PARENT_NODE    : node.Name,
                                                       SWAP_ITEMS     : AttrDict( { 'index1' : i, 'index2' : i + 1 } ) }) )

        pprint( shuffleManipulations )
        return shuffleManipulations

    def TraverseBFSAndGenerateManipulations( self, topTreeLayer, manipulationFactory ):
        manipulations = []

        # BFS traverse over msg tree:
        # First go over all nodes in currentLayer, collecting their children in nextLayer.
        # Then move to next depth layer by swapping currentLayer <-- nextLayer
        currentLayer  = topTreeLayer
        while True:
            nextLayer = []
            for node in currentLayer:
                if TLSParser.IsTerminalPiece( node ):
                    continue

                manipulations += manipulationFactory( node ) 
                for piece in node.Interpretation:
                    nextLayer.append( piece )
        
            if len( nextLayer ) == 0:
                break  
            #else:   
            currentLayer = nextLayer

        return manipulations

    def test_ReorderPieces_onWire( self ):
        return 
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        self.RunSingleTest()
        keysMonitor.StopMonitorStdoutForLeakedKeys()
        

        #################################
        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateShuffleChildrenManipulations,  
                                                                                                handshakeType = handshakeType )   )
        ###########################
        tlsParser = TLSParser()
        msg0      = originalTranscript[ 0 ]
        for manipulation in manipulations:
            print( "###############################################")
            pprint( manipulation )
            print( "==================== Original Message =====================")
            tlsParser.PrintMsg( msg0 )

            print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
            manipulatedMsg = tlsParser.ManipulateMsg( msg0, manipulation )
            rawMsg         = tlsParser.ReconstructRecordAndCompareToOriginal( manipulatedMsg, doCompare = False )
            
            # The following will print the message as a side effect
            parsedManipulatedMsg = tlsParser.Digest( rawMsg, manipulatedMsg[ DIRECTION ] )

        
    def RemoveItemAndSplit( self, itemList, itemToRemove ):
        otherItems = itemList[ : ]
        otherItems.remove( itemToRemove )
        numItems   = len( otherItems )
        listA      = otherItems[ : numItems // 2 ]
        listB      = otherItems[ numItems // 2 : ] 

        return listA, listB

    def RunSingleTest(  self, 
                        supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
                        supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
                        supportedNamedGroups            = SUPPORTED_NAMED_GROUPS,
                        applicationData                 = None,
                        msgManipulators                 = [] ):
        memorySocket.tlsParser = tlsparser.TLSParser()
        memorySocket.tlsParser.SetMsgManipulators( msgManipulators )
        serverThread = self.StartServerThread(  supportedCipherSuites,
                                                supportedSignatureAlgorithms,
                                                supportedNamedGroups,
                                                applicationData )

        self.tlsClient = MITLS( "client" )
        self.tlsClient.InitClient(  "test_server.com", 
                                    supportedCipherSuites,
                                    supportedSignatureAlgorithms,
                                    supportedNamedGroups )
        self.tlsClient.Connect()
        self.tlsClient.Send( b"Client->Server\x00" )            
        self.tlsClient.dataReceived = self.tlsClient.Receive()

        serverThread.join()
        if self.tlsServer.acceptConnectionSucceeded == False:
            raise Exception( "Server failed to connect" )

        self.log.debug( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        self.log.debug( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

    def test_NamedGroups( self ):
        if not runNamedGroups:
            return

        self.log.info( "test_NamedGroups" )
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "named_groups.txt", "w" ) as logFile:
            for group in SUPPORTED_NAMED_GROUPS:
                logFile.write( "group = %-40s" % group )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest( supportedNamedGroups = [ group ], applicationData = b"Server->Client\x00" )
                    logFile.write( "OK\n" )
                except:
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_SignatureAlgorithms( self ):
        if not runSignatureAlgorithms:
            return

        self.log.info( "test_SignatureAlgorithms" )
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "signature_algorithms.txt", "w" ) as logFile:
            for algorithm in SUPPORTED_SIGNATURE_ALGORITHMS:
                logFile.write( "algorithm = %-40s" % algorithm )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest( supportedSignatureAlgorithms = [ algorithm ] )
                    logFile.write( "OK\n" )
                except:
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_CipherSuites( self ):
        if not runCipherSuites:
            return

        self.log.info( "test_CipherSuites" )
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "cipher_suites.txt", "w" ) as logFile:
            for cipherSuite in SUPPORTED_CIPHER_SUITES:
                logFile.write( "cipherSuite = %-40s" % cipherSuite )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest( supportedCipherSuites = [ cipherSuite ] )
                    logFile.write( "OK\n" )
                except:
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_CipherSuites_commonSuiteIsHighest( self ):
        if not runCipherSuites_commonSuiteIsHighest:
            return

        self.log.info( "test_CipherSuites_commonSuiteIsHighest" )
        

        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        try:
            for cipherSuite in SUPPORTED_CIPHER_SUITES:
                self.log.info( "cipherSuite = %s" % cipherSuite )

                cipherSuiteListA, cipherSuiteListB = self.RemoveItemAndSplit( SUPPORTED_CIPHER_SUITES, cipherSuite )
                cipherSuiteListA.insert( 0, cipherSuite )
                cipherSuiteListB.insert( 0, cipherSuite )

                memorySocket.tlsParser = tlsparser.TLSParser()
                serverThread = self.StartServerThread( supportedCipherSuites = cipherSuiteListA )

                self.tlsClient = MITLS( "client" )
                self.tlsClient.InitClient(  hostName              = "test_server.com", 
                                            supportedCipherSuites = cipherSuiteListB )
                self.tlsClient.Connect()
            
                serverThread.join()
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

            # pprint( memorySocket.tlsParser.transcript )
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )

    def SendToServerFromFile( self, memorySocket, msgFilePath ):
        with open( msgFilePath, "rb" ) as msgFile:
            mockMsg = msgFile.read()

        cBuffer = ( c_uint8 * len( mockMsg ) ).from_buffer( bytearray( mockMsg ) )
        
        memorySocket.SendToServer( None, self.tlsServer.cutils.getAddress( cBuffer ), len( mockMsg ) )

    def GetMsgFromFile( self, msgFilePath ):
        with open( msgFilePath, "rb" ) as msgFile:
            rawMsg = msgFile.read()

        if Direction.CLIENT_TO_SERVER in msgFilePath:
            direction = Direction.CLIENT_TO_SERVER
        elif Direction.SERVER_TO_CLIENT in msgFilePath:
            direction = Direction.SERVER_TO_CLIENT
        else:
            raise Exception( "Unknown direction" )

        tlsParser = TLSParser()
        msg       = tlsParser.Digest( rawMsg, direction )

        return msg

    def test_MITLS_MockClientAndServer( self ):
        if not runMockClientAndServer:
            return

        hostName = "test_server.com"

        memorySocket.tlsParser = tlsparser.TLSParser()

        self.tlsServer = MITLS( "server" )
        self.tlsServer.MonitorStdoutForLeakedKeys()
        self.tlsServer.InitServer()

        # self.tlsServer.AcceptConnection()
        serverThread = threading.Thread(target = self.tlsServer.AcceptConnection )
        serverThread.start()

        mockMsgPath = "transcripts/2017-06-07_17-10-21/msg-00-Client-to-Server.bin"
        self.SendToServerFromFile( memorySocket, mockMsgPath )
        
        serverThread.join()
        self.tlsServer.StopMonitorStdoutForLeakedKeys()

        for msg in memorySocket.tlsParser.transcript:
            memorySocket.tlsParser.PrintMsg( msg )

        originalServerResponse = self.GetMsgFromFile( "transcripts/2017-06-07_17-10-21/msg-01-Server-to-Client.bin")
        currentServerResponse  = memorySocket.tlsParser.transcript[ 1 ]

        memorySocket.tlsParser.CompareMsgs( originalServerResponse, currentServerResponse )

        pprint( originalServerResponse )

    def test_MITLS_FindMsgDifferences( self ):
        if not runFindMsgDifferences:
            return

        hostName = "test_server.com"

        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        transcripts = []
        for i in range( 2 ):
            memorySocket.FlushBuffers()
            memorySocket.tlsParser = tlsparser.TLSParser()

            self.tlsServer = MITLS( "server" )
            self.tlsServer.InitServer()

            # self.tlsServer.AcceptConnection()
            serverThread = threading.Thread(target = self.tlsServer.AcceptConnection )
            serverThread.start()

            self.tlsClient = MITLS( "client" )
            self.tlsClient.InitClient( hostName )
            self.tlsClient.Connect()

            serverThread.join()
            transcripts.append( memorySocket.tlsParser.transcript )
            print( "#" * 40 )
            # time.sleep( 3 )

        keysMonitor.StopMonitorStdoutForLeakedKeys()

        numMsgs = len( transcripts[ 0 ] )
        for msgIdx in range( numMsgs ):
            msg1 = transcripts[ 0 ][ msgIdx ]
            msg2 = transcripts[ 1 ][ msgIdx ]
            # memorySocket.tlsParser.PrintMsg( msg1 )
            # memorySocket.tlsParser.PrintMsg( msg2 )
            memorySocket.tlsParser.CompareMsgs( msg1, msg2 )

def ConfigureMITLSArguments( parser ):
    parser.add_argument("-s", "--supress_output", help="turn off verbosity", action='store_false' )
    parser.add_argument("--mitls_so_path", help="full path_to_libmitls.so")
    parser.add_argument("--srv_cert_path", help="full path_to_server_cert_file")
    parser.add_argument("--srv_key_path",  help="full path_to_server_key_path")
    parser.add_argument("--srv_ca_path",   help="full path_to_server_ca_path")
    parser.add_argument("--openssl_path",  help="full path_to_openssl.lib")
    parser.add_argument("unittest_args", nargs="*")
    
def HandleMITLSArguments( args ):
    if args.mitls_so_path:
        config.set_mitls_so_path(args.mitls_so_path)

    if not args.supress_output:
        SUPRESS_ALL_LOGS = 100
        config.set_log_level( SUPRESS_ALL_LOGS )

if __name__ == '__main__':
    # SI: argparse seems not to complete before unitest.main starts running? 
    # usage = "usage: %prog [options] arg"
    parser = argparse.ArgumentParser()
    ConfigureMITLSArguments( parser )
    
    args   = parser.parse_args()
    HandleMITLSArguments( args )

    # SI: reset args, else unittest.main complains of flags not being valid.
    sys.argv[1:] = args.unittest_args

    # SI: these should be args. 
    # runClientServerTest        = True
    # runMockClientAndServer     = True
    # runFindMsgDifferences      = True
    # runCipherSuites            = True
    # runSignatureAlgorithms     = True
    # runNamedGroups             = True
    # runCipherSuites_commonSuiteIsHighest = True

    unittest.main()



