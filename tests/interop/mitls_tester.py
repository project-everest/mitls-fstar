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
from copy      import deepcopy
from functools import partial
from pprint import pprint, pformat
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
                    POINTER,   \
                    addressof                  


import argparse 
import config
import tlsparser
from tlsparser import   MemorySocket,                       \
                        TLSParser,                          \
                        Direction,                          \
                        AttrDict,                           \
                        GetKey,								\
                        HANDSHAKE_TYPE,                     \
                        PARENT_NODE,                        \
                        SWAP_ITEMS,                         \
                        HANDSHAKE_TYPE_CLIENT_HELLO,        \
                        CIPHER_SUITES,                      \
                        DIRECTION,                          \
                        RECORD_TYPE,                        \
                        NAME,                               \
                        HANDSHAKE_MSG,                      \
                        RAW_CONTENTS,                       \
                        RAW_RECORD,                         \
                        INTERPRETATION,                     \
                        RECORD,                             \
                        KEY_SHARE_ENTRY,                    \
                        IV_AND_KEY,                         \
                        EXTENSION_TYPE_NAMES,               \
                        EXTENSION_TYPE_SUPPORTED_VERSIONS,  \
                        EXTRACT_TO_PLAINTEXT,               \
                        HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS,\
                        HANDSHAKE_TYPE_CERTIFICATE         ,\
                        HANDSHAKE_TYPE_CERTIFICATE_REQUEST ,\
                        HANDSHAKE_TYPE_CERTIFICATE_VERIFY  ,\
                        HANDSHAKE_TYPE_FINISHED,            \
                        REMOVE_ITEM,                        \
                        ALERT,                              \
                        CERT_ENTRY,                         \
                        TLS_RECORD_TYPE_APP_DATA



SUCCESS                     = 1
SIZEOF_QUIC_TICKET          = 1296
NULL_BYTE                   = b"\0"
TLS_VERSION_1_3             = b"1.3" + NULL_BYTE
# SERVER_KEY_PATH             = "/home/user/dev/microsoft-git/Everest/tests/pytester/certificates/rsa_certificates/test_server.key"
# SERVER_CA_PATH              = "/home/user/dev/microsoft-git/Everest/tests/pytester/certificates/rsa_certificates/ca.crt"
# SERVER_SIGNATURE_ALGORITHM  = "ECDSA+SHA384"
SUPPORTED_CIPHER_SUITES = [  
                            "TLS_AES_128_GCM_SHA256",               # OK
                            "TLS_AES_256_GCM_SHA384",               # OK
                            "TLS_CHACHA20_POLY1305_SHA256",         # OK
                            # # "TLS_AES_128_CCM_SHA256",               # NOT ok: errmsg = "b'Failure("not linked to openSSL yet")'"                                    
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
                                    'ECDSA+SHA256',  # OK     
                                    'ECDSA+SHA384',  # OK     
                                    'ECDSA+SHA512',  # OK 
                                    # 'ECDSA+SHA1',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm
                                    # 'RSA+SHA384',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm     
                                    # 'RSA+SHA512',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm     
                                    # 'RSA+SHA256',    # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm        
                                    # 'RSA+SHA1',      # NOT OK: FFI| returning error: AD_handshake_failure no compatible signature algorithm                            
]
SUPPORTED_NAMED_GROUPS = [
                            "X25519",                    # OK 
                            "P-521", # a.k.a secp521r1   # OK                         
                            "P-384", # a.k.a secp384r1   # OK                         
                            "P-256", # a.k.a secp256r1   # OK                         
                            # "X448",                      # NOT OK    TLS| StAE decrypt failed.; TLS| Ignoring the decryption failure (rejected 0-RTT data) 
                            # "FFDHE4096",                 # OK         
                            # "FFDHE3072",                 # OK         
                            # "FFDHE2048",                 # OK         
]

PIECES_THAT_CANT_BE_SHUFFLED = [ KEY_SHARE_ENTRY, 
                                 #EXTENSION_TYPE_NAMES[ EXTENSION_TYPE_SUPPORTED_VERSIONS ] # because a potential bug was found
                                 ]
PIECES_THAT_CANT_BE_SKIPPED  = [ KEY_SHARE_ENTRY, CERT_ENTRY ]                                 

class MITLSError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

def CString( pythonString ):
    NULL_BYTE = b"\0"
    return c_char_p( bytes( pythonString, "ascii" ) + NULL_BYTE )

QUICResult = AttrDict( {'TLS_would_block' 						: 0,
						'TLS_error_local' 						: 1,
						'TLS_error_alert' 						: 2,
						'TLS_client_early' 						: 3,
						'TLS_client_complete' 					: 4,
						'TLS_client_complete_with_early_data' 	: 5,
						'TLS_server_accept' 					: 6,
						'TLS_server_accept_with_early_data' 	: 7,
						'TLS_server_complete' 					: 8,
						'TLS_error_other' 						: 0xffff, } )

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
    MAX_BUFFER_SIZE = 8 * 1024 #see QuicWin.cpp

    def __init__( self, name = "", sharedObjectPath = config.MITLS_SO_PATH  ):
        self.SetupLogger( name )
        self.log.info( "Initilizaed with sharedObjectPath = %s" % os.path.abspath( sharedObjectPath ) )
        self.log.info( "")
        self.miTLS              = CDLL( sharedObjectPath ) 
        self.cutils             = CDLL( "cutils/cutils.so" )
        self.mitls_state        = None 
        self.quicEarlySecret    = None

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
        if outmsg != None and outmsg.value != None:
            self.log.error( 'outmsg = "%s"' % outmsg.value )
            self.miTLS.FFI_mitls_free_msg( outmsg )

        if errmsg.value != None:
            self.log.error( 'errmsg = "%s"' % errmsg.value )
            self.miTLS.FFI_mitls_free_msg( errmsg )

    def FFI_mitls_quic_create( self, quicConfig ):
        self.log.debug( "FFI_mitls_quic_create; quicConfig = 0x%x" % quicConfig )

        quicState = c_voidp()
        errmsg    = c_char_p()

        self.miTLS.FFI_mitls_quic_create.restype  = c_int
        self.miTLS.FFI_mitls_quic_create.argtypes = [ c_voidp, c_voidp, c_voidp ]
        ret = self.miTLS.FFI_mitls_quic_create( byref( quicState ),
        										quicConfig,
                                                byref( errmsg ) )
        self.log.debug( "FFI_mitls_quic_create --> %s" % quicState )
        self.PrintMsgIfNotNull( None, errmsg )
        self.VerifyResult( "FFI_mitls_quic_create", ret )

        return quicState

    def FFI_mitls_configure( self, hostName = "" ):
        self.log.debug( "FFI_mitls_configure" )
        mitls_state = c_voidp()
        tls_version = c_char_p( TLS_VERSION_1_3 )
        host_name   = c_char_p( bytes( hostName, "ascii" ) + NULL_BYTE )
        outmsg      = c_char_p()
        errmsg      = c_char_p()

        self.miTLS.FFI_mitls_configure.restype = c_int
        self.miTLS.FFI_mitls_configure.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp, c_voidp ]
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

    def InitQUIC( 	self,
    				isServer,
    			  	hostName 						= None, 
	                supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
	                supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
	                supportedNamedGroups            = SUPPORTED_NAMED_GROUPS,
                    quicSessionTicket              = None ):
        self.cutils.QuicConfigCreate.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp, c_voidp, c_voidp, c_voidp, c_uint32, c_voidp ]
        self.cutils.QuicConfigCreate.restype  = c_voidp

        
        if quicSessionTicket is None:
            quicTicket_c = c_voidp( None )
        else:
            quicTicket_c = ( c_uint8 * SIZEOF_QUIC_TICKET ).from_buffer( quicSessionTicket )
        
        self.quicConfig = self.cutils.QuicConfigCreate( CString( config.SERVER_CERT_PATH ),
        												CString( config.SERVER_KEY_PATH  ),
        												CString( config.SERVER_CA_PATH   ),
        												CString( ":".join( supportedCipherSuites 		) ),
        												CString( ":".join( supportedSignatureAlgorithms ) ),
        												CString( ":".join( supportedNamedGroups 		) ),
        												CString( hostName ),
        												c_uint32( isServer ),
                                                        quicTicket_c )
        self.mitlsQuicState = self.FFI_mitls_quic_create( self.quicConfig )

        self.clientToServer = ( c_uint8 * self.MAX_BUFFER_SIZE )()
        self.serverToClient = ( c_uint8 * self.MAX_BUFFER_SIZE )()

    def InitQUICClient( self, 
	                    hostName, 
	                    supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
	                    supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
	                    supportedNamedGroups            = SUPPORTED_NAMED_GROUPS,
                        quicSessionTicket              = None  ):
        self.log.debug( "InitQUICClient" )
        isServer = 0
        self.InitQUIC( 	isServer, 
        				hostName,
			        	supportedCipherSuites,       
						supportedSignatureAlgorithms,
						supportedNamedGroups,
                        quicSessionTicket 			)

    def InitQUICServer( self, 
	                    supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
	                    supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
	                    supportedNamedGroups            = SUPPORTED_NAMED_GROUPS ):
        self.log.debug( "InitQUICServer" )
        isServer = 1
        hostName = ""
        self.InitQUIC( 	isServer, 
        				hostName,
			        	supportedCipherSuites,       
						supportedSignatureAlgorithms,
						supportedNamedGroups 			)

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

    def FFI_mitls_quic_process( self, inputCBuffer, inputSize, outputCBuffer ):
        inputSize_c = c_uint64( inputSize )
        bytesToSend = c_uint64( len( outputCBuffer ) )
        errmsg      = c_char_p() 

        self.miTLS.FFI_mitls_quic_process.argtypes = [ c_voidp, c_voidp, c_voidp, c_voidp, c_voidp, c_voidp ]
        self.miTLS.FFI_mitls_quic_process.restype  = c_uint32
        ret = self.miTLS.FFI_mitls_quic_process( 	self.mitlsQuicState, 
        											inputCBuffer, 
        											byref( inputSize_c ),
        											outputCBuffer,
        											byref( bytesToSend ),
        											byref( errmsg ) )
        self.PrintMsgIfNotNull( None, errmsg )

        if ret == QUICResult.TLS_error_other or \
           ret == QUICResult.TLS_error_local or \
           ret == QUICResult.TLS_error_alert:
           errMsg = "FFI_mitls_quic_process returned error code: 0x%x" % ret
           self.log.error( errMsg )
           raise MITLSError( errMsg )

        self.log.debug( "FFI_mitls_quic_process --> %-25s; %d bytes to send" % (GetKey( QUICResult, ret, "<unknown error code %d>" % ret), bytesToSend.value ))
        return bytesToSend.value, ret

    def AssertEqual( self, valueA, valueB, msg ):
        if valueA != valueB:
            self.log.error( msg )
            raise MITLSError( msg )

    def AssertGreater( self, valueA, valueB, msg ):
        if valueA <= valueB:
            self.log.error( msg )
            raise MITLSError( msg )

    def AcceptQUICConnection( self, earlyData = None ):
        try:
            self.log.debug( "AcceptQUICConnection" )
            self.acceptConnectionSucceeded 	= False
            outmsg                   		= c_char_p()
            errmsg                   		= c_char_p() 
            
            self.FFI_mitls_thread_register()

            lastResult = -1
            while lastResult != QUICResult.TLS_server_complete:
                bytesRead 			       = memorySocket.ReadFromClient( None, addressof( self.clientToServer ), len( self.clientToServer ) )
                numBytesToSend, lastResult = self.FFI_mitls_quic_process( self.clientToServer, bytesRead, self.serverToClient )

                if numBytesToSend > 0:
                    memorySocket.SendToClient( None, addressof( self.serverToClient ), numBytesToSend )

                if lastResult == QUICResult.TLS_server_accept_with_early_data:
                    self.quicEarlySecret = self.GetQUICSecret( isEarlyData = True )
                
            
            # Send session ticket:
            bytesRead = 0
            numBytesToSend, lastResult = self.FFI_mitls_quic_process( self.clientToServer, bytesRead, self.serverToClient )            
            self.AssertGreater( numBytesToSend, 0, "Expeted FFI_mitls_quic_process to have bytes to send (session ticket)" )
            self.AssertEqual  ( lastResult, QUICResult.TLS_would_block, "FFI_mitls_quic_process returned %d instead of TLS_would_block (%d)" % ( lastResult, QUICResult.TLS_would_block ) )
            memorySocket.SendToClient( None, addressof( self.serverToClient ), numBytesToSend )

            self.log.debug( "AcceptQUICConnection done!")
            
            self.acceptConnectionSucceeded = True

        except Exception as err: 
            traceback.print_tb(err.__traceback__)
            raise
    
    def AcceptConnection( self, applicationData = None ):
        try:
            self.log.debug( "AcceptConnection; mitls_state = %s" % self.mitls_state )
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
            pprint( traceback.format_tb( err.__traceback__ ) )
            pprint( err )
            # raise
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

    def FFI_mitls_quic_get_ticket( self ):
        self.miTLS.FFI_mitls_quic_get_ticket.restype  = c_int
        self.miTLS.FFI_mitls_quic_get_ticket.argtypes = [ c_voidp, c_voidp, c_voidp ]
        errmsg                                        = c_char_p() 

        quicTicket   = bytearray( SIZEOF_QUIC_TICKET )
        quicTicket_c = ( c_uint8 * SIZEOF_QUIC_TICKET ).from_buffer( quicTicket )

        ret = self.miTLS.FFI_mitls_quic_get_ticket( self.mitlsQuicState,
                                                    quicTicket_c,
                                                    byref( errmsg ) )
        self.PrintMsgIfNotNull( None, errmsg )
        self.VerifyResult( "FFI_mitls_quic_get_ticket", ret )

        return quicTicket

    # For client side
    def QUICConnect( self ):
        self.log.debug( "QUICConnect" )

        bytesRead  				   = 0
        numBytesToSend, lastResult = self.FFI_mitls_quic_process( self.serverToClient, bytesRead, self.clientToServer )
        
        if lastResult == QUICResult.TLS_client_early:
            self.quicEarlySecret = self.GetQUICSecret( isEarlyData = True )

        if numBytesToSend > 0:
        	memorySocket.SendToServer( None, addressof( self.clientToServer ), numBytesToSend )
        else:
        	raise MITLSError( "QUICConnect: FFI_mitls_quic_process doesn't want to send anything")

        while lastResult != QUICResult.TLS_client_complete and lastResult != QUICResult.TLS_client_complete_with_early_data:
            bytesRead 				   = memorySocket.ReadFromServer( None, addressof( self.serverToClient ), len( self.serverToClient ) )        	
            numBytesToSend, lastResult = self.FFI_mitls_quic_process( self.serverToClient, bytesRead, self.clientToServer )	

            if numBytesToSend > 0:
                memorySocket.SendToServer( None, addressof( self.clientToServer ), numBytesToSend )

        #Get session ticket
        bytesRead                  = memorySocket.ReadFromServer( None, addressof( self.serverToClient ), len( self.serverToClient ) )  
        numBytesToSend, lastResult = self.FFI_mitls_quic_process( self.serverToClient, bytesRead, self.clientToServer )            
        self.AssertEqual( numBytesToSend, 0, "Expeted FFI_mitls_quic_process to have bytes to send (session ticket)" )
        self.AssertEqual( lastResult, QUICResult.TLS_would_block, "FFI_mitls_quic_process returned %d instead of TLS_would_block (%d)" % ( lastResult, QUICResult.TLS_would_block ) )

        quicSessionTicket = self.FFI_mitls_quic_get_ticket()        

        self.log.debug( "QUICConnect completed!" )

        return quicSessionTicket

    def FFI_mitls_quic_free( self ):
        self.log.debug( "FFI_mitls_quic_free" )
        self.miTLS.FFI_mitls_quic_free.argtypes = [ c_voidp ]
        self.miTLS.FFI_mitls_quic_free.restype  = None

        self.miTLS.FFI_mitls_quic_free( self.mitlsQuicState )

    def QUICCleanup( self ):
        self.FFI_mitls_quic_free()

    def GetQUICSecret( self, isEarlyData = False ):
        SIZEOF_QUIC_SECRET = 72

        early = c_int( 0 )
        if isEarlyData:
            early = c_int( 1 )
        
        quicSecret   = bytearray( SIZEOF_QUIC_SECRET )
        quicSecret_c = ( c_uint8 * SIZEOF_QUIC_SECRET ).from_buffer( quicSecret )

        self.miTLS.FFI_mitls_quic_get_exporter.restype  = c_int
        self.miTLS.FFI_mitls_quic_get_exporter.argtypes = [ c_voidp, c_int, c_voidp, c_voidp ]
        errmsg                                          = c_char_p() 
        ret = self.miTLS.FFI_mitls_quic_get_exporter(   self.mitlsQuicState,
                                                        early,
                                                        quicSecret_c,
                                                        byref( errmsg ) )
        self.PrintMsgIfNotNull( None, errmsg )
        self.VerifyResult( "FFI_mitls_quic_get_exporter", ret )

        return quicSecret

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
        self.log.debug( "Send: %s; self.mitls_state = %s" % (payload, self.mitls_state  ) )
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
        if os.path.exists(LOG_FILE):
            os.remove( LOG_FILE )
        tee      = subprocess.Popen(["tee", LOG_FILE ], stdin=subprocess.PIPE )
        os.dup2(tee.stdin.fileno(), sys.stdout.fileno())

        
        # sys.stdout.close()
        # sys.stderr.close()
        # os.dup2(tee.stdout.fileno(), devNull)

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
        PATTERN  = r"(\S+) key\[(.)\]:(.+), IV=(.+)"
        PATTERN2 = r"(\S+) (0-RTT) key:(.+), IV=(.+)"

        MSG_FILENAME    = "%s-%s-keys-mitls.%d"
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
                    result = re.search( PATTERN2, line )
                if result is None:
                    continue

                purpose = result.groups()[ 0 ].strip()
                entity  = result.groups()[ 1 ].strip()
                rawKey  = result.groups()[ 2 ].strip()
                rawIV   = result.groups()[ 3 ].strip()
                IV  = "".join( map( lambda x: "0x%s, " % x , self.ChopStringToBytes( rawIV ) ) )
                key = "".join( map( lambda x: "0x%s, " % x , self.ChopStringToBytes( rawKey ) ) )

                filePath = keyFilePath % (purpose, entity, keyIdx)
                with open( filePath, "w" ) as keyFile:
                    keyFile.write( "IV: %s\n" % IV )
                    keyFile.write( "KEY: %s\n" % key )                    
                    keyIdx += 1

                    if config.LOG_LEVEL < logging.ERROR:
                    	sys.stdout.write( "Dumped key to %s\n" % filePath )

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

    def StartQUICServerThread( 	self, 
	                            supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
	                            supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
	                            supportedNamedGroups            = SUPPORTED_NAMED_GROUPS,
	                            applicationData                 = None ):
        self.tlsServer = MITLS( "QUIC-server" )
        self.tlsServer.InitQUICServer(  supportedCipherSuites, 
	                                    supportedSignatureAlgorithms, 
	                                    supportedNamedGroups )
        
        serverThread   = threading.Thread(target = self.tlsServer.AcceptQUICConnection, args = [ applicationData ] )
        serverThread.start()

        return serverThread

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

    def test_QUIC_parameters_matrix( self ):
        sys.stderr.write( "Running test_QUIC_parameters_matrix\n" )
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "parameters_matrix_QUIC.csv", "w" ) as logFile:
            outputSinks = [ sys.stderr, logFile ]
            self.WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s %-15s%-6s\n" % ("CipherSuite,", "SignatureAlgorithm,", "NamedGroup,", "PassFail,", "Time (seconds)") )

            for cipherSuite in SUPPORTED_CIPHER_SUITES:
                for algorithm in SUPPORTED_SIGNATURE_ALGORITHMS:
                    for group in SUPPORTED_NAMED_GROUPS:
                        self.WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s " % ( cipherSuite+",", algorithm+",", group+"," ) )

                        memorySocket.tlsParser.DeleteLeakedKeys()
                        try:
                            startTime = time.time()
                            self.RunSingleQUICTest( supportedCipherSuites        = [ cipherSuite ],
                                                    supportedSignatureAlgorithms = [ algorithm ],
                                                    supportedNamedGroups         = [ group ] )
                            self.WriteToMultipleSinks( outputSinks, "%-15s" % ("OK,") )
                        except Exception as err: 
                            pprint( traceback.format_tb( err.__traceback__ ) )
                            print( err )
                            self.WriteToMultipleSinks( outputSinks, "%-15s" % "FAILED," )
                        finally:
                            totalTime = time.time() - startTime
                            self.WriteToMultipleSinks( outputSinks, "%-6f\n" % totalTime )
                            time.sleep(0.2)
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()    

    def test_MITLS_QUIC_ClientAndServer( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        preExistingKeys = memorySocket.tlsParser.FindMatchingKeys()
        try:
            self.RunSingleQUICTest()
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()
            
        if config.LOG_LEVEL < logging.ERROR:
            # pprint( memorySocket.tlsParser.transcript )
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )

            keysAndFiles = memorySocket.tlsParser.FindNewKeys( preExistingKeys )
            pprint( keysAndFiles )

        # self.log.debug( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        # self.log.debug( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )
        return memorySocket.tlsParser.transcript

    def test_MITLS_QUIC_ClientAndServer_sessionResumption( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        preExistingKeys = memorySocket.tlsParser.FindMatchingKeys()
        try:
            sessionTicket   = self.RunSingleQUICTest(  ) 
            firstSession    = memorySocket.tlsParser.transcript[ : ]
            self.RunSingleQUICTest( quicSessionTicket = sessionTicket ) 
            entireTranscipt = firstSession + memorySocket.tlsParser.transcript
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()
            
        print( "============= client EARLY secret ===============")
        print( TLSParser.FormatBuffer( self.tlsClient.quicEarlySecret ))
        print( "============= server EARLY secret ===============")
        print( TLSParser.FormatBuffer( self.tlsServer.quicEarlySecret ))

        if config.LOG_LEVEL < logging.ERROR:
            # pprint( memorySocket.tlsParser.transcript )
            for msg in entireTranscipt:
                memorySocket.tlsParser.PrintMsg( msg )

            keysAndFiles = memorySocket.tlsParser.FindNewKeys( preExistingKeys )
            pprint( keysAndFiles )

        # self.log.debug( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        # self.log.debug( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )
        return memorySocket.tlsParser.transcript

    def test_MITLS_ClientAndServer( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        preExistingKeys = memorySocket.tlsParser.FindMatchingKeys()
        try:
            self.RunSingleTest()
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()
            
        if config.LOG_LEVEL < logging.ERROR:
            # pprint( memorySocket.tlsParser.transcript )
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )
                # if tlsparser.IV_AND_KEY in msg.keys():
                #     pprint( msg[ tlsparser.IV_AND_KEY ])

            keysAndFiles = memorySocket.tlsParser.FindNewKeys( preExistingKeys )
            pprint( keysAndFiles )

        self.log.debug( "self.tlsServer.dataReceived = %s" % self.tlsServer.dataReceived )
        self.log.debug( "self.tlsClient.dataReceived = %s" % self.tlsClient.dataReceived )

        # TLSParser.DumpTranscript( memorySocket.tlsParser.transcript )
        return memorySocket.tlsParser.transcript

    # def test_ReorderCipherSuites( self ):
    #     testsToRun.append( "ClientServerTest" )
    #     transcript               = self.test_MITLS_ClientAndServer()
    #     msg0                     = transcript[ 0 ]
    #     msg1                     = transcript[ 1 ]

    #     manipulation = AttrDict( { HANDSHAKE_TYPE : HANDSHAKE_TYPE_CLIENT_HELLO,
    #                                PARENT_NODE    : CIPHER_SUITES,
    #                                SWAP_ITEMS     : AttrDict( { 'index1' : 0, 'index2' : -1 } ) })
    #     tlsParser = tlsparser.TLSParser()
    #     manipulatedMsg = tlsParser.ManipulateMsg( msg1, manipulation )
    #     self.assertTrue( manipulatedMsg == None )

    #     manipulatedMsg = tlsParser.ManipulateMsg( msg0, manipulation )

    #     print( "==================== Original Message =====================")
    #     tlsParser.PrintMsg( msg0 )

    #     # print( "==================== Manipulated Message =====================")
    #     # tlsParser.PrintMsg( manipulatedMsg )

    #     print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
    #     rawMsg = tlsParser.ReconstructRecordAndCompareToOriginal( manipulatedMsg, doCompare = False )
        
    #     # The following will print the message as a side effect
    #     parsedManipulatedMsg = tlsParser.Digest( rawMsg, manipulatedMsg[ DIRECTION ] )

    #     # tlsParser.PrintMsg( parsedManipulatedMsg )


    # def test_ReorderCipherSuites_onWire( self ):
    #     manipulation = AttrDict( { HANDSHAKE_TYPE : HANDSHAKE_TYPE_CLIENT_HELLO,
    #                                PARENT_NODE    : CIPHER_SUITES,
    #                                SWAP_ITEMS     : AttrDict( { 'index1' : 1, 'index2' : 2 } ) })
        
    #     keysMonitor = MonitorLeakedKeys()
    #     keysMonitor.MonitorStdoutForLeakedKeys()

    #     exceptionThrown = False
    #     try:
    #         self.RunSingleTest( msgManipulators = [ manipulation ] )
    #     except:
    #         exceptionThrown = True
    #         traceback.print_exc()

    #     keysMonitor.StopMonitorStdoutForLeakedKeys()

    #     self.assertTrue( exceptionThrown == True )

    #     for msg in  memorySocket.tlsParser.transcript:
    #         print( "Direction: %s, type = %s" % (msg[ DIRECTION ], msg[ RECORD_TYPE ] ) )

    def CreateShuffleChildrenManipulations( self, node, handshakeType ):
        shuffleManipulations = []
        if node.Name in PIECES_THAT_CANT_BE_SHUFFLED:
            return shuffleManipulations

        numberOfChildren = len( node.Interpretation )
        for i in range( numberOfChildren - 1 ):
            shuffleManipulations.append( AttrDict( {   HANDSHAKE_TYPE : handshakeType,
                                                       PARENT_NODE    : node.Name,
                                                       SWAP_ITEMS     : AttrDict( { 'index1' : i, 'index2' : i + 1 } ),
                                                       # "Description"  : "Swapping  children of %s: %s <--> %s" % ( node.Name, index1Name, index2Name ), 
                                                       }) )

        # pprint( shuffleManipulations )
        return shuffleManipulations

    def CreateSkipPieceManipulations( self, node, handshakeType ):
        skipManipulations = []
        if node.Name in PIECES_THAT_CANT_BE_SKIPPED:
            return skipManipulations

        numberOfChildren = len( node.Interpretation )
        for i in range( numberOfChildren ):
            skipManipulations.append( AttrDict( {  HANDSHAKE_TYPE : handshakeType,
                                                   PARENT_NODE    : node.Name,
                                                   REMOVE_ITEM    : i } ) )

        # pprint( shuffleManipulations )
        return skipManipulations

    def CreateTopLevelShuffleManipulations( self, record, direction ):
        shuffleManipulations = []

        numberOfChildren = len( record )
        for i in range( numberOfChildren - 1 ):
            shuffleManipulations.append( AttrDict( {   DIRECTION      : direction,
                                                       PARENT_NODE    : RECORD,
                                                       SWAP_ITEMS     : AttrDict( { 'index1' : i, 'index2' : i + 1 } ) }) )

        # pprint( shuffleManipulations )
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

    def GetClientHelloReorderManipulations( self, runHandshake = None ):
        if runHandshake is  None:
            runHandshake = self.RunSingleTest
       
        runHandshake()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateShuffleChildrenManipulations,  
                                                                                                handshakeType = handshakeType )   )

        return manipulations

    def GetClientHelloSkipManipulations( self, runHandshake = None ):
        if runHandshake is  None:
            runHandshake = self.RunSingleTest
       
        runHandshake()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateSkipPieceManipulations,  
                                                                                                handshakeType = handshakeType )   )

        return manipulations

    def GetServerEncryptedHelloReorderManipulations( self, runHandshake = None ):
        if runHandshake is  None:
            runHandshake = self.RunSingleTest
       
        runHandshake()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateShuffleChildrenManipulations,  
                                                                                                handshakeType = handshakeType )   )

        return manipulations

    def GetServerReorderHandshakesManipulations( self, runHandshake = None ):
        if runHandshake is  None:
            runHandshake = self.RunSingleTest
       
        runHandshake()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.CreateTopLevelShuffleManipulations( originalTranscript[ 2 ][ RECORD ], Direction.SERVER_TO_CLIENT )

        return manipulations

    def GetServerSkipPiecesManipulations( self, runHandshake = None ):
        if runHandshake is  None:
            runHandshake = self.RunSingleTest
       
        runHandshake()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        numHandshakes       = len( originalTranscript[ 2 ][ RECORD ] )

        manipulations = []
        for handshakeIdx in range( numHandshakes ):
            topTreeLayer        = originalTranscript[ 2 ][ RECORD ][ handshakeIdx ][ HANDSHAKE_MSG ] 
            handshakeType       = originalTranscript[ 2 ][ RECORD ][ handshakeIdx ][ HANDSHAKE_TYPE ]
            manipulations      += self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateSkipPieceManipulations,  
                                                                                                    handshakeType = handshakeType )   )

        return manipulations

    def GetServerExtractPiecesToPlaintextManipulations( self ):
        handshakesToExtarct = [ HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS,
                                HANDSHAKE_TYPE_CERTIFICATE         ,
                                HANDSHAKE_TYPE_CERTIFICATE_VERIFY  ,
                                HANDSHAKE_TYPE_FINISHED            ]

        manipulations = []
        for handshakeType in handshakesToExtarct:
            manipulations.append( AttrDict( {  DIRECTION                : Direction.SERVER_TO_CLIENT,
                                               PARENT_NODE              : RECORD,
                                               EXTRACT_TO_PLAINTEXT     : True,
                                               HANDSHAKE_TYPE           : handshakeType }) )

        return manipulations

    def test_ReorderPieces_ClientHello_onWire( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        
        manipulations = self.GetClientHelloReorderManipulations()
        experiments   = self.RunManipulationTest( manipulations, numExpectedSharedKeys = 0, numExpectedAlerts = 0 )
        keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( experiments )

        # for manipulation in manipulations:
        #     msg0      = originalTranscript[ 0 ]
        #     tlsParser = TLSParser()
        #     print( "###############################################")
        #     pprint( manipulation )
        #     print( "==================== Original Message =====================")
        #     tlsParser.PrintMsg( msg0 )

        #     print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
        #     manipulatedMsg = tlsParser.ManipulateMsg( msg0, manipulation )
        #     rawMsg         = tlsParser.ReconstructRecordAndCompareToOriginal( manipulatedMsg, doCompare = False )
            
        #     # The following will print the message as a side effect
        #     parsedManipulatedMsg = tlsParser.Digest( rawMsg, manipulatedMsg[ DIRECTION ] )

    def GetAbbreviatedTranscript( self, transcript ):
        abbreviatedTranscript = []
        for msg in transcript:
            isEncrypted = ""
            if msg[ RECORD_TYPE ] == TLS_RECORD_TYPE_APP_DATA:
                isEncrypted = "(Enc)"

            if msg[ DIRECTION ] == Direction.CLIENT_TO_SERVER:
                direction = "-%s-> " % isEncrypted
            else:
                direction = "<-%s- " % isEncrypted

            if ALERT in msg.keys():
                content = "Alert( %s );" % msg[ ALERT ][ 'Type' ]
            
            elif TLSParser.IsMsgContainsOnlyAppData( msg ):
                content = "<app data>;"

            else:
                content = ""
                for handshakeMsg in msg[ RECORD ]:
                    content += TLSParser.GetHandshakeType( handshakeMsg[ HANDSHAKE_TYPE ] ) + ";"

            abbreviatedTranscript.append( direction + content )

        return abbreviatedTranscript

    def RunManipulationTest(    self, 
                                manipulations, 
                                numExpectedSharedKeys, 
                                assertExceptionThrown   = True, 
                                numExpectedAlerts       = None,
                                runTestFunction         = None ):
        if runTestFunction is None:
            runTestFunction = self.RunSingleTest

        experiments = []
        for manipulation in manipulations:
            self.log.debug( "manipulation = %s" % manipulation)

            exceptionThrown = False
            try:
                preExistingKeys     = memorySocket.tlsParser.FindMatchingKeys()
                runTestFunction( msgManipulators = [ manipulation ] )
            except:
                exceptionThrown = True
                traceback.print_exc()

            time.sleep( 1 ) #wait for messages to reach transcript
            keysAndFiles               = memorySocket.tlsParser.FindNewKeys( preExistingKeys )
            numFilesPerKey             = map( lambda key : len( keysAndFiles[ key ] ), keysAndFiles.keys() )
            numKeysWithMoreThanOneFile = sum( i > 1 for i in numFilesPerKey )

            IsMsgEncrypted             = lambda msg : " (encrypted)" if ( msg[ RECORD_TYPE ] == TLS_RECORD_TYPE_APP_DATA ) else ""
            alerts                     = list( map( lambda msg : "%s%s: %s" % ( msg[ DIRECTION ], 
                                                                                IsMsgEncrypted( msg ), 
                                                                                msg[ ALERT ][ 'Type' ]), 
                                                     memorySocket.tlsParser.GetAlerts() ) )            
            abbreviatedTranscript      = self.GetAbbreviatedTranscript( memorySocket.tlsParser.transcript )

            thisExperiment = AttrDict( {'Manipulation'         : manipulation, 
                                        'Keys'                 : keysAndFiles, 
                                        'NumKeys'              : len( keysAndFiles.keys() ),
                                        'SuccessfulSharedKeys' : numKeysWithMoreThanOneFile,
                                        'Alerts'               : alerts,
                                        'Transcript'           : abbreviatedTranscript } )
            experiments.append( deepcopy( thisExperiment ) )

            # Asserts:
            if assertExceptionThrown:
                self.assertTrue( exceptionThrown == True )
            if numExpectedAlerts != None:
                self.assertTrue( len( thisExperiment.Alerts ) == numExpectedAlerts )
            if numExpectedSharedKeys != None:
                self.assertTrue( thisExperiment.SuccessfulSharedKeys == numExpectedSharedKeys, msg = pformat( thisExperiment ) ) 

            # # allow stdout to be flushed and read by keysMonitor
            # time.sleep(0.5) 

        return experiments

    def test_SkipPieces_ClientHello_onWire( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        self.RunSingleTest()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 0 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateSkipPieceManipulations,  
                                                                                                handshakeType = handshakeType )   )
        experiments = self.RunManipulationTest( manipulations, numExpectedSharedKeys = 0 )
        keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( experiments )

        # for manipulation in manipulations:
        #     msg0      = originalTranscript[ 0 ]
        #     tlsParser = TLSParser()
        #     print( "###############################################")
        #     pprint( manipulation )
        #     print( "==================== Original Message =====================")
        #     tlsParser.PrintMsg( msg0 )
        #     memorySocket.tlsParser.SetMsgManipulators( [ manipulation ] )
        #     print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
        #     rawMsg = memorySocket.tlsParser.ManipulateAndReconstruct( msg0 )
        #     # The following will print the message as a side effect
        #     parsedManipulatedMsg = tlsParser.Digest( rawMsg, msg0[ DIRECTION ] )

    def test_SkipPieces_ServerHello_onWire( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        self.RunSingleTest()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 1 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 1 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateSkipPieceManipulations,  
                                                                                                handshakeType = handshakeType )   )
        experiments = self.RunManipulationTest( manipulations, numExpectedSharedKeys = 0 )
        keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( experiments )
        # time.sleep(2)
        # pprint( manipulations )
        # for manipulation in manipulations:
        #     msg0      = originalTranscript[ 1 ]
        #     tlsParser = TLSParser()
        #     print( "###############################################")
        #     pprint( manipulation )
        #     print( "==================== Original Message =====================")
        #     tlsParser.PrintMsg( msg0 )
        #     memorySocket.tlsParser.SetMsgManipulators( [ manipulation ] )
        #     print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
        #     rawMsg = memorySocket.tlsParser.ManipulateAndReconstruct( msg0 )
        #     # The following will print the message as a side effect
        #     parsedManipulatedMsg = tlsParser.Digest( rawMsg, msg0[ DIRECTION ] )

    def test_SkipPieces_EncryptedServerHello_onWire( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        self.RunSingleTest()
        
        originalTranscript  = memorySocket.tlsParser.transcript
        numHandshakes = len( originalTranscript[ 2 ][ RECORD ] )

        manipulations = []
        for handshakeIdx in range( numHandshakes ):
            topTreeLayer        = originalTranscript[ 2 ][ RECORD ][ handshakeIdx ][ HANDSHAKE_MSG ] 
            handshakeType       = originalTranscript[ 2 ][ RECORD ][ handshakeIdx ][ HANDSHAKE_TYPE ]
            manipulations      += self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateSkipPieceManipulations,  
                                                                                                    handshakeType = handshakeType )   )
        try:
            experiments = self.RunManipulationTest( manipulations, numExpectedSharedKeys = 2 )
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( experiments )

    def test_ReorderPieces_ServerEncryptedHello_onWire( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        self.RunSingleTest()

        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.TraverseBFSAndGenerateManipulations( topTreeLayer, partial(  self.CreateShuffleChildrenManipulations,  
                                                                                                handshakeType = handshakeType )   )
        try:
            experiments = self.RunManipulationTest( manipulations, numExpectedSharedKeys = 2 )
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( experiments )

        # for manipulation in manipulations:
        #     pprint( manipulation )
        #     msg2      = originalTranscript[ 2 ]
        #     tlsParser = TLSParser()
        #     print( "###############################################")
        #     pprint( manipulation )
        #     print( "==================== Original Message =====================")
        #     tlsParser.PrintMsg( msg2 )

        #     print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
        #     manipulatedMsg = tlsParser.ManipulateMsg( msg2, manipulation )
        #     rawMsg         = memorySocket.tlsParser.ReconstructRecordAndCompareToOriginal( manipulatedMsg, doCompare = False )
            
        #     # The following will print the message as a side effect
        #     parsedManipulatedMsg = memorySocket.tlsParser.Digest( rawMsg, manipulatedMsg[ DIRECTION ], ivAndKey = msg2[ IV_AND_KEY ] )



    def test_ReorderPieces_ServerEncryptedHello_shuffleHandshakesOrder_onWire( self ):    
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        self.RunSingleTest()

        originalTranscript  = memorySocket.tlsParser.transcript
        topTreeLayer        = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_MSG ] 
        handshakeType       = originalTranscript[ 2 ][ RECORD ][ 0 ][ HANDSHAKE_TYPE ]
        manipulations       = self.CreateTopLevelShuffleManipulations( originalTranscript[ 2 ][ RECORD ], Direction.SERVER_TO_CLIENT )
        
        try:
            experiments = self.RunManipulationTest( manipulations, numExpectedSharedKeys = 2 )
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( experiments )

    def test_ServerEncryptedHello_extractToPlaintext( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()
        self.RunSingleTest()
        
        handshakesToExtarct = [ HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS,
                                HANDSHAKE_TYPE_CERTIFICATE         ,
                                HANDSHAKE_TYPE_CERTIFICATE_VERIFY  ,
                                HANDSHAKE_TYPE_FINISHED            ]

        manipulations = []
        for handshakeType in handshakesToExtarct:
            manipulations.append( AttrDict( {  DIRECTION                : Direction.SERVER_TO_CLIENT,
                                               PARENT_NODE              : RECORD,
                                               EXTRACT_TO_PLAINTEXT     : True,
                                               HANDSHAKE_TYPE           : handshakeType }) )

        try:
            experiments = self.RunManipulationTest( manipulations, numExpectedSharedKeys = 2 )
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()
            
        pprint( experiments )

        # for manipulation in manipulations:
        #     pprint( manipulation )
        #     msg2      = originalTranscript[ 2 ]
        #     # memorySocket.tlsParser = TLSParser()
        #     memorySocket.tlsParser.SetMsgManipulators( [ manipulation ] )
        #     print( "###############################################")
        #     pprint( manipulation )
        #     print( "==================== Original Message =====================")
        #     memorySocket.tlsParser.PrintMsg( msg2 )

        #     print( "==================== Manipulated Message  =====================")
        #     rawMsg = memorySocket.tlsParser.ManipulateAndReconstruct( msg2 )
        #     # rawMsg         = memorySocket.tlsParser.ReconstructRecordAndCompareToOriginal( manipulatedMsg, doCompare = False )
            
        #     memorySocket.tlsParser.SetMsgManipulators( [] )
        #     # The following will print the message as a side effect
        #     print( "==================== Manipulated Message after reconstructing and re-parsing =====================")
        #     parsedManipulatedMsg = memorySocket.tlsParser.Digest( rawMsg, msg2[ DIRECTION ], ivAndKey = msg2[ IV_AND_KEY ] )


    def RemoveItemAndSplit( self, itemList, itemToRemove ):
        otherItems = itemList[ : ]
        otherItems.remove( itemToRemove )
        numItems   = len( otherItems )
        listA      = otherItems[ : numItems // 2 ]
        listB      = otherItems[ numItems // 2 : ] 

        return listA, listB

    def RunSingleQUICTest( 	self , 
	                        supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
	                        supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
	                        supportedNamedGroups            = SUPPORTED_NAMED_GROUPS,
	                        applicationData                 = None,
	                        msgManipulators                 = [],
                            quicSessionTicket              = None ):
        memorySocket.FlushBuffers()
        memorySocket.tlsParser = tlsparser.TLSParser()
        memorySocket.tlsParser.SetMsgManipulators( msgManipulators )
        serverThread = self.StartQUICServerThread(  supportedCipherSuites,
                                                    supportedSignatureAlgorithms,
                                                    supportedNamedGroups,
                                                    applicationData )

        self.tlsClient = MITLS( "QUIC-client" )
        self.tlsClient.InitQUICClient(  "test_server.com", 
                                        supportedCipherSuites,
                                        supportedSignatureAlgorithms,
                                        supportedNamedGroups,
                                        quicSessionTicket )
        quicSessionTicket = self.tlsClient.QUICConnect()
        # self.tlsClient.Send( b"Client->Server\x00" )            
        # self.tlsClient.dataReceived = self.tlsClient.Receive()

        serverThread.join()
        
        clientSecret = self.tlsClient.GetQUICSecret( isEarlyData = False )
        serverSecret = self.tlsServer.GetQUICSecret( isEarlyData = False )

        # print( "============= client secret ===============")
        # print( TLSParser.FormatBuffer( clientSecret ))
        # print( "============= server secret ===============")
        # print( TLSParser.FormatBuffer( serverSecret ))
        # print( "============= client ticket ===============")
        # print( TLSParser.FormatBuffer( self.tlsClient.quicSessionTicket ) )

        self.tlsClient.QUICCleanup()
        self.tlsServer.QUICCleanup()

        if self.tlsServer.acceptConnectionSucceeded == False:
            raise Exception( "QUIC Server failed to connect" )

        if clientSecret != serverSecret:
            raise Exception( "QUIC secrets are different" )

        if self.tlsClient.quicEarlySecret != None:
            if self.tlsClient.quicEarlySecret != self.tlsServer.quicEarlySecret:
                raise Exception( "QUIC EARLY secrets are different" )                

        return quicSessionTicket

    def RunSingleTest(  self, 
                        supportedCipherSuites           = SUPPORTED_CIPHER_SUITES,
                        supportedSignatureAlgorithms    = SUPPORTED_SIGNATURE_ALGORITHMS,
                        supportedNamedGroups            = SUPPORTED_NAMED_GROUPS,
                        applicationData                 = None,
                        msgManipulators                 = [] ):

        memorySocket.FlushBuffers()
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

    @staticmethod
    def WriteToMultipleSinks( sinks, msg ):
        for sink in sinks:
            sink.write( msg )
            sink.flush()

    def test_NamedGroups( self ):
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

    def test_parameters_matrix( self ):
        sys.stderr.write( "Running test_parameters_matrix\n" )
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "parameters_matrix_MITLS_MITLS.csv", "w" ) as logFile:
            outputSinks = [ sys.stderr, logFile ]
            self.WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s %-15s%-6s\n" % ("CipherSuite,", "SignatureAlgorithm,", "NamedGroup,", "PassFail,", "Time (seconds)") )

            for cipherSuite in SUPPORTED_CIPHER_SUITES:
                for algorithm in SUPPORTED_SIGNATURE_ALGORITHMS:
                    for group in SUPPORTED_NAMED_GROUPS:
                        self.WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s " % ( cipherSuite+",", algorithm+",", group+"," ) )

                        memorySocket.tlsParser.DeleteLeakedKeys()
                        try:
                            startTime = time.time()
                            self.RunSingleTest( supportedCipherSuites        = [ cipherSuite ],
                                                supportedSignatureAlgorithms = [ algorithm ],
                                                supportedNamedGroups         = [ group ] )
                            self.WriteToMultipleSinks( outputSinks, "%-15s" % ("OK,") )
                        except Exception as err: 
                            print( traceback.format_tb( err.__traceback__ ) )
                            self.WriteToMultipleSinks( outputSinks, "%-15s" % "FAILED," )
                        finally:
                            totalTime = time.time() - startTime
                            self.WriteToMultipleSinks( outputSinks, "%-6f\n" % totalTime )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()    

    def test_CipherSuites( self ):
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
    parser.add_argument("-s", "--supress_output", help="turn off verbosity", action='store_true' )
    parser.add_argument("--mitls_so_path", help="full path_to_libmitls.so")
    parser.add_argument("--srv_cert_path", help="full path_to_server_cert_file")
    parser.add_argument("--srv_key_path",  help="full path_to_server_key_path")
    parser.add_argument("--srv_ca_path",   help="full path_to_server_ca_path")
    parser.add_argument("--openssl_path",  help="full path_to_openssl.lib")
    parser.add_argument("unittest_args", nargs="*")
    
def HandleMITLSArguments( args ):
    if args.mitls_so_path:
        config.set_mitls_so_path(args.mitls_so_path)

    if args.supress_output:
        SUPRESS_ALL_LOGS = 100
        config.set_log_level( SUPRESS_ALL_LOGS )

        memorySocket.tlsParser.log.setLevel( config.LOG_LEVEL )


from output_redirector import stdout_redirector
if __name__ == '__main__':
    # SI: argparse seems not to complete before unitest.main starts running? 
    # usage = "usage: %prog [options] arg"
    parser = argparse.ArgumentParser()
    ConfigureMITLSArguments( parser )
    
    args   = parser.parse_args()
    HandleMITLSArguments( args )
    memorySocket.log.setLevel( config.LOG_LEVEL )   

    # SI: reset args, else unittest.main complains of flags not being valid.
    sys.argv[1:] = args.unittest_args

    # SI: these should be args. 
    suite = unittest.TestSuite()
    
    # suite.addTest( MITLSTester('test_MITLS_ClientAndServer' ) )
    # suite.addTest( MITLSTester('test_MITLS_QUIC_ClientAndServer' ) )
    # suite.addTest( MITLSTester('test_parameters_matrix' ) )
    # suite.addTest( MITLSTester('test_QUIC_parameters_matrix' ) )
    suite.addTest( MITLSTester('test_MITLS_QUIC_ClientAndServer_sessionResumption' ) )

    # suite.addTest( MITLSTester( "test_CipherSuites" ) )
    # suite.addTest( MITLSTester( "test_SignatureAlgorithms" ) )
    # suite.addTest( MITLSTester( "test_NamedGroups" ) )
    # suite.addTest( MITLSTester( "test_ReorderPieces_ClientHello_onWire" ) )
    # suite.addTest( MITLSTester( "test_ReorderPieces_ServerEncryptedHello_onWire" ) )
    # suite.addTest( MITLSTester( "test_ReorderPieces_ServerEncryptedHello_shuffleHandshakesOrder_onWire" ) )
    # suite.addTest( MITLSTester( "test_ServerEncryptedHello_extractToPlaintext" ) )
    # suite.addTest( MITLSTester( "test_SkipPieces_ClientHello_onWire" ) )
    # suite.addTest( MITLSTester( "test_SkipPieces_ServerHello_onWire" ) )
    # suite.addTest( MITLSTester( "test_SkipPieces_EncryptedServerHello_onWire" ) )
    
     
    runner = unittest.TextTestRunner()
    
    if args.supress_output:
        devNull = open( "/dev/null", "wb" )
        with stdout_redirector( devNull ):
            runner.run(suite)
    else:
        runner.run(suite)


