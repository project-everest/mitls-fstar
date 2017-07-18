import logging
import unittest
import os
import time
import threading
import sys
import glob
import cutils
import config

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

OPENSSL_SUCCESS           = 1 
SIZE_OF_METHODS 		  = 96
SIZE_OF_VOID_P            = 8
METHODS_NUM_POINTERS 	  = int( SIZE_OF_METHODS / SIZE_OF_VOID_P )

BIO_TYPE_SOCKET 		  = 0x505
SOCKET_NAME 			  = "socket"

METHODS_TYPE			= 0
METHODS_NAME			= 1
METHODS_WRITE			= 2
METHODS_WRITE_OLD		= 3	
METHODS_READ			= 4
METHODS_READ_OLD		= 5	
METHODS_PUTS			= 6
METHODS_GETS			= 7
METHODS_CTRL			= 8
METHODS_CREATE			= 9
METHODS_DESTROY			= 10
METHODS_CALLBACK_CTRL	= 11		


globalLibSSL            = CDLL( config.OPENSSL_PATH )
globalDescriptorTable   = {}

def CString( pythonString ):
    NULL_BYTE = b"\0"
    return c_char_p( bytes( pythonString, "ascii" ) + NULL_BYTE )

class BIOWrapperError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

def BIO_set_fd( bio, fd, flags ):
    # print( "BIO_set_fd; bio = %s, fd = %s, flags = %s" % ( bio, fd, flags ))
    BIO_C_SET_FD = c_int( 104 )

    globalLibSSL.BIO_int_ctrl.restype  = c_long
    globalLibSSL.BIO_int_ctrl.argtypes = [ c_voidp, c_int, c_long, c_int ]

    return globalLibSSL.BIO_int_ctrl( bio, BIO_C_SET_FD, c_long( flags ), c_int( fd ) )

def WriteConverterCallbak( bio, buffer, bufferSize, written ):
    # print( "WriteConverterCallbak; fileDescriptor = %s" % bio )
    bytesWritten      = ( c_long * 1 ).from_address( written )
    bioWrapper        = globalDescriptorTable[ bio ]
    bytesWritten[ 0 ] = bioWrapper.WriteCallback( None, buffer, bufferSize )

    return OPENSSL_SUCCESS

def ReadConverterCallbak( bio, buffer, bufferSize, readbytes ):
    # print( "ReadConverterCallbak" )
 
    bytesRead = ( c_long * 1 ).from_address( readbytes )

    print( "fileDescriptor = %s" % bio )
    bioWrapper     = globalDescriptorTable[ bio ]
    bytesRead[ 0 ] = bioWrapper.ReadCallback( None, buffer, bufferSize )

    return OPENSSL_SUCCESS

def PutsCallback( bio, str ):
    print( "PutsCallback" )

    fileDescriptor = BIO_get_fd( c_voidp( bio ) )
    print( "fileDescriptor = %s" % fileDescriptor )

    raise BIOWrapperError( "Unexpected call" )

def SockCtrlCallback( bio, cmd, num, ptr ):
    # print( "SockCtrlCallback: bio = %s, cmd = %s, num = %s, ptr = %s" % ( bio, cmd, num, ptr ) )

    globalCUtils.sock_ctrl.restype  = c_long
    globalCUtils.sock_ctrl.argtypes = [ c_voidp, c_int, c_long, c_voidp ]
    return globalCUtils.sock_ctrl( bio, c_int( cmd ), c_long( num ), ptr )

def SockNewCallback( bio ):
    # print( "SockNewCallback" )

    globalDescriptorTable[ bio ] = None

    globalCUtils.sock_new.restype =    c_int
    globalCUtils.sock_new.argtypes = [ c_voidp ]

    return globalCUtils.sock_new( bio )

def SockFreeCallback( bio ):
    print( "SockFreeCallback" )

    fileDescriptor = BIO_get_fd( c_voidp( bio ) )
    print( "fileDescriptor = %s" % fileDescriptor )

    raise BIOWrapperError( "Unexpected call" )

def ReadCallback( ctx, buffer, bufferSize ):
    print( "ReadCallback" )

    fileDescriptor = BIO_get_fd( c_voidp( ctx ) )
    print( "fileDescriptor = %s" % fileDescriptor )

    return globalDescriptorTable[ fileDescriptor ].ReadCallback( None, buffer, bufferSize )

def WriteCallback( ctx, buffer, bufferSize ):
    print( "ReadCallback" )

    fileDescriptor = BIO_get_fd( c_voidp( ctx ) )
    print( "fileDescriptor = %s" % fileDescriptor )

    return globalDescriptorTable[ fileDescriptor ].WriteCallback( None, buffer, bufferSize )

class BIOWrapper():
    def __init__( self ):
        self.libssl    = CDLL( config.OPENSSL_PATH )
        self.cutils    = globalCUtils
        
        self.cutils = cutils.GetObject()
        self.cutils.getAddress.restype = c_voidp

        self.ReadCallback   = None
        self.WriteCallback  = None

        self.SetupBIOMethods()
        self.RegisterBIOMethods()

    def SetupBIOMethods( self ):
        WRITE_CONVERSION_CALLBACK 		= CFUNCTYPE( c_int, c_voidp, c_voidp, c_long, c_voidp ) 
        self.writeConverterCallback 	= WRITE_CONVERSION_CALLBACK( WriteConverterCallbak )

        WRITE_CALLBACK                  = CFUNCTYPE( c_int, c_voidp, c_voidp, c_int ) 
        self.writeCallback              = WRITE_CALLBACK( WriteCallback )

        READ_CONVERSION_CALLBACK 		= CFUNCTYPE( c_int, c_voidp, c_voidp, c_long, c_voidp ) 
        self.readConverterCallback 		= READ_CONVERSION_CALLBACK( ReadConverterCallbak )

        READ_CALLBACK                   = CFUNCTYPE( c_int, c_voidp, c_voidp, c_int ) 
        self.readCallback               = READ_CALLBACK( ReadCallback )

        PUTS_CALLBACK                   = CFUNCTYPE( c_int, c_voidp, c_voidp ) 
        self.putsCallback               = PUTS_CALLBACK( PutsCallback )

        SOCK_CTRL_CALLBACK              = CFUNCTYPE( c_long, c_voidp, c_int, c_long, c_voidp ) 
        self.sockCtrlCallback           = SOCK_CTRL_CALLBACK( SockCtrlCallback )

        SOCK_NEW_CALLBACK               = CFUNCTYPE( c_int, c_voidp ) 
        self.sockNewCallback            = SOCK_NEW_CALLBACK( SockNewCallback )

        SOCK_FREE_CALLBACK              = CFUNCTYPE( c_int, c_voidp ) 
        self.sockFreeCallback           = SOCK_FREE_CALLBACK( SockFreeCallback )


        self.BIOMethods = (c_voidp * METHODS_NUM_POINTERS )()
        self.BIOMethods[ METHODS_TYPE     	 ]       = c_voidp( BIO_TYPE_SOCKET )
        self.BIOMethods[ METHODS_NAME     	 ]       = globalCUtils.duplicateString( CString( SOCKET_NAME ), len( SOCKET_NAME ) + 1)
        self.BIOMethods[ METHODS_WRITE    	 ]       = self.cutils.getAddress( self.writeConverterCallback ) #int bwrite_conv(BIO *bio, const char *data, size_t datal, size_t *written)
        self.BIOMethods[ METHODS_WRITE_OLD	 ]       = self.cutils.getAddress( self.writeCallback )
        self.BIOMethods[ METHODS_READ		 ]       = self.cutils.getAddress( self.readConverterCallback ) #int bread_conv(BIO *bio, char *data, size_t datal, size_t *readbytes)
        self.BIOMethods[ METHODS_READ_OLD	 ]       = self.cutils.getAddress( self.readCallback )
        self.BIOMethods[ METHODS_PUTS		 ]       = self.cutils.getAddress( self.putsCallback ) #int sock_puts(BIO *bp, const char *str)
        self.BIOMethods[ METHODS_GETS		 ]       = None
        self.BIOMethods[ METHODS_CTRL		 ]       = self.cutils.getAddress( self.sockCtrlCallback )#long sock_ctrl(BIO *b, int cmd, long num, void *ptr)
        self.BIOMethods[ METHODS_CREATE	 ]           = self.cutils.getAddress( self.sockNewCallback )#int sock_new(BIO *bi)
        self.BIOMethods[ METHODS_DESTROY	 ]       = self.cutils.getAddress( self.sockFreeCallback ) #int sock_free(BIO *a)
        self.BIOMethods[ METHODS_CALLBACK_CTRL ]     = None

    def RegisterBIOMethods( self ):
        BIO_NOCLOSE = 0

        globalLibSSL.BIO_new.restype  = c_voidp
        globalLibSSL.BIO_new.argtypes = [ c_voidp ]
        print( "############# BIO_new"  )
        self.bioObject = globalLibSSL.BIO_new( self.BIOMethods );
        print( "############# self.bioObject = %s" % self.bioObject )
        if self.bioObject is None:
            raise BIOWrapperError( "BIO_new returned NULL")

        globalDescriptorTable[ self.bioObject ] = self

        fakeFD = 0
        BIO_set_fd( self.bioObject, fakeFD, BIO_NOCLOSE);
        
