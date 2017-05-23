import unittest



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


SIZE_OF_METHODS 		= 288
SIZE_OF_VOID_P 	 		= 8
METHODS_NUM_POINTERS 	= int( SIZE_OF_METHODS / SIZE_OF_VOID_P )
METHODS_FILE_TYPE 		= 0 # see see nspr\pr\include\prio.h
METHODS_READ 			= 2

PR_DESC_FILE 		= 1
PR_DESC_SOCKET_TCP 	= 2
PR_DESC_SOCKET_UDP 	= 3
PR_DESC_LAYERED 	= 4
PR_DESC_PIPE 		= 5

class PRDLL():
    def __init__( self, nsprPath = "/home/user/dev/nss-3.30.2/nspr/Linux4.8_x86_64_cc_glibc_PTH_64_DBG.OBJ/pr/src/libnspr4.so" ):
        self.nspr   = CDLL( nsprPath )

        self.nspr.PR_AllocFileDesc.restype  = c_voidp
        self.nspr.PR_AllocFileDesc.argtypes = [ c_int, c_voidp ]  # see nspr\pr\include\private\pprio.h

        self.nspr.PR_FileDesc2NativeHandle.restype  = c_int
        self.nspr.PR_FileDesc2NativeHandle.argtypes = [ c_voidp ]

globalNSPR            = PRDLL()
globalDescriptorTable = {}

def ReadCallback( ctx, buffer, bufferSize ):
    print( "ReadCallback" )

    fileDescriptor = globalNSPR.nspr.PR_FileDesc2NativeHandle( c_voidp( ctx ) )
    print( "fileDescriptor = %s" % fileDescriptor )

    return globalDescriptorTable[ fileDescriptor ].ReadCallback( buffer, bufferSize )
    # pyBuffer = ( c_uint8 * bufferSize ).from_address( buffer )
    # for i in range( bufferSize ):
    #     pyBuffer[ i ] = c_uint8( i )

    # return bufferSize

class PRWrapper():
    def __init__( self ):
        self.nspr   = globalNSPR.nspr
        self.cutils = CDLL( "cutils/cutils.so" )

        READ_CALLBACK     	= CFUNCTYPE(c_int, c_voidp, c_voidp, c_int ) 
        self.readCallback   = READ_CALLBACK( ReadCallback )

        self.cutils.getAddress.restype = c_voidp

        self.PRIOMethods = (c_voidp * METHODS_NUM_POINTERS )()
        self.PRIOMethods[ METHODS_FILE_TYPE ] 	= PR_DESC_LAYERED
        self.PRIOMethods[ METHODS_READ ] 		= self.cutils.getAddress( self.readCallback )

        self.fileDescriptor = self.RegisterNewFileDescriptor()
        FAKE_FD = c_int( self.fileDescriptor )

        

        self.prFileDesc = self.nspr.PR_AllocFileDesc( FAKE_FD, self.PRIOMethods )

    def RegisterNewFileDescriptor( self ):
        global globalDescriptorTable

        fileDescriptor = -1
        if len( globalDescriptorTable.keys() ) == 0:
            fileDescriptor = 1
        else:
            fileDescriptor = max( globalDescriptorTable.keys() ) + 1 

        globalDescriptorTable[ fileDescriptor ] = self

        return fileDescriptor
		
    def ReadCallback( self, buffer, bufferSize ):
        print( "ReadCallback with fd = %d" % self.fileDescriptor )
        pyBuffer = ( c_uint8 * bufferSize ).from_address( buffer )
        for i in range( bufferSize ):
            pyBuffer[ i ] = c_uint8( i )

        return bufferSize

    def Read( self, size ):
        buffer  = bytearray( size )
        cBuffer = ( c_uint8 * size ).from_buffer( buffer )
        cSize   = c_int( size )


        ret = self.nspr.PR_Read( self.prFileDesc, cBuffer, cSize )
        print( "ret = %s, buffer = %s" % ( ret, buffer ) )

        return buffer

class PRWrapperTester( unittest.TestCase ):
    def __init__(self, *args, **kwargs):
        super( PRWrapperTester, self).__init__(*args, **kwargs)

    def setUp(self):
        pass
        # self.prWrapper = PRWrapper()

    def tearDown(self):
        pass

    def testInitReadWrite( self ):
        print( "hello" )
        
        clientSocket = PRWrapper()
        serverSocket = PRWrapper()

        clientSocket.Read( 10 )
        serverSocket.Read( 10 )
        


if __name__ == '__main__':
	unittest.main()
