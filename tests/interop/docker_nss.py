import sys
from ctypes import CDLL

if sys.platform == "linux":
    NSS_PATH = "nss-dependencies/"
    SHARED_OBJECT_TEMPLATE = "lib%s.so"   
elif sys.platform == "win32": 
    NSS_PATH =  "c:/dev/nss-3.30.2/dist/WIN954.0_DBG.OBJ/lib/"
    SHARED_OBJECT_TEMPLATE = "%s.dll"
else:
    raise Exception( "Unknown operating system '%s'" % sys.platform )

def GetObject( name ):
	objectName = SHARED_OBJECT_TEMPLATE % name
	objectPath = NSS_PATH + objectName

	print( "Loading object %s" % objectPath )
	return CDLL( objectPath )
