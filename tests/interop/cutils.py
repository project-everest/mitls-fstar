import sys
from ctypes import CDLL, c_voidp

if sys.platform == "linux":
    objectPath = "cutils/cutils.so"
elif sys.platform == "win32": 
    objectPath = "cutils/cutils.dll"
else:
    raise Exception( "Unknown operating system '%s'" % sys.platform )

def GetObject():
	print( "Loading object %s" % objectPath )
	sharedObject = CDLL( objectPath )
	sharedObject.getAddress.restype      = c_voidp
	sharedObject.duplicateString.restype = c_voidp
	
	return sharedObject
