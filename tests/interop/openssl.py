import unittest
import logging
from ctypes import cdll, CDLL, c_long, c_ulong,c_int, c_float, c_double, c_char_p, create_string_buffer, byref, c_voidp, c_uint8, c_uint32, c_uint64, c_void_p, cast, POINTER, addressof
import sys 
import os
import struct
import base64
import time

import config 

SUCCESS = 1
NULL    = c_voidp( None )

SIZE_OF_CHACHA_DEFAULT_IV   = 12
SIZE_OF_CHACHA_TAG 			= 16
SIZE_OF_CHACHA_KEY 			= 32

EVP_CTRL_AEAD_GET_TAG       = 0x10
EVP_CTRL_AEAD_SET_TAG       = 0x11

def CSize( buffer ):
	return c_uint32( len( buffer ) )

def CBuffer( buffer ):
	return c_char_p( bytes( buffer ) )

class OpenSSLError( Exception ):
	def __init__( self, msg ):
		Exception.__init__( self, msg )

class OpenSSLTagMismatchError( OpenSSLError ):
	pass

class OpenSSL():
	def __init__( self, sharedObjectPath = config.OPENSSL_PATH  ):
		self.SetupLogger()
		self.openssl = CDLL( sharedObjectPath )  

	def SetupLogger( self ):
		self.log = logging.getLogger( 'OpenSSL' )
		self.log.setLevel( config.LOG_LEVEL )

		formatter 	   = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
		consoleHandler = logging.StreamHandler()
		consoleHandler.setLevel( config.LOG_LEVEL  )
		consoleHandler.setFormatter(formatter)

		self.log.handlers = []
		self.log.addHandler(consoleHandler)


	def CreateCipherContext( self ):
		self.log.debug( "CreateCipherContext" )
		self.openssl.EVP_CIPHER_CTX_new.restype = c_voidp
		ctx = c_voidp( self.openssl.EVP_CIPHER_CTX_new() )
		
		if ctx.value is None:
			logMsg = "EVP_CIPHER_CTX_new returned NULL"
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		return ctx

	def Init_CHACHA20Poly1305( self, ctx, key, iv, isEncrypt = True ):
		self.log.debug( "Init_CHACHA20Poly1305" )

		self.openssl.EVP_chacha20_poly1305.restype = c_void_p
		mechanism =  c_void_p( self.openssl.EVP_chacha20_poly1305 ()  )
		
		if mechanism.value is None:
			logMsg = "EVP_chacha20_poly1305 returned NULL"
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		self.openssl.EVP_EncryptInit_ex.restype = c_int
		if isEncrypt:
			if SUCCESS != self.openssl.EVP_EncryptInit_ex( ctx, mechanism, NULL, CBuffer( key) , CBuffer( iv ) ):  
				logMsg = "EVP_EncryptInit_ex returned value != %d" % SUCCESS
				self.log.error( logMsg )
				raise OpenSSLError( logMsg )
		else:
			if SUCCESS != self.openssl.EVP_DecryptInit_ex( ctx, mechanism, NULL, CBuffer( key) , CBuffer( iv ) ):  
				logMsg = "EVP_EncryptInit_ex returned value != %d" % SUCCESS
				self.log.error( logMsg )
				raise OpenSSLError( logMsg )

	def EVP_EncryptUpdate( self, ctx, plaintext ):
		self.log.debug( "EVP_EncryptUpdate" )

		ciphertext_c 	 = ( c_uint8 * len( plaintext ) )()
		ciphertextLength = c_uint32()

		self.openssl.EVP_EncryptUpdate.restype = c_int
		if SUCCESS != self.openssl.EVP_EncryptUpdate( 	ctx, 
														ciphertext_c, 
														byref( ciphertextLength),
														CBuffer( plaintext ),
														CSize( plaintext ) ):  
			logMsg = "EVP_EncryptUpdate returned value != %d" % SUCCESS
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		if ciphertextLength.value != len( plaintext ):
			logMsg = "ciphertextLength.value != len( plaintext ): %d != %d" % ( ciphertextLength.value, len( plaintext ) )
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		return bytearray( ciphertext_c )

	def EVP_DecryptUpdate( self, ctx, ciphertext ):
		self.log.debug( "EVP_EncryptUpdate" )

		plaintext 	  = ( c_uint8 * len( ciphertext ) )()
		plaintextSize = c_uint32()

		self.openssl.EVP_EncryptUpdate.restype = c_int
		if SUCCESS != self.openssl.EVP_DecryptUpdate( 	ctx, 
														plaintext, 
														byref( plaintextSize),
														CBuffer( ciphertext ),
														CSize( ciphertext ) ):  
			logMsg = "EVP_DecryptUpdate returned value != %d" % SUCCESS
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		if plaintextSize.value != len( ciphertext ):
			logMsg = "plaintextSize.value != len( ciphertext ): %d != %d" % ( plaintextSize.value, len( ciphertext ) )
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		return bytearray( plaintext )

	def EVP_EncryptFinal_ex( self, ctx ):
		self.log.debug( "EVP_EncryptFinal_ex" )

		dummyOut 	= c_uint32()

		self.openssl.EVP_EncryptFinal_ex.restype = c_int
		if SUCCESS != self.openssl.EVP_EncryptFinal_ex( ctx, 
														NULL, 
														byref( dummyOut ) ):  
			logMsg = "EVP_EncryptFinal_ex returned value != %d" % SUCCESS
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		if dummyOut.value != 0:
			logMsg = "dummyOut.value != 0: %d != 0" % ( tagLength.value )
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

	def EVP_DecryptFinal_ex( self, ctx ):
		self.log.debug( "EVP_DecryptFinal_ex" )

		dummyOut 	= c_uint32()

		self.openssl.EVP_DecryptFinal_ex.restype = c_int
		if SUCCESS != self.openssl.EVP_DecryptFinal_ex( ctx, 
														NULL, 
														byref( dummyOut ) ):  
			# self.openssl.ERR_get_error.restype = c_ulong
			# errCode = self.openssl.ERR_get_error()
			# self.openssl.ERR_print_errors_fp(stderr);
			logMsg = "EVP_DecryptFinal_ex returned value != %d" % SUCCESS 

			self.log.error( logMsg )
			raise OpenSSLTagMismatchError( logMsg )

		if dummyOut.value != 0:
			logMsg = "dummyOut.value != 0: %d != 0" % ( tagLength.value )
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

	def GetTag( self, ctx ):
		tag_c 	  = ( c_uint8 * SIZE_OF_CHACHA_TAG )()
		tahLength = c_uint32( SIZE_OF_CHACHA_TAG )

		if SUCCESS != self.openssl.EVP_CIPHER_CTX_ctrl( ctx, 
														EVP_CTRL_AEAD_GET_TAG, 
														tahLength,
														tag_c ):  
			logMsg = "EVP_CIPHER_CTX_ctrl returned value != %d" % SUCCESS
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

		return bytearray( tag_c )

	def SetTag( self, ctx, tag ):
		if SUCCESS != self.openssl.EVP_CIPHER_CTX_ctrl( ctx, 
														EVP_CTRL_AEAD_SET_TAG, 
														c_int( SIZE_OF_CHACHA_TAG ),
														CBuffer( tag ) ):  
			logMsg = "EVP_CIPHER_CTX_ctrl returned value != %d" % SUCCESS
			self.log.error( logMsg )
			raise OpenSSLError( logMsg )

	def Encrypt_CHACHA20Poly1305( self, plaintext, key, iv = None ):
		self.log.debug( "Encrypt_CHACHA20Poly1305" )
		if iv != None and len( iv ) != SIZE_OF_CHACHA_DEFAULT_IV:
			raise OpenSSLError( "Bad iv size")

		if len( key ) != SIZE_OF_CHACHA_KEY:
			raise OpenSSLError( "Bad key size")

		ctx = self.CreateCipherContext()

		if iv == None:
			iv = os.urandom( SIZE_OF_CHACHA_DEFAULT_IV )
		elif len( iv ) != SIZE_OF_CHACHA_DEFAULT_IV:
			logMsg = "iv size is %d instead of %d" % ( len( iv ), SIZE_OF_CHACHA_DEFAULT_IV )
			self.log.error( logMsg )
			raise LibreSSLWrapperError( logMsg )

		self.Init_CHACHA20Poly1305( ctx, key, iv )
		ciphertext = self.EVP_EncryptUpdate( ctx, plaintext )
		self.EVP_EncryptFinal_ex( ctx )
		tag        = self.GetTag( ctx )

		return iv, ciphertext, tag

	def Decrypt_CHACHA20Poly1305( self, key, iv, ciphertext, tag ):
		self.log.debug( "Decrypt_CHACHA20Poly1305" )

		if len( tag ) != SIZE_OF_CHACHA_TAG:
			raise OpenSSLError( "Bad tag size")

		if len( iv ) != SIZE_OF_CHACHA_DEFAULT_IV:
			raise OpenSSLError( "Bad iv size")

		if len( key ) != SIZE_OF_CHACHA_KEY:
			raise OpenSSLError( "Bad key size")

		ctx = self.CreateCipherContext()
		self.Init_CHACHA20Poly1305( ctx, key, iv, isEncrypt = False )
		self.SetTag( ctx, tag )
		plaintext = self.EVP_DecryptUpdate( ctx, ciphertext )
		self.EVP_DecryptFinal_ex( ctx )

		return plaintext

class TestOpenSSL(unittest.TestCase):
	def setUp(self):		
		self.openssl = OpenSSL( config.OPENSSL_PATH )

	def tearDown(self):
		pass

	def testCreateCipherContext( self ):
		ctx = self.openssl.CreateCipherContext()

	def testCHAHAEncrypt( self ):
		plaintext = os.urandom( 1000 )
		key 	  = os.urandom( SIZE_OF_CHACHA_KEY )

		iv, ciphertext, tag = self.openssl.Encrypt_CHACHA20Poly1305( plaintext, key )
		decryptedText = self.openssl.Decrypt_CHACHA20Poly1305( key, iv, ciphertext, tag )

		self.assertTrue( plaintext == decryptedText )

		ciphertext[ 10 ] ^= 1
		exceptionThrown = False
		try:
			# We changed ciphertext, so the tag should NOT fit
			decryptedText = self.openssl.Decrypt_CHACHA20Poly1305( key, iv, ciphertext, tag )
		except OpenSSLError:
			exceptionThrown = True

		self.assertTrue( exceptionThrown )

if __name__ == '__main__':
	unittest.main()
