import logging
import sys
import time
import struct
import glob
import logging
import traceback
import datetime
import os
from copy      import deepcopy
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
                    CFUNCTYPE, \
                    POINTER   

import cryptography
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.ciphers import (
    Cipher, algorithms, modes
)

from openssl import OpenSSL, OpenSSLError

import config


LOG_TRANSMITTED_BYTES       = False

WAIT_FOR_KEYS_TO_BE_LEAKEDD_SECONDS = 0.2

class TLSParserError( Exception ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

class TLSParserDecryptionError( TLSParserError ):
    def __init__( self, msg ):
        Exception.__init__( self, msg )

class AttrDict(dict):
    def __init__(self, *args, **kwargs):
        super(AttrDict, self).__init__(*args, **kwargs)
        self.__dict__ = self

    def __deepcopy__(self, memo ):
        deepcopy_method = self.__deepcopy__
        self.__deepcopy__ = None
        cp = deepcopy(self, memo)
        self.__deepcopy__ = deepcopy_method

        # custom treatments
        cp.__dict__ = cp

        return cp

def GetKey( dictionary, valueToSearch, defaultResponse ):
    if valueToSearch not in dictionary.values():
        return defaultResponse

    for key in dictionary.keys():
        if dictionary[ key ] == valueToSearch:
            return key

class COLORS():
    BLACK       = 0
    RED         = 1
    GREEN       = 2
    YELLOW      = 3
    BLUE        = 4
    MAGENTA     = 5
    CYAN        = 6
    WHITE       = 7
    DEFAULT     = 8

    #Attributes: 
    NORMAL      = 0
    BRIGHT      = 1

class Terminal():
    @staticmethod
    def GetColorSequence( foreground, background = COLORS.DEFAULT, attribute = COLORS.NORMAL ):
        return "\x1b[%d;%d;%dm" % ( COLORS.BRIGHT, foreground + 30, background + 40 );

    @staticmethod
    def ColorText( color, text, originalColor = COLORS.WHITE ):
        return Terminal.GetColorSequence( color ) + text + Terminal.GetColorSequence( originalColor )

def Red( text, originalColor = COLORS.WHITE ):
    if sys.platform == "win32":
        return text
    return Terminal.ColorText( COLORS.RED, text, originalColor )

def Green( text, originalColor = COLORS.WHITE ):
    if sys.platform == "win32":
        return text
    return Terminal.ColorText( COLORS.GREEN, text, originalColor )

def Yellow( text, originalColor = COLORS.WHITE ):
    if sys.platform == "win32":
        return text
    return Terminal.ColorText( COLORS.YELLOW, text, originalColor )

def Magenta( text, originalColor = COLORS.WHITE ):
    if sys.platform == "win32":
        return text
    return Terminal.ColorText( COLORS.MAGENTA, text, originalColor )

def Blue( text, originalColor = COLORS.WHITE ):
    if sys.platform == "win32":
        return text
    return Terminal.ColorText( COLORS.BLUE, text, originalColor )

class Cryptor():
    @staticmethod
    def AES_GCM_Decrypt( iv, key, cipherText, tag ):
        decryptor = Cipher( algorithms.AES(key),
                            modes.GCM(iv, tag),
                            backend=default_backend()
                            ).decryptor()

        AAD = b"" #no additional authenticated data
        decryptor.authenticate_additional_data( AAD )
        
        return decryptor.update(cipherText) + decryptor.finalize()

    @staticmethod
    def AES_GCM_Encrypt( iv, key, plaintext ):        
        encryptor = Cipher( algorithms.AES(key),
                            modes.GCM(iv),
                            backend=default_backend()
                           ).encryptor()

        AAD = b"" #no additional authenticated data
        encryptor.authenticate_additional_data( AAD )

        ciphertext = encryptor.update(plaintext) + encryptor.finalize()
        
        return (ciphertext, encryptor.tag)

SIZE_OF_TYPE            = 1
SIZE_OF_PROTOCOL        = 2
SIZE_OF_UINT8           = 1
SIZE_OF_UINT16          = 2
SIZE_OF_UINT24          = 3
TLS_RECORD_HEADER_SIZE  = SIZE_OF_TYPE + SIZE_OF_PROTOCOL + SIZE_OF_UINT16

TLS_RECORD_TYPE_ALERT      = 21
TLS_RECORD_TYPE_HANDSHAKE  = 22
TLS_RECORD_TYPE_APP_DATA   = 23

SIZE_OF_HANDSHAKE_TYPE              = 1
HANDSHAKE_TYPE_CLIENT_HELLO         = 1
HANDSHAKE_TYPE_SERVER_HELLO         = 2
HANDSHAKE_TYPE_NEW_SESSION_TICKET   = 4
HANDSHAKE_TYPE_END_OF_EARLY_DATA    = 5
HANDSHAKE_TYPE_HELLO_RETRY_REQUEST  = 6
HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS = 8
HANDSHAKE_TYPE_CERTIFICATE          = 11
HANDSHAKE_TYPE_CERTIFICATE_REQUEST  = 13
HANDSHAKE_TYPE_CERTIFICATE_VERIFY   = 15
HANDSHAKE_TYPE_FINISHED             = 20
HANDSHAKE_TYPE_KEY_UPDATE           = 24
HANDSHAKE_TYPE_MESSAGE_HASH         = 254

HANDSHAKE_TYPE_NAME = {
    HANDSHAKE_TYPE_CLIENT_HELLO         : "client_hello",
    HANDSHAKE_TYPE_SERVER_HELLO         : "server_hello",
    HANDSHAKE_TYPE_NEW_SESSION_TICKET   : "new_session_ticket",
    HANDSHAKE_TYPE_END_OF_EARLY_DATA    : "end_of_early_data",
    HANDSHAKE_TYPE_HELLO_RETRY_REQUEST  : "hello_retry_request",
    HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS : "encrypted_extensions",
    HANDSHAKE_TYPE_CERTIFICATE          : "certificate",
    HANDSHAKE_TYPE_CERTIFICATE_REQUEST  : "certificate_request",
    HANDSHAKE_TYPE_CERTIFICATE_VERIFY   : "certificate_verify",
    HANDSHAKE_TYPE_FINISHED             : "finished",
    HANDSHAKE_TYPE_KEY_UPDATE           : "key_update",
    HANDSHAKE_TYPE_MESSAGE_HASH         : "message_hash",
}

TLS_RECORD_TYPE_NAME = {    TLS_RECORD_TYPE_ALERT     : "alert",  
                            TLS_RECORD_TYPE_HANDSHAKE : "handshake", 
                            TLS_RECORD_TYPE_APP_DATA  : "application_data" } 

TLS_RSA_WITH_RC4_128_SHA                = 0x0005
TLS_RSA_WITH_3DES_EDE_CBC_SHA           = 0x000a
TLS_RSA_WITH_AES_128_CBC_SHA            = 0x002f
TLS_RSA_WITH_AES_256_CBC_SHA            = 0x0035
TLS_RSA_WITH_AES_128_CBC_SHA256         = 0x003c
TLS_RSA_WITH_AES_128_GCM_SHA256         = 0x009c
TLS_RSA_WITH_AES_256_GCM_SHA384         = 0x009d
TLS_ECDHE_ECDSA_WITH_RC4_128_SHA        = 0xc007
TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA    = 0xc009
TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA    = 0xc00a
TLS_ECDHE_RSA_WITH_RC4_128_SHA          = 0xc011
TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA     = 0xc012
TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA      = 0xc013
TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA      = 0xc014
TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 = 0xc023
TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256   = 0xc027
TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256   = 0xc02f
TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 = 0xc02b
TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384   = 0xc030
TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = 0xc02c
TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305    = 0xcca8
TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305  = 0xcca9
TLS_DHE_RSA_WITH_CHACHA20_POLY1305      = 0xccaa
TLS_AES_128_GCM_SHA256                  = 0x1301
TLS_AES_256_GCM_SHA384                  = 0x1302
TLS_CHACHA20_POLY1305_SHA256            = 0x1303
TLS_AES_128_CCM_SHA256                  = 0x1304
TLS_AES_128_CCM_8_SHA256                = 0x1305

TLS_RSA_WITH_AES_128_CBC_SHA            = 0x002F
TLS_DH_DSS_WITH_AES_128_CBC_SHA         = 0x0030
TLS_DH_RSA_WITH_AES_128_CBC_SHA         = 0x0031
TLS_DHE_DSS_WITH_AES_128_CBC_SHA        = 0x0032
TLS_DHE_RSA_WITH_AES_128_CBC_SHA        = 0x0033
TLS_DH_anon_WITH_AES_128_CBC_SHA        = 0x0034
TLS_RSA_WITH_AES_256_CBC_SHA            = 0x0035
TLS_DH_DSS_WITH_AES_256_CBC_SHA         = 0x0036
TLS_DH_RSA_WITH_AES_256_CBC_SHA         = 0x0037
TLS_DHE_DSS_WITH_AES_256_CBC_SHA        = 0x0038
TLS_DHE_RSA_WITH_AES_256_CBC_SHA        = 0x0039
TLS_DH_anon_WITH_AES_256_CBC_SHA        = 0x003A

TLS_DHE_DSS_WITH_AES_128_GCM_SHA256     = 0x00A2
TLS_DHE_RSA_WITH_AES_128_GCM_SHA256     = 0x009E
TLS_DHE_RSA_WITH_AES_256_GCM_SHA384     = 0x009F

TLS_EMPTY_RENEGOTIATION_INFO_SCSV       = 0x00FF

AES_128_GCM_FAMILY = [ TLS_AES_128_GCM_SHA256, TLS_AES_256_GCM_SHA384 ]

CIPHER_SUITES_NAMES = {
    TLS_RSA_WITH_RC4_128_SHA                : "TLS_RSA_WITH_RC4_128_SHA",
    TLS_RSA_WITH_3DES_EDE_CBC_SHA           : "TLS_RSA_WITH_3DES_EDE_CBC_SHA",
    TLS_RSA_WITH_AES_128_CBC_SHA            : "TLS_RSA_WITH_AES_128_CBC_SHA",
    TLS_RSA_WITH_AES_256_CBC_SHA            : "TLS_RSA_WITH_AES_256_CBC_SHA",
    TLS_RSA_WITH_AES_128_CBC_SHA256         : "TLS_RSA_WITH_AES_128_CBC_SHA256",
    TLS_RSA_WITH_AES_128_GCM_SHA256         : "TLS_RSA_WITH_AES_128_GCM_SHA256",
    TLS_RSA_WITH_AES_256_GCM_SHA384         : "TLS_RSA_WITH_AES_256_GCM_SHA384",
    TLS_ECDHE_ECDSA_WITH_RC4_128_SHA        : "TLS_ECDHE_ECDSA_WITH_RC4_128_SHA",
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA    : "TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA",
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA    : "TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA",
    TLS_ECDHE_RSA_WITH_RC4_128_SHA          : "TLS_ECDHE_RSA_WITH_RC4_128_SHA",
    TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA     : "TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA",
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA      : "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA",
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA      : "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA",
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 : "TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256",
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256   : "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256",
    TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256   : "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256",
    TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 : "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256",
    TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384   : "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384",
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 : "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384",
    TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305    : "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305",
    TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305  : "TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305",
    TLS_AES_128_GCM_SHA256                  : "TLS_AES_128_GCM_SHA256",
    TLS_AES_256_GCM_SHA384                  : "TLS_AES_256_GCM_SHA384",
    TLS_CHACHA20_POLY1305_SHA256            : "TLS_CHACHA20_POLY1305_SHA256",
    TLS_RSA_WITH_AES_128_CBC_SHA            : "TLS_RSA_WITH_AES_128_CBC_SHA",
    TLS_DH_DSS_WITH_AES_128_CBC_SHA         : "TLS_DH_DSS_WITH_AES_128_CBC_SHA",
    TLS_DH_RSA_WITH_AES_128_CBC_SHA         : "TLS_DH_RSA_WITH_AES_128_CBC_SHA",
    TLS_DHE_DSS_WITH_AES_128_CBC_SHA        : "TLS_DHE_DSS_WITH_AES_128_CBC_SHA",
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA        : "TLS_DHE_RSA_WITH_AES_128_CBC_SHA",
    TLS_DH_anon_WITH_AES_128_CBC_SHA        : "TLS_DH_anon_WITH_AES_128_CBC_SHA",
    TLS_RSA_WITH_AES_256_CBC_SHA            : "TLS_RSA_WITH_AES_256_CBC_SHA",
    TLS_DH_DSS_WITH_AES_256_CBC_SHA         : "TLS_DH_DSS_WITH_AES_256_CBC_SHA",
    TLS_DH_RSA_WITH_AES_256_CBC_SHA         : "TLS_DH_RSA_WITH_AES_256_CBC_SHA",
    TLS_DHE_DSS_WITH_AES_256_CBC_SHA        : "TLS_DHE_DSS_WITH_AES_256_CBC_SHA",
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA        : "TLS_DHE_RSA_WITH_AES_256_CBC_SHA",
    TLS_DH_anon_WITH_AES_256_CBC_SHA        : "TLS_DH_anon_WITH_AES_256_CBC_SHA", 
    TLS_DHE_DSS_WITH_AES_128_GCM_SHA256     : "TLS_DHE_DSS_WITH_AES_128_GCM_SHA256",
    TLS_DHE_RSA_WITH_AES_128_GCM_SHA256     : "TLS_DHE_RSA_WITH_AES_128_GCM_SHA256",
    TLS_AES_128_CCM_SHA256                  : "TLS_AES_128_CCM_SHA256",               
    TLS_AES_128_CCM_8_SHA256                : "TLS_AES_128_CCM_8_SHA256",
    TLS_DHE_RSA_WITH_CHACHA20_POLY1305      : "TLS_DHE_RSA_WITH_CHACHA20_POLY1305",
    TLS_DHE_RSA_WITH_AES_256_GCM_SHA384     : "TLS_DHE_RSA_WITH_AES_256_GCM_SHA384",
    TLS_EMPTY_RENEGOTIATION_INFO_SCSV       : "TLS_EMPTY_RENEGOTIATION_INFO_SCSV",
}

# https://www.iana.org/assignments/tls-extensiontype-values/tls-extensiontype-values.xhtml
EXTENSION_TYPE_MAX_FRAGMENT_LENGTH                      = 1
EXTENSION_TYPE_CLIENT_CERTIFICATE_URL                   = 2
EXTENSION_TYPE_TRUSTED_CA_KEYS                          = 3
EXTENSION_TYPE_TRUNCATED_HMAC                           = 4
EXTENSION_TYPE_STATUS_REQUEST                           = 5
EXTENSION_TYPE_USER_MAPPING                             = 6
EXTENSION_TYPE_CLIENT_AUTHZ                             = 7
EXTENSION_TYPE_SERVER_AUTHZ                             = 8
EXTENSION_TYPE_CERT_TYPE                                = 9
EXTENSION_TYPE_SUPPORTED_GROUPS                         = 10
EXTENSION_TYPE_EC_POINT_FORMATS                         = 11
EXTENSION_TYPE_SRP                                      = 12
EXTENSION_TYPE_SIGNATURE_ALGORITHMS                     = 13
EXTENSION_TYPE_USE_SRTP                                 = 14
EXTENSION_TYPE_HEARTBEAT                                = 15
EXTENSION_TYPE_APPLICATION_LAYER_PROTOCOL_NEGOTIATION   = 16
EXTENSION_TYPE_STATUS_REQUEST_V2                        = 17
EXTENSION_TYPE_SIGNED_CERTIFICATE_TIMESTAMP             = 18
EXTENSION_TYPE_CLIENT_CERTIFICATE_TYPE                  = 19
EXTENSION_TYPE_SERVER_CERTIFICATE_TYPE                  = 20
EXTENSION_TYPE_PADDING                                  = 21
EXTENSION_TYPE_ENCRYPT_THEN_MAC                         = 22
EXTENSION_TYPE_EXTENDED_MASTER_SECRET                   = 23
EXTENSION_TYPE_TOKEN_BINDING                            = 24
EXTENSION_TYPE_CACHED_INFO                              = 25
EXTENSION_TYPE_SESSIONTICKET                            = 35
EXTENSION_TYPE_KEY_SHARE                                = 40
EXTENSION_TYPE_PRE_SHARED_KEY                           = 41
EXTENSION_TYPE_EARLY_DATA                               = 42
EXTENSION_TYPE_SUPPORTED_VERSIONS                       = 43
EXTENSION_TYPE_COOKIE                                   = 44
EXTENSION_TYPE_PSK_KEY_EXCHANGE_MODES                   = 45
EXTENSION_TYPE_CERTIFICATE_AUTHORITIES                  = 47
EXTENSION_TYPE_OID_FILTERS                              = 48
EXTENSION_TYPE_POST_HANDSHAKE_AUTH                      = 49
EXTENSION_TYPE_RENEGOTIATION_INFO                       = 65281

EXTENSION_TYPE_NAMES = {
    0  : 'SERVER_NAME',
    1  : "MAX_FRAGMENT_LENGTH",
    2  : "CLIENT_CERTIFICATE_URL",
    3  : "TRUSTED_CA_KEYS",
    4  : "TRUNCATED_HMAC",
    5  : "STATUS_REQUEST",
    6  : "USER_MAPPING",
    7  : "CLIENT_AUTHZ",
    8  : "SERVER_AUTHZ",
    9  : "CERT_TYPE",
    10 : "SUPPORTED_GROUPS",
    11 : "EC_POINT_FORMATS",
    12 : "SRP",
    13 : "SIGNATURE_ALGORITHMS",
    14 : "USE_SRTP",
    15 : "HEARTBEAT",
    16 : "APPLICATION_LAYER_PROTOCOL_NEGOTIATION",
    17 : "STATUS_REQUEST_V2",
    18 : "SIGNED_CERTIFICATE_TIMESTAMP",
    19 : "CLIENT_CERTIFICATE_TYPE",
    20 : "SERVER_CERTIFICATE_TYPE",
    21 : "PADDING",
    22 : "ENCRYPT_THEN_MAC",
    23 : "EXTENDED_MASTER_SECRET",
    24 : "TOKEN_BINDING",
    25 : "CACHED_INFO",
    26 : "QUIC_TRANSPORT_PARAMETERS",
    35 : "SESSIONTICKET",
    40 : "KEY_SHARE",
    41 : "PRE_SHARED_KEY",
    42 : "EARLY_DATA",
    43 : "SUPPORTED_VERSIONS",
    44 : "COOKIE",
    45 : "PSK_KEY_EXCHANGE_MODES",
    47 : "CERTIFICATE_AUTHORITIES",
    48 : "OID_FILTERS",
    49 : "POST_HANDSHAKE_AUTH",
    65281 : "RENEGOTIATION_INFO",
}

NAME                    = "Name"
INTERPRETATION          = "Interpretation"
RAW_CONTENTS            = "RawContents"
DIRECTION               = "Direction"
GROUP_NAME              = "GroupName"
VERSION_ID              = "VersionID"
KEY_SHARE               = "KeyShare"
KEY_SHARE_ENTRY         = "KeyShareEntry"
SIGNATURE_ALGORITHM     = "SignatureAlgorithm"
CIPHER_SUITE            = "CipherSuite"
RECORD_TYPE             = "Record type"
PROTOCOL                = "Protocol"
ALERT                   = "Alert"
LENGTH                  = "Length"
RAW_RECORD              = "Raw record"
HANDSHAKE_TYPE          = "HandshakeType"
HANDSHAKE_MSG           = "Handshake message"
RANDOM                  = "Random"
LEGACY_ID               = "LegacySessionID"
CIPHER_SUITES           = "Cipher suites"
LEGACY_COMPRESSION      = "Legacy compression"
EXTENSIONS              = "Extensions"
RECORD                  = "Record"
SELECTED_CIPHER_SUITE   = "Selected cipher suite"
RAW_MSG                 = "Raw message"
DECRYPTED_RECORD_TYPE   = "Decrypted record type"
DECRYPTED_RECORD        = "Decrypted record"
REQUEST_CONTEXT         = "RequestContext"
RAW_CERTIFICATE         = "RawCertificate"
CERT_ENTRY              = "CertificateEntry"
CERTIFICATES            = "Certificates"
CERTIFICATE             = "Certificate"
OPAQUE_CERT             = "OpaqueCert"
CERTIFICATE_LIST        = "CertificateList"
CERTIFICATE_VERIFY      = "CertificateVerify"
SIGNATURE_SCHEME        = "Signature scheme"
SIGNATURE               = "Signature"
IV_AND_KEY              = "IV and Key"
PARENT_NODE             = "ParentNode"
SWAP_ITEMS              = "SwapItems"
EXTRACT_TO_PLAINTEXT    = "ExtractToPlaintext"
REMOVE_ITEM             = "RemoveItem"

LEAKED_KEYS_DIR     = "leaked_keys"

class SignatureScheme():
    rsa_pkcs1_sha256        = 0x0401
    rsa_pkcs1_sha384        = 0x0501
    rsa_pkcs1_sha512        = 0x0601

    # ECDSA algorithms 
    ecdsa_secp256r1_sha256  = 0x0403
    ecdsa_secp384r1_sha384  = 0x0503
    ecdsa_secp521r1_sha512  = 0x0603

    # RSASSA-PSS algorithms 
    rsa_pss_sha256          = 0x0804
    rsa_pss_sha384          = 0x0805
    rsa_pss_sha512          = 0x0806
    
    # EdDSA algorithms  
    ed25519                 = 0x0807
    ed448                   = 0x0808
    
    # Legacy algorithms     
    rsa_pkcs1_sha1          = 0x0201
    ecdsa_sha1              = 0x0203

    dsa_sha256              = 0x0402
    dsa_sha384              = 0x0502
    dsa_sha512              = 0x0602
    dsa_sha224              = 0x0302
    dsa_sha1                = 0x0202

    SchemeByValue = { 
        0x0401 : "rsa_pkcs1_sha256",
        0x0501 : "rsa_pkcs1_sha384",
        0x0601 : "rsa_pkcs1_sha512",
        0x0403 : "ecdsa_secp256r1_sha256",
        0x0503 : "ecdsa_secp384r1_sha384",
        0x0603 : "ecdsa_secp521r1_sha512",
        0x0804 : "rsa_pss_sha256",
        0x0805 : "rsa_pss_sha384",
        0x0806 : "rsa_pss_sha512",
        0x0807 : "ed25519",
        0x0808 : "ed448",
        0x0201 : "rsa_pkcs1_sha1",
        0x0203 : "ecdsa_sha1",
        0x0402 : "dsa_sha256",
        0x0502 : "dsa_sha384",
        0x0602 : "dsa_sha512",
        0x0302 : "dsa_sha224",
        0x0202 : "dsa_sha1",
    }

class Alert():
    close_notify                    =   0
    unexpected_message              =   10
    bad_record_mac                  =   20
    decryption_failed_RESERVED      =   21
    record_overflow                 =   22
    handshake_failure               =   40
    bad_certificate                 =   42
    unsupported_certificate         =   43
    certificate_revoked             =   44
    certificate_expired             =   45
    certificate_unknown             =   46
    illegal_parameter               =   47
    unknown_ca                      =   48
    access_denied                   =   49
    decode_error                    =   50
    decrypt_error                   =   51
    protocol_version                =   70
    insufficient_security           =   71
    internal_error                  =   80
    inappropriate_fallback          =   86
    user_canceled                   =   90
    missing_extension               =   109
    unsupported_extension           =   110
    certificate_unobtainable        =   111
    unrecognized_name               =   112
    bad_certificate_status_response =   113
    bad_certificate_hash_value      =   114
    unknown_psk_identity            =   115
    certificate_required            =   116
    no_application_protocol         =   120

    AlertByValue = {
        0   :   'close_notify',
        10  :   'unexpected_message',
        20  :   'bad_record_mac',
        21  :   'decryption_failed_RESERVED',
        22  :   'record_overflow',
        40  :   'handshake_failure',
        42  :   'bad_certificate',
        43  :   'unsupported_certificate',
        44  :   'certificate_revoked',
        45  :   'certificate_expired',
        46  :   'certificate_unknown',
        47  :   'illegal_parameter',
        48  :   'unknown_ca',
        49  :   'access_denied',
        50  :   'decode_error',
        51  :   'decrypt_error',
        70  :   'protocol_version',
        71  :   'insufficient_security',
        80  :   'internal_error',
        86  :   'inappropriate_fallback',
        90  :   'user_canceled',
        109 :   'missing_extension',
        110 :   'unsupported_extension',
        111 :   'certificate_unobtainable',
        112 :   'unrecognized_name',
        113 :   'bad_certificate_status_response',
        114 :   'bad_certificate_hash_value',
        115 :   'unknown_psk_identity',
        116 :   'certificate_required',
        120 :   'no_application_protocol',
    }

NamedGroups = AttrDict( {'secp256r1'    : 0x0017,
                         'secp384r1'    : 0x0018,
                         'secp521r1'    : 0x0019,
                         'x25519'       : 0x001D,
                         'x448'         : 0x001E,
                         'ffdhe2048'    : 0x0100,
                         'ffdhe3072'    : 0x0101,
                         'ffdhe4096 '   : 0x0102,
                         'ffdhe6144'    : 0x0103,
                         'ffdhe8192'    : 0x0104, } )

class Direction():
    CLIENT_TO_SERVER = "Client-to-Server"
    SERVER_TO_CLIENT = "Server-to-Client"

Identity = lambda x: x #identity function


class TLSParser():
    TLS_1_3_MAGIC   = b"\x03\x01"
    NUM_RECENT_DIRS = 3

    def __init__( self ):
        self.recentBytes     = b""
        self.curretPosition  = 0
        self.transcript      = []
        self.state           = AttrDict()
        self.openssl         = OpenSSL()
        self.msgManipulators = []

        self.SetupLogger()

    def SetupLogger( self ):
        self.log = logging.getLogger( 'TLSParser' )
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL )
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def ExpectedMsgSize():
        pass

    def GetTLSRecordMsgType( self, typeNumber ):
        if typeNumber in TLS_RECORD_TYPE_NAME.keys():
            return TLS_RECORD_TYPE_NAME[ typeNumber ]

        return "unknown_type"

    @staticmethod
    def GetHandshakeType( typeNumber ):
        if typeNumber in HANDSHAKE_TYPE_NAME.keys():
            return HANDSHAKE_TYPE_NAME[ typeNumber ]

        return "unknown_type"

    def GetExtensionName( self, typeNumber ):
        if typeNumber in EXTENSION_TYPE_NAMES.keys():
            return EXTENSION_TYPE_NAMES[ typeNumber ]

        return "unknown_extension (%d)" % typeNumber
    
    def GetCipherSuiteName( self, suiteID ):
        if suiteID in CIPHER_SUITES_NAMES.keys():
            return CIPHER_SUITES_NAMES[ suiteID ]

        return "unknown_type"

    def GetSignatureScheme( self, schemeNumber ):
        if schemeNumber in SignatureScheme.SchemeByValue.keys():
            return SignatureScheme.SchemeByValue[ schemeNumber ]

        return "unknown scheme"

    def GetAlertType( self, typeNumber ):
        if typeNumber in Alert.AlertByValue.keys():
            return Alert.AlertByValue[ typeNumber ]

        return "unknown_alert - %d" % typeNumber
    
    def ConsumeByte( self, expectedValue = None ):
        value = struct.unpack( "B", self.recentBytes[ self.curretPosition: self.curretPosition + SIZE_OF_UINT8 ] )[0]
        self.curretPosition     += SIZE_OF_UINT8

        if expectedValue is not None:
            if value != expectedValue:
                raise TLSParserError( "value == %d instead of expected %d" % ( value, expectedValue ) )

        return value

    @staticmethod
    def ParseShort( rawShort ):
        return struct.unpack( ">H", rawShort )[0]

    def ConsumeShort( self, expectedValue = None  ):
        value = self.ParseShort( self.recentBytes[ self.curretPosition: self.curretPosition + SIZE_OF_UINT16 ] )
        self.curretPosition     += SIZE_OF_UINT16

        if expectedValue is not None:
            if value != expectedValue:
                raise TLSParserError( "value == %d instead of expected %d" % ( value, expectedValue ) )

        return value

    def ConsumeTrippleByteSize( self, expectedValue = None  ):
        value = struct.unpack( ">I", b"\x00" + self.recentBytes[ self.curretPosition: self.curretPosition + SIZE_OF_UINT24 ] )[0]
        self.curretPosition     += SIZE_OF_UINT24

        if expectedValue is not None:
            if value != expectedValue:
                raise TLSParserError( "value == %d instead of expected %d" % ( value, expectedValue ) )

        return value

    def PeekRawBytes( self, numBytes, attachPreviousBytes = 0 ):
        if self.curretPosition - attachPreviousBytes < 0:
            raise TLSParserError( "Can't attach %d previous bytes" % attachPreviousBytes )

        value = self.recentBytes[ self.curretPosition - attachPreviousBytes : self.curretPosition + numBytes ]

        if len( value ) != numBytes + attachPreviousBytes :
            raise TLSParserError( "Can't consume %d bytes + previous %d bytes, only %d left" % (numBytes, attachPreviousBytes, len( value )))

        return value

    def ConsumeRawBytes( self, numBytes, attachPreviousBytes = 0 ):
        values = self.PeekRawBytes( numBytes, attachPreviousBytes )
        self.curretPosition += numBytes

        return values

    def ParseMsgHeader( self, direction ):
        msg                 = {}
        msg[ DIRECTION ]    = direction

        msg[ RECORD_TYPE ]  = self.ConsumeByte() 
        msg[ PROTOCOL ]     = self.ConsumeRawBytes( SIZE_OF_PROTOCOL ) 
        msg[ LENGTH    ]    = self.ConsumeShort()
        
        # print( "msg= %s" % msg )
        if msg[ PROTOCOL ] != self.TLS_1_3_MAGIC:
            raise TLSParserError( "Protocol magic is %s instead of expected %s" % ( msg[ PROTOCOL ], self.TLS_1_3_MAGIC ) )

        return msg

    def ConsumeCertificateVerify( self ):
        certVerify          = []

        certVerify.append( self.ConsumeSignatureScheme() )

        opaqueSignatureAsList, rawSignature = self.ConsumeList( SIZE_OF_UINT16, self.ConsumeByte )
        certVerify.append( AttrDict( {  NAME            : SIGNATURE, 
                                        RAW_CONTENTS    : rawSignature, 
                                        INTERPRETATION  : bytes( opaqueSignatureAsList ) } ) )
        return certVerify

    def ConsumeSingleCertificate( self ):
        singleCertEntry = []

        opaqueCertAsList, rawCertContent = self.ConsumeList( SIZE_OF_UINT24, self.ConsumeByte )
        singleCertEntry.append( AttrDict( { NAME            : OPAQUE_CERT, 
                                            RAW_CONTENTS    : rawCertContent, 
                                            INTERPRETATION  : bytes( opaqueCertAsList ) }) )

        extensionList, rawExtensions = self.ConsumeList( SIZE_OF_UINT16, self.ConsumeExtension )
        singleCertEntry.append( AttrDict( { NAME : EXTENSIONS, RAW_CONTENTS : rawExtensions, INTERPRETATION : extensionList }) )

        return AttrDict( { NAME           : CERT_ENTRY, 
                           RAW_CONTENTS   : rawCertContent + rawExtensions, 
                           INTERPRETATION : singleCertEntry  } ) 

    def ConsumeCertificate( self ):
        certificate         = []

        requestContextSize  = self.ConsumeByte()
        rawRequestContext   = self.PeekRawBytes( requestContextSize, SIZE_OF_UINT8 )
        requestContext      = self.ConsumeRawBytes( requestContextSize ) 
        certificate.append( AttrDict( { NAME : REQUEST_CONTEXT, RAW_CONTENTS : rawRequestContext, INTERPRETATION : requestContext } ) )


        certificates, rawCertificateList = self.ConsumeList( SIZE_OF_UINT24, self.ConsumeSingleCertificate )
        certificate.append( AttrDict( { NAME : CERTIFICATE_LIST, RAW_CONTENTS : rawCertificateList, INTERPRETATION : certificates } ) )

        return certificate

    def ParseSupportedVersions( self, rawVersions ):
        totalSize = rawVersions[ 0 ]
        if totalSize + 1 != len( rawVersions ) or totalSize % 2 != 0:
            raise TLSParserError( "Bad size %d for supported versions. len( rawVersions ) = %s" 
                % ( totalSize, len( rawVersions ) ) )

        curretPosition    = 1
        supportedVersions = []
        while curretPosition < len( rawVersions ):
            version = struct.unpack( ">H", rawVersions[ curretPosition : curretPosition + SIZE_OF_UINT16 ] )[ 0 ]
            supportedVersions.append( version )
            curretPosition += SIZE_OF_UINT16

        return supportedVersions

    def ConsumeKeyShareEntry( self ):
        keyShareEntry = []

        supportedGroup = self.ConsumeSupportedGroup() 
        keyShareEntry.append( supportedGroup )

        keyShareSize = self.ConsumeShort()
        rawKeyShare  = self.PeekRawBytes( keyShareSize, SIZE_OF_UINT16 )
        keyShare     = self.ConsumeRawBytes( keyShareSize )
        keyShareEntry.append( AttrDict( { NAME           : KEY_SHARE,
                                          RAW_CONTENTS   : keyShare,
                                          INTERPRETATION : "<key share>" } ) )

        
        return AttrDict( { NAME           : KEY_SHARE_ENTRY,
                           RAW_CONTENTS   : supportedGroup.RawContents + rawKeyShare,
                           INTERPRETATION : keyShareEntry } )

    def ConsumeKeyShare( self, handshakeType ):
        if handshakeType == HANDSHAKE_TYPE_SERVER_HELLO:
            return [ self.ConsumeKeyShareEntry() ]

        elif handshakeType == HANDSHAKE_TYPE_CLIENT_HELLO:
            keyShares, _ = self.ConsumeList( SIZE_OF_UINT16, self.ConsumeKeyShareEntry )
            return keyShares

        elif handshakeType == HANDSHAKE_TYPE_HELLO_RETRY_REQUEST:
            return [ self.ConsumeSupportedGroup() ]

        #else:
        raise TLSParserError( "Unexpected handshakeType %d" % handshakeType )

    def ConsumeCipherSuite( self ):
        rawSignatureScheme = self.PeekRawBytes( SIZE_OF_UINT16 )
        cipherSuiteID      = self.ConsumeShort() 

        parsedPiece = AttrDict( { NAME           : CIPHER_SUITE,
                                  RAW_CONTENTS   : rawSignatureScheme,
                                  INTERPRETATION : self.GetCipherSuiteName( cipherSuiteID )  } )

        return parsedPiece

    def ConsumeSignatureScheme( self ):
        rawSignatureScheme = self.PeekRawBytes( SIZE_OF_UINT16 )
        signatureScheme = self.ConsumeShort() 

        parsedPiece = AttrDict( { NAME           : SIGNATURE_ALGORITHM,
                                  RAW_CONTENTS   : rawSignatureScheme,
                                  INTERPRETATION : self.GetSignatureScheme( signatureScheme )  } )

        return parsedPiece

    def ConsumeSupportedGroup( self ):
        rawNamedGroup = self.PeekRawBytes( SIZE_OF_UINT16 )
        namedGroupID  = self.ConsumeShort() 

        parsedPiece = AttrDict( { NAME           : GROUP_NAME,
                                  RAW_CONTENTS   : rawNamedGroup,
                                  INTERPRETATION : GetKey( NamedGroups, namedGroupID, "unkown group" )  } )

        return parsedPiece

    def ConsumeSupportedVersion( self ):
        rawVersionID = self.ConsumeRawBytes( SIZE_OF_UINT16 )
        versionID    = self.ParseShort( rawVersionID )

        versionName = "<unknown version>"
        if versionID == 0x0303:
            versionName = "TLS-1.2"
        elif versionID == 0x7f14:
            versionName = "TLS-1.3-draft-20"
        elif versionID == 0x7f15:
            versionName = "TLS-1.3-draft-21"

        return AttrDict( { NAME           : VERSION_ID,
                           RAW_CONTENTS   : rawVersionID,
                           INTERPRETATION : versionName } )

    def ConsumeExtension( self, msgType ):
        extensionType = self.ConsumeShort()
        extensionSize = self.ConsumeShort()
        rawExtension  = self.PeekRawBytes( extensionSize, 2 * SIZE_OF_UINT16 )

        if extensionType == EXTENSION_TYPE_SUPPORTED_VERSIONS:
                extension, _ = self.ConsumeList( SIZE_OF_UINT8, self.ConsumeSupportedVersion )
        elif extensionType == EXTENSION_TYPE_KEY_SHARE:
            extension = self.ConsumeKeyShare( msgType )
        elif extensionType == EXTENSION_TYPE_SIGNATURE_ALGORITHMS:
            extension, _ = self.ConsumeList( SIZE_OF_UINT16, self.ConsumeSignatureScheme)
        elif extensionType == EXTENSION_TYPE_SUPPORTED_GROUPS:
            extension, _ = self.ConsumeList( SIZE_OF_UINT16, self.ConsumeSupportedGroup)
        else:
            extension = self.ConsumeRawBytes( extensionSize )

        
        return AttrDict({ NAME           : self.GetExtensionName( extensionType ),
                          RAW_CONTENTS   : rawExtension,
                          INTERPRETATION : extension } )
        # return ( extensionType, rawExtension, extension ) 

    def ConsumeHeadlessList( self, listSize, consumItemFunction, sizeOfListSize = 0 ):
        rawList = self.PeekRawBytes( listSize, sizeOfListSize )

        itemList = []
        startPosition = self.curretPosition
        while self.curretPosition - startPosition < listSize:
            itemList.append( consumItemFunction() )

        if self.curretPosition - startPosition != listSize:
            raise TLSParserError( "Bad list parameters: list size = %d, but consumed %d bytes" % ( listSize, self.curretPosition - startPosition ))

        return itemList, rawList

    def ConsumeList( self, sizeOfListSize, consumItemFunction, expectedListSize = None ):
        if sizeOfListSize == SIZE_OF_UINT8:
            listSize = self.ConsumeByte( expectedListSize )
        elif sizeOfListSize == SIZE_OF_UINT16:
            listSize = self.ConsumeShort( expectedListSize )
        elif sizeOfListSize == SIZE_OF_UINT24:
            listSize = self.ConsumeTrippleByteSize( expectedListSize )
        else: 
            raise TLSParserError( "Unknown size %d" % sizeOfListSize )

        return self.ConsumeHeadlessList( listSize, consumItemFunction, sizeOfListSize )

    def ConsumeLegacyCompression( self ):
        return bytearray( [ self.ConsumeByte( expectedValue = 0 ) ] )

    def ParseServerHello( self ):
        SIZE_OF_RANDOM = 32
        curretPosition = 0

        serverHello = []

        serverHello.append( AttrDict( { NAME : PROTOCOL, RAW_CONTENTS : self.ConsumeRawBytes( SIZE_OF_PROTOCOL ) } ) )
        serverHello.append( AttrDict( { NAME : RANDOM,   RAW_CONTENTS : self.ConsumeRawBytes( SIZE_OF_RANDOM  ) } ) )

        cipherSuite = self.ConsumeCipherSuite()        
        serverHello.append( cipherSuite )
        self.state.selectedCipherSuite = self.ParseShort( cipherSuite.RawContents )
        ################# Extensions:
        extensions, rawExtensions = self.ConsumeList( SIZE_OF_UINT16, 
                                                      partial(  self.ConsumeExtension, 
                                                                msgType = HANDSHAKE_TYPE_SERVER_HELLO ) ) 
        serverHello.append( AttrDict( { NAME : EXTENSIONS, RAW_CONTENTS : rawExtensions, INTERPRETATION : extensions } ) )

        return serverHello

    def ParseClientHello( self ):
        SIZE_OF_RANDOM = 32

        clientHello = []
        clientHello.append( AttrDict( { NAME : PROTOCOL, RAW_CONTENTS : self.ConsumeRawBytes( SIZE_OF_PROTOCOL ) } ) )
        clientHello.append( AttrDict( { NAME : RANDOM,   RAW_CONTENTS : self.ConsumeRawBytes( SIZE_OF_RANDOM  ) } ) )
        
        legacySessionIDSize  = self.ConsumeByte( expectedValue = 0)
        clientHello.append( AttrDict( { NAME : LEGACY_ID,   RAW_CONTENTS : self.PeekRawBytes( 0, SIZE_OF_UINT8 ) } ) ) 

        ############### Cipher suites: 
        cipherSuites, rawCipherSuites = self.ConsumeList( SIZE_OF_UINT16, self.ConsumeCipherSuite ) 
        clientHello.append( AttrDict( { NAME : CIPHER_SUITES, RAW_CONTENTS : rawCipherSuites, INTERPRETATION : cipherSuites } ) ) 

        legacyComression, rawLegacyCompression = self.ConsumeList(  SIZE_OF_UINT8, 
                                                                    self.ConsumeLegacyCompression, 
                                                                    expectedListSize = 1 ) 
        clientHello.append( AttrDict( { NAME : LEGACY_COMPRESSION, RAW_CONTENTS : rawLegacyCompression, INTERPRETATION : str( legacyComression[ 0 ] ) } ) ) 

        ################# Extensions:
        extensions, rawExtensions = self.ConsumeList( SIZE_OF_UINT16, 
                                                      partial(  self.ConsumeExtension, 
                                                                msgType = HANDSHAKE_TYPE_CLIENT_HELLO ) ) 
        clientHello.append( AttrDict( { NAME : EXTENSIONS, RAW_CONTENTS : rawExtensions, INTERPRETATION : extensions } ) )

        return clientHello

    def ParseHelloRetry( self ):
        helloRetry = []
        helloRetry.append( AttrDict( { NAME : PROTOCOL, RAW_CONTENTS : self.ConsumeRawBytes( SIZE_OF_PROTOCOL ) } ) )
        
        rawCipherSuiteID = self.ConsumeRawBytes( SIZE_OF_UINT16 )
        cipherSuiteID    = self.ParseShort( rawCipherSuiteID )
        helloRetry.append( AttrDict( {  NAME            : CIPHER_SUITES, 
                                        RAW_CONTENTS    : rawCipherSuiteID, 
                                        INTERPRETATION  : self.GetCipherSuiteName( cipherSuiteID ) } ) )
        
        extensions, rawExtensions = self.ConsumeList( SIZE_OF_UINT16, 
                                                        partial(  self.ConsumeExtension, 
                                                                  msgType = HANDSHAKE_TYPE_HELLO_RETRY_REQUEST ) )

        helloRetry.append( AttrDict( {  NAME            : EXTENSIONS, 
                                        RAW_CONTENTS    : rawExtensions, 
                                        INTERPRETATION  : extensions } ) )

        return helloRetry

    def ParseKeyFile_parseContent( self, keyFile ):
        HEX_RADIX = 16
        iv        = None
        key       = None

        while iv is None or key is None:
            line           = keyFile.readline()
            header, values = line.split( ":" )
            splitValues    = values.split( "," )
            
            #remove last empty object, if it exists:
            if len( splitValues[ -1 ].strip() ) == 0:
                splitValues = splitValues[ : -1 ]

            data = bytearray( map( lambda x: int( x, HEX_RADIX ), splitValues ) )

            if header.strip().upper() == "KEY":
                key = bytes( data )
            elif header.strip().upper() == "IV":
                iv  = bytes( data )
            else:
                errMsg = "Error loading leaked keys from file %s, Ivalid header: %s" % ( keyFilePath, header )
                self.log.error( errMsg )
                raise TLSParserError( errMsg )

        return iv, key

    def ParseKeyFile( self, keyFilePath ):
        MAX_RETRIES = 3

        with open( keyFilePath, "r" ) as keyFile:
            tryIndex = 0
            try:
                iv, key = self.ParseKeyFile_parseContent( keyFile )
            except:
                tryIndex += 1
                if tryIndex >= MAX_RETRIES:
                    raise

                time.sleep( WAIT_FOR_KEYS_TO_BE_LEAKEDD_SECONDS )

        return iv, key

    def FindMatchingKeys( self ):
        ivsAndKeys  = self.GetLeakedKeys( LEAKED_KEYS_DIR )
        keys        = map( lambda x: x.Key, ivsAndKeys )
        keys        = set( keys )

        keysToFiles = {}
        for k in keys:
            filesWithKey = []
            for leakedSecret in ivsAndKeys:
                if leakedSecret.Key == k:
                    filesWithKey.append( leakedSecret.File )

            keysToFiles[ k ] = filesWithKey

        return keysToFiles

    def FindNewKeys( self, preExistingKeys ):
        postExperimentKeys  = self.FindMatchingKeys()
        newKeys             = set( postExperimentKeys ) - set( preExistingKeys )
        keysAndFiles        = {}
        for k in newKeys:
            keysAndFiles[ k ] = postExperimentKeys[ k ]

        return keysAndFiles

    def DeleteLeakedKeys( self, dirPath = LEAKED_KEYS_DIR ):
        allRuns = glob.glob( dirPath + "/*" )
        allRuns.sort()

        mostRecentDirs =  allRuns[ -self.NUM_RECENT_DIRS: ]
        for dirPath in mostRecentDirs:
            self.log.debug( "Deleting keys in %s" % dirPath )

            allKeyFiles   = glob.glob( dirPath + "/*" )
            for keyFilePath in allKeyFiles:
                os.remove( keyFilePath )

    def GetLeakedKeys( self, dirPath ):
        allRuns = glob.glob( dirPath + "/*" )
        allRuns.sort()

        mostRecentDirs =  allRuns[ -self.NUM_RECENT_DIRS: ]
        ivsAndKeys     = []
        for dirPath in mostRecentDirs:
            self.log.debug( "Extracting keys from %s" % dirPath )

            allKeyFiles   = glob.glob( dirPath + "/*" )
            # if len( allKeyFiles ) == 0 :
            #     time.sleep( 0.1 )
            #     allKeyFiles = glob.glob( dirPath + "/*" )

            allKeyFiles.sort()

            for keyFilePath in allKeyFiles:
                iv, key   = self.ParseKeyFile( keyFilePath )                
                timestamp = os.path.getmtime( keyFilePath )
                keyMaterial = AttrDict( { 'IV' : iv, 'Key' : key, "File" : keyFilePath } )
                ivsAndKeys.append( keyMaterial )

        return ivsAndKeys

    def EncryptRecord( self, rawRecord, iv, key ):
        if self.state.selectedCipherSuite in AES_128_GCM_FAMILY:
            ciphertext, tag = Cryptor.AES_GCM_Encrypt( iv, key, rawRecord )
        elif self.state.selectedCipherSuite == TLS_CHACHA20_POLY1305_SHA256:
            iv, ciphertext, tag = self.openssl.Encrypt_CHACHA20Poly1305( rawRecord, key, iv )
        else:
            raise TLSParserError( "Unknown selectedCipherSuite %d" % self.state.selectedCipherSuite )
        
        return ciphertext + tag

    def NextAEAD_IV( self, nonce, nextSequenceNumber  ):
        sequenceNumberBuff = struct.pack( ">Q", nextSequenceNumber )
        nextIV = bytearray( nonce )
        for i in range( 4, 12 ):
            nextIV[ i ] ^= sequenceNumberBuff[ i - 4 ]

        return bytes( nextIV )
        
    def GetCurrentIV( self, ivAndKey ):
        nonce               = None
        nextSequenceNumber  = 0
        for msg in self.transcript:
            if IV_AND_KEY in msg.keys() and ivAndKey.Key == msg[ IV_AND_KEY ].Key:
                nextSequenceNumber += 1
                if nonce == None: # The first IV to be used is actually the nonce
                    nonce = msg[ IV_AND_KEY ].IV[ : ]

        if nonce != None:
            return self.NextAEAD_IV( nonce, nextSequenceNumber )
        # else:
        # ivAndKey.Key was never used before to decrypt message                    
        return ivAndKey.IV

    def DecryptMsgBody_tryToDecrypt( self, ivsAndKeys, cipherText, tag, automaticallyAdvanceIV ):
        plaintext        = None
        correctIVAndKey  = None
        for secret in ivsAndKeys:
            try:
                if automaticallyAdvanceIV:
                    nextIV = self.GetCurrentIV( secret )
                else:
                    nextIV = secret.IV

                if self.state.selectedCipherSuite in AES_128_GCM_FAMILY:
                    plaintext = Cryptor.AES_GCM_Decrypt( nextIV, secret.Key, cipherText, tag )

                elif self.state.selectedCipherSuite == TLS_CHACHA20_POLY1305_SHA256:
                    plaintext = self.openssl.Decrypt_CHACHA20Poly1305( secret.Key, nextIV, cipherText, tag )

                else:
                    raise TLSParserError( "Unknown selectedCipherSuite %s" % self.state.selectedCipherSuite)

                correctIVAndKey = AttrDict( { 'Key' : secret.Key[ : ], 'IV' : nextIV[:]} )
                
                break
            except (cryptography.exceptions.InvalidTag, OpenSSLError):
                pass

        return plaintext, correctIVAndKey

    def DecryptMsgBody( self, rawRecord, fixedIVAndKey ):
        SIZE_OF_AES_GCM_TAG                 = 16 

        cipherText  = rawRecord[ : -SIZE_OF_AES_GCM_TAG ]
        tag         = rawRecord[ -SIZE_OF_AES_GCM_TAG : ]
        
        if fixedIVAndKey != None:
            ivsAndKeys              = [ fixedIVAndKey ] 
            automaticallyAdvanceIV  = False
        else:
            ivsAndKeys              = self.GetLeakedKeys( LEAKED_KEYS_DIR )
            automaticallyAdvanceIV  = True

        plaintext, ivAndKey = self.DecryptMsgBody_tryToDecrypt( ivsAndKeys, cipherText, tag, automaticallyAdvanceIV )

        if( plaintext == None ):
            time.sleep( WAIT_FOR_KEYS_TO_BE_LEAKEDD_SECONDS )
            ivsAndKeys          = self.GetLeakedKeys( LEAKED_KEYS_DIR )
            plaintext, ivAndKey = self.DecryptMsgBody_tryToDecrypt( ivsAndKeys, cipherText, tag, automaticallyAdvanceIV )

        if plaintext == None:
            errMsg = "Can't decrypt meesage"
            self.log.error( errMsg )
            raise TLSParserDecryptionError( errMsg )

        return plaintext, ivAndKey

    def ConsumeHandshake( self ):
        handshakeMsg                    = {}
        handshakeMsg[ HANDSHAKE_TYPE ]  = self.ConsumeByte()
        handshakeMsg[ LENGTH  ]         = self.ConsumeTrippleByteSize()

        rawHandshakeMsg = self.PeekRawBytes( handshakeMsg[ LENGTH  ] )
        startPosition   = self.curretPosition

        if handshakeMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_CLIENT_HELLO:
            handshakeMsg[ HANDSHAKE_MSG ] = self.ParseClientHello()

        elif handshakeMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_SERVER_HELLO:
            handshakeMsg[ HANDSHAKE_MSG ] = self.ParseServerHello()

        elif handshakeMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_HELLO_RETRY_REQUEST:
            handshakeMsg[ HANDSHAKE_MSG ] = self.ParseHelloRetry()

        elif handshakeMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_ENCRYPTED_EXTENSIONS:
            extensions, rawExtensions = self.ConsumeList(   SIZE_OF_UINT16, 
                                                partial( self.ConsumeExtension, 
                                                         msgType = handshakeMsg[ HANDSHAKE_TYPE ] ) )
            handshakeMsg[ HANDSHAKE_MSG  ] = [  AttrDict( { NAME : EXTENSIONS, RAW_CONTENTS : rawExtensions, INTERPRETATION : extensions } ) ] 
            
        
        elif handshakeMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_CERTIFICATE:
            certificates = self.ConsumeCertificate()
            handshakeMsg[ HANDSHAKE_MSG  ] = [ AttrDict( { NAME : CERTIFICATES, RAW_CONTENTS : rawHandshakeMsg, INTERPRETATION : certificates } )]

        elif handshakeMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_CERTIFICATE_VERIFY:
            certificateVerify = self.ConsumeCertificateVerify()
            handshakeMsg[ HANDSHAKE_MSG  ] = [ AttrDict( { NAME : CERTIFICATE_VERIFY, RAW_CONTENTS : rawHandshakeMsg, INTERPRETATION : certificateVerify } )]
           
        else:
            _ = self.ConsumeRawBytes( handshakeMsg[ LENGTH  ] )
            handshakeMsg[ HANDSHAKE_MSG  ]   = [ AttrDict( { NAME : RAW_MSG, RAW_CONTENTS : rawHandshakeMsg } ) ]

        if self.curretPosition - startPosition != handshakeMsg[ LENGTH  ]:
            raise TLSParserError( "handshakeMsg[ LENGTH  ] = %d, bute consumed %d bytes" % ( handshakeMsg[ LENGTH  ], self.curretPosition - startPosition))

        return handshakeMsg

    def RebuildRawContentFromInterpretation( self, node, bytesRemoved ):
        rawBody = b""
        header  = b""

        for item in node.Interpretation:
            rawBody += item.RawContents

        if node.Name in EXTENSION_TYPE_NAMES.values():
            SIZEOF_EXTENSION_TYPE = SIZE_OF_UINT16
            SIZEOF_EXTENSION_SIZE = SIZE_OF_UINT16
            
            #The following is the extraBytes after substructing the ExtensionType and OpaqueExtensionSize
            extraBytes =    len( node.RawContents ) - \
                            bytesRemoved            - \
                            SIZEOF_EXTENSION_TYPE -   \
                            SIZEOF_EXTENSION_SIZE -   \
                            len( rawBody )

            extensionType       = node.RawContents[ : SIZEOF_EXTENSION_TYPE ]
            opaqueExtensionSize = struct.pack( ">H", len( rawBody ) + extraBytes )

            header = extensionType + opaqueExtensionSize
        else:
            extraBytes = len( node.RawContents ) - len( rawBody ) - bytesRemoved

        if extraBytes == 0:
            return header + rawBody

        if extraBytes == 1:
            rawSize = bytes( [ len( rawBody ) ] )
            return header + rawSize + rawBody

        if extraBytes == 2:
            rawSize = struct.pack( ">H", len( rawBody ) )
            return header + rawSize + rawBody

        if extraBytes == 3:
            rawSize = struct.pack( ">I", len( rawBody ))[  -SIZE_OF_UINT24 : ]
            return header + rawSize + rawBody

        raise TLSParserError( "Unexpeded extraBytes = %d" % extraBytes )

    def FindNodeWithName( self, msg, nodeName ):
        routeToNode = []
        # DFS search for nodeName:
        for item in msg:            
            if item[ NAME ] == nodeName:
                return item, routeToNode

            if not self.IsTerminalPiece( item ):
                node, subrouteToNode = self.FindNodeWithName( item.Interpretation, nodeName )                
                if node != None:
                    routeToNode += [ item ] + subrouteToNode
                    return node, routeToNode

        return None, None

    def ManipulateAndReconstruct( self, originalMsg ):
        # Run manipulation in order on originalMsg. If any manipulation was performed
        # then reconstruct the wire frame and return it. Otherwise return None.

        isMsgManipulated = False
        msg              = originalMsg

        for manipulation in self.msgManipulators:
            manipulatedMsg = self.ManipulateMsg( msg, manipulation ) 
            if manipulatedMsg != None:
                msg              = manipulatedMsg #prepare for next potential manipulation
                isMsgManipulated = True

        if isMsgManipulated:
            self.transcript.pop()

            wireMsg      = b""
            plainTextMsg = None
            if EXTRACT_TO_PLAINTEXT in manipulatedMsg.keys():
                plainTextMsg = manipulatedMsg[ EXTRACT_TO_PLAINTEXT ]
                wireMsg     += self.ReconstructRecordAndCompareToOriginal( plainTextMsg, doCompare = False )
                self.transcript.append( plainTextMsg )

            wireMsg += self.ReconstructRecordAndCompareToOriginal( manipulatedMsg, doCompare = False )
            self.transcript.append( manipulatedMsg )

            if config.LOG_LEVEL < logging.ERROR:
                print( "================== Manipulated Message =====================" )
                
                if plainTextMsg != None:
                    self.PrintMsg( plainTextMsg )

                self.PrintMsg( msg )

            return wireMsg
        # else:
        return None


    def CreateHandshakeRecord( self, handshakeMsg, direction ):
        msg = {}
        msg[ RECORD      ] = [ handshakeMsg ]
        msg[ RECORD_TYPE ] = TLS_RECORD_TYPE_HANDSHAKE
        msg[ PROTOCOL    ] = self.TLS_1_3_MAGIC
        msg[ DIRECTION   ] = direction
        msg[ LENGTH      ] = -1 

        return msg
    
    def ManipulateMsg_TopLevel( self, msg, manipulation ):
        if SWAP_ITEMS in manipulation.keys():
            swapIDs = manipulation[ SWAP_ITEMS ]
            items   = msg[ RECORD ]

            if swapIDs.index1 >= len( items ) or swapIDs.index2 >= len( items ):
                return None

            pprint(  items[ swapIDs.index1 ] )
            handshakeName1 = self.GetHandshakeType( items[ swapIDs.index1 ][ HANDSHAKE_TYPE ] )
            handshakeName2 = self.GetHandshakeType( items[ swapIDs.index2 ][ HANDSHAKE_TYPE ] )
            manipulation[ "Description" ] = "Swapping %s <--> %s" % ( handshakeName1, handshakeName2 )
            items[ swapIDs.index1 ], items[ swapIDs.index2 ] = items[ swapIDs.index2 ], items[ swapIDs.index1 ] 

            return msg
        # else:
        handshakeMsgToExtract = None
        if EXTRACT_TO_PLAINTEXT in manipulation.keys() and msg[ RECORD_TYPE ] == TLS_RECORD_TYPE_APP_DATA:
            for handshakeMsg in msg[ RECORD ]:
                if handshakeMsg[ HANDSHAKE_TYPE ] == manipulation[ HANDSHAKE_TYPE ]:
                    handshakeMsgToExtract = handshakeMsg

            msg[ RECORD ].remove( handshakeMsgToExtract )
            msg[ EXTRACT_TO_PLAINTEXT ] = self.CreateHandshakeRecord( handshakeMsgToExtract, msg[ DIRECTION ] )

            manipulation[ "Description" ] = "Extracting %s to plaintext" % ( self.GetHandshakeType( handshakeMsgToExtract[ HANDSHAKE_TYPE ] ) )

            return msg

        return None

    def ManipulateMsg( self, msg, manipulation ):
        if  ALERT in msg.keys() or \
            self.IsMsgContainsOnlyAppData( msg ):
            return None

        msg = deepcopy( msg )
        
        if manipulation[ PARENT_NODE ] == RECORD and manipulation[ DIRECTION ] == msg[ DIRECTION ]:
            return self.ManipulateMsg_TopLevel( msg, manipulation )
          
        # else:
        handshakeMsgToManipulate = None
        if HANDSHAKE_TYPE in manipulation.keys():
            for handshakeMsg in msg[ RECORD ]:
                if handshakeMsg[ HANDSHAKE_TYPE ] == manipulation[ HANDSHAKE_TYPE ]:
                    handshakeMsgToManipulate = handshakeMsg
        
        if handshakeMsgToManipulate is None:
            return None
        
        # else:      
        if PARENT_NODE in manipulation.keys():
            parentNodeName      = manipulation[ PARENT_NODE ]
            node, routeToNode   = self.FindNodeWithName( handshakeMsgToManipulate[ HANDSHAKE_MSG ], manipulation[ PARENT_NODE ] )
            bytesRemoved        = 0

            if SWAP_ITEMS in manipulation.keys():
                swapIDs = manipulation[ SWAP_ITEMS ]
                items   = node.Interpretation
                
                if max( swapIDs.index1, swapIDs.index2 ) >= len( items ):
                    logMsg = "Can't swap indices %d <--> %d, because %s has only only %d children" % ( swapIDs.index1, swapIDs.index2, node.Name, len( items ) )
                    self.log.warning( logMsg )
                    manipulation[ "Description" ] = "Skipped manipulation: " + logMsg
                    return None

                if  TLSParser.IsTerminalPiece( node.Interpretation[ swapIDs.index1 ] ) and \
                    TLSParser.IsTerminalPiece( node.Interpretation[ swapIDs.index2 ] ):
                    index1Name = node.Interpretation[ swapIDs.index1 ].Interpretation
                    index2Name = node.Interpretation[ swapIDs.index2 ].Interpretation
                else:
                    index1Name = node.Interpretation[ swapIDs.index1 ].Name
                    index2Name = node.Interpretation[ swapIDs.index2 ].Name
                
                manipulation[ "Description" ] = "Swapping  children of %s: %s <--> %s" % ( node.Name, index1Name, index2Name )

                items[ swapIDs.index1 ], items[ swapIDs.index2 ] = items[ swapIDs.index2 ], items[ swapIDs.index1 ]
            
            elif REMOVE_ITEM in manipulation.keys():
                itemIDToRemove  = manipulation[ REMOVE_ITEM ]
                items           = node.Interpretation
                if itemIDToRemove >= len( items ):
                    logMsg = "Can't delete from %s at location %d there only only %d children" % ( node.Name, itemIDToRemove, len( items ) )
                    self.log.warning( logMsg )
                    manipulation[ "Description" ] = "Skipped manipulation: " + logMsg
                    return None

                bytesRemoved    = len( items[ itemIDToRemove ].RawContents )

                if  TLSParser.IsTerminalPiece( node.Interpretation[ itemIDToRemove ] ):
                    name = node.Interpretation[ itemIDToRemove].Interpretation
                else:
                    name = node.Interpretation[ itemIDToRemove ].Name
                    
                manipulation[ "Description" ] = "Removing %s from %s" % ( name, node.Name )
                del items[ itemIDToRemove ]

            nodesToRebuild = routeToNode + [ node ]
            nodesToRebuild.reverse()
            # pprint( nodesToRebuild )
            for modifiedNode in nodesToRebuild:
                modifiedNode.RawContents = self.RebuildRawContentFromInterpretation( modifiedNode, bytesRemoved )

        # pprint( "msg after manipulation = %s" % msg )
        return msg

    def SetMsgManipulators( self, msgManipulators ):
        self.msgManipulators = msgManipulators

    @staticmethod
    def IsTerminalPiece( piece ):
        if INTERPRETATION not in piece.keys():
            return True

        if (type( piece.Interpretation ) is str) or \
           (type( piece.Interpretation ) is bytes):
            return True

        return False

    def PrintTerminalPiece( self, prefix, piece ):
        if len( piece.RawContents ) == 2:
            valueStr = Blue( "0x%04X" % self.ParseShort( piece.RawContents ) )
        elif len( piece.RawContents ) == 1:
            valueStr = Blue( "0x%02X" %  piece.RawContents[ 0 ] )
        else:
            if INTERPRETATION in piece.keys():
                size = len( piece.Interpretation )
            else:
                size = len( piece.RawContents )
            valueStr = Green( "; Size: ") + Blue( "%d" % size )

        if INTERPRETATION in piece.keys():
            if len( piece.Interpretation ) < 64:
                valueStr += ": " + Yellow( str( piece.Interpretation ) ) 
            else:
                valueStr += ": " + Yellow( "<content to big to print>" ) 

        sys.stdout.write( prefix + Green( piece.Name + ": ") + valueStr + "\n" )

    def PrintPieceTree( self, prefix, pieceTree ):
        for piece in pieceTree:
            if self.IsTerminalPiece( piece ):
                self.PrintTerminalPiece( prefix[ -1 ], piece )
            else:
                sys.stdout.write( prefix[ -1 ]  + Green( piece.Name + ": ") + "\n" )
                prefix.append(  "---" + prefix[ -1 ] )
                self.PrintPieceTree( prefix[:], piece.Interpretation )
                prefix = prefix[ : -1 ]


    def PrintSingleMsg( self, singleMsg ):
        prefix = [ "---------------->" ]
        sys.stdout.write( prefix[ -1 ] +  
                            Green( HANDSHAKE_TYPE + ": " ) +  
                            Yellow( "%-20s (%d); "  
                                % ( self.GetHandshakeType( singleMsg[ HANDSHAKE_TYPE ] ), singleMsg[ HANDSHAKE_TYPE ]  )  ) + 
                            Green( LENGTH + ":" ) + Blue( "%5d" % singleMsg[ LENGTH ] ) + "\n" )

        prefix.append(  "---" + prefix[ -1 ] )

        if singleMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_HELLO_RETRY_REQUEST:
            self.PrintPieceTree( prefix[:], singleMsg[ HANDSHAKE_MSG ] )            
            return

        for piece in singleMsg[ HANDSHAKE_MSG ]:
            self.PrintPieceTree( prefix[:], [ piece ] )
            



    def VerifyEqual( self, val1, val2, doNotRaise = False ):
        if val1 != val2:
            errMsg = "%s != %s" % ( val1, val2 )
            self.log.error( errMsg )

            if doNotRaise:
                return
            raise TLSParserError( errMsg )

    def CompareHandshakeMsg( self, handshakeMsg1, handshakeMsg2 ):
        self.VerifyEqual( handshakeMsg1[ HANDSHAKE_TYPE ],    handshakeMsg2[ HANDSHAKE_TYPE ] )
        
        sys.stdout.write(   Green( HANDSHAKE_TYPE + ": " ) +  
                            Yellow( "%-20s (%d); "  
                                % ( self.GetHandshakeType( handshakeMsg1[ HANDSHAKE_TYPE ] ), handshakeMsg1[ HANDSHAKE_TYPE ]  )  ) + 
                             "\n" )

        for piece1, piece2 in zip( handshakeMsg1[ HANDSHAKE_MSG ], handshakeMsg2[ HANDSHAKE_MSG ] ):
            PREFIX1 = "---->"
            PREFIX2 = "----" + PREFIX1

            self.VerifyEqual( piece1.Name, piece2.Name )
            sys.stdout.write( Green( "Comparing " ) + Yellow( "%-20s" % piece1.Name ) + ": " )
            if piece1.RawContents == piece2.RawContents:
                sys.stdout.write( Blue( "SAME" ) + "\n" )
            else: 
                sys.stdout.write( Blue( "DIFFERENT" ) + "\n")
                self.VisuallyCompareBuffers( piece1.RawContents, piece2.RawContents, PREFIX1 )

            if  INTERPRETATION in piece1.keys() and type( piece1.Interpretation ) == list :
                for content1, content2 in zip( piece1.Interpretation, piece2.Interpretation ) :
                    if type( content1 ) == tuple:
                        sys.stdout.write( "------------------- Comparing " + Yellow( "%s" % content1.Name))

                        if piece1[ PIECE_NAME ] == EXTENSIONS:
                            sys.stdout.write( Yellow( " %s\n" % self.GetExtensionName( content1.Name)))
                        else:
                            print( "" )

                        self.VisuallyCompareBuffers( content1.RawContents, content2.RawContents, PREFIX2 )                    



    def VisuallyCompareBuffers( self, buff1, buff2, prefix = "" ):
        maxLength = max( len( buff1 ), len( buff2 ) )

        LINE_WIDTH  = 8
        numLines    = maxLength // LINE_WIDTH + 1
        
        for lineIdx in range( numLines ):
            sys.stdout.write( prefix )
            for colIdx in range( LINE_WIDTH ):
                byteIdx = lineIdx * LINE_WIDTH + colIdx
                if byteIdx >= len( buff1 ):
                    sys.stdout.write( Green( "----, " ) )
                elif byteIdx >= len( buff2 ):
                    sys.stdout.write( Blue( "0x%2X, " % buff1[ byteIdx ] ) )
                elif buff1[ byteIdx ] == buff2[ byteIdx ]:
                    sys.stdout.write( Green( "0x%2X, " % buff1[ byteIdx ] ) )
                else:
                    sys.stdout.write( Red( "0x%2X, " % buff1[ byteIdx ] ) )

            sys.stdout.write( " |  " )

            for colIdx in range( LINE_WIDTH ):
                byteIdx = lineIdx * LINE_WIDTH + colIdx
                if byteIdx >= len( buff2 ):
                    sys.stdout.write( Green( "----, " ) )
                elif byteIdx >= len( buff1 ):
                    sys.stdout.write( Blue( "0x%2X, " % buff2[ byteIdx ] ) )   
                elif buff1[ byteIdx ] == buff2[ byteIdx ]:
                    sys.stdout.write( Green( "0x%2X, " % buff2[ byteIdx ] ) )
                else:
                    sys.stdout.write( Red( "0x%2X, " % buff2[ byteIdx ] ) )

            print( "" )

    def CompareMsgs( self, msg1, msg2 ):
        self.VerifyEqual( msg1[ DIRECTION ],    msg2[ DIRECTION ])
        self.VerifyEqual( msg1[ RECORD_TYPE ],  msg2[ RECORD_TYPE ])
        self.VerifyEqual( msg1[ PROTOCOL ],     msg2[ PROTOCOL ],   doNotRaise = True)
        self.VerifyEqual( msg1[ LENGTH ],       msg2[ LENGTH ],     doNotRaise = True)

        isRecordEncrypted_1 = ( DECRYPTED_RECORD in msg1.keys() )
        isRecordEncrypted_2 = ( DECRYPTED_RECORD in msg2.keys() )
        self.VerifyEqual( isRecordEncrypted_1, isRecordEncrypted_2 )

        print( "--------------------------%-15s. Comparing RAW record ----------------" % msg1[ DIRECTION ] )

        if isRecordEncrypted_1:
            self.VerifyEqual( msg1[ DECRYPTED_RECORD_TYPE ],    msg2[ DECRYPTED_RECORD_TYPE ])
            self.VisuallyCompareBuffers( msg1[ DECRYPTED_RECORD ], msg2[ DECRYPTED_RECORD ] )
        else:
            self.VisuallyCompareBuffers( msg1[ RAW_RECORD ], msg2[ RAW_RECORD ] )

        print( "----------------- Comparing pieces ----------------")
        for idx, (handshakeMsg1, handshakeMsg2) in enumerate( zip( msg1[ RECORD ], msg2[ RECORD ] ) ):
            sys.stdout.write( Green( "Comparing handshake message ") + Blue( "%d; " % idx ) )
            self.CompareHandshakeMsg( handshakeMsg1, handshakeMsg2 )

    def PrintMsgHeader( self, msg ):
        sys.stdout.write(   Red( msg[ DIRECTION ] + "  " ) + 
                            Green( RECORD_TYPE + ": " ) + Yellow( "%-18s (0x%x)" ) % 
                                ( self.GetTLSRecordMsgType( msg[ RECORD_TYPE ] ), msg[ RECORD_TYPE ] ) + 
                            Green( " length: ")   + Blue( "%5d" % msg[ LENGTH ] ) + 
                            Green( " protocol: ") + Magenta( str( msg[ PROTOCOL ] ) ) + ";\n")

    def PrintMsg( self, msg ):
        # pprint( msg )
        self.PrintMsgHeader( msg )

        if ALERT in msg.keys():
            alert = msg[ ALERT ]
            print( Red( "ALERT: " ) + Green( "Level: " ) + Blue( alert.Level ) + Green( "; Type: " ) + Yellow( alert.Type ) )
            
        elif self.IsMsgContainsOnlyAppData( msg ):
            print( Green( "App data: " ) + Magenta( str( msg[ RECORD ] ) ) )
        
        elif RECORD in msg.keys():
            for singleMsg in msg[ RECORD ]:
                self.PrintSingleMsg( singleMsg )
        
        else:
            print( Red( "<Can't decrypt record!>" ) ) 
        
    def VerifyBuffersEquall( self, buffer1, buffer2 ):
        if len( buffer1 ) != len( buffer2 ):
            raise TLSParserError( "len( buffer1 ) != len( buffer2 ): %d != %d" 
                % ( len( buffer1 ) , len( buffer2 ) ))

        for byteIdx in range( len( buffer1 ) ):
            if buffer1[ byteIdx ] != buffer2[ byteIdx ]:
                print("Error-------------------:")
                self.VisuallyCompareBuffers( buffer1, buffer2 )
                raise TLSParserError( "Buffers are different at byte %d" % byteIdx )    

    def ReconstructExtensions( self, extensionsList ):
        RAW_CONTENTS = 1

        rawExtensions = b""
        for extension in extensionsList:
            rawExtensions += extension.RawContents

        extensionsHeader = struct.pack( ">H", len( rawExtensions ) )

        return extensionsHeader + rawExtensions

    def ReassembleHandshakes( self, parsedRecord ):
        PIECE_NAME              = 0
        RAW_CONTENTS            = 1
        PIECE_INTERPRETATION    = 2

        reconstructedRawRecord = b""
        for handshakeMsg in parsedRecord:
            reconstructedMsg = b""

            if handshakeMsg[ HANDSHAKE_TYPE ] == HANDSHAKE_TYPE_HELLO_RETRY_REQUEST:
                for piece in handshakeMsg[ HANDSHAKE_MSG ]:
                    reconstructedMsg += piece.RawContents

            else:
                for piece in handshakeMsg[ HANDSHAKE_MSG ]:
                    if type( piece ) == AttrDict:
                        reconstructedMsg += piece.RawContents
                    elif piece[ PIECE_NAME ] == EXTENSIONS:
                        reconstructedMsg += self.ReconstructExtensions( piece[ PIECE_INTERPRETATION ] )
                    else:
                        reconstructedMsg += piece[ RAW_CONTENTS ]
                
            handshakeMsgSize = struct.pack( ">I", len( reconstructedMsg ))[  -SIZE_OF_UINT24 : ]
            reconstructedRawRecord +=   bytearray( [ handshakeMsg[ HANDSHAKE_TYPE ] ] ) + \
                                        handshakeMsgSize                                + \
                                        reconstructedMsg

        return reconstructedRawRecord

    @staticmethod
    def IsMsgContainsOnlyAppData( msg ):
        return DECRYPTED_RECORD_TYPE in msg.keys() and \
               msg[ DECRYPTED_RECORD_TYPE ] == TLS_RECORD_TYPE_APP_DATA

    def ReconstructRecordAndCompareToOriginal( self, parsedMsg, doCompare = True ):
        PIECE_NAME              = 0
        RAW_CONTENTS            = 1
        PIECE_INTERPRETATION    = 2
        # pprint( parsedMsg )
        if self.IsMsgContainsOnlyAppData( parsedMsg ):
            reconstructedRawRecord = parsedMsg[ RECORD ]
        else:
            reconstructedRawRecord = self.ReassembleHandshakes( parsedMsg[ RECORD ] )
        
        isRecordEncrypted = ( DECRYPTED_RECORD in parsedMsg.keys() )
        if isRecordEncrypted:
            reconstructedRawRecord += bytearray([ parsedMsg[ DECRYPTED_RECORD_TYPE ] ])

            if doCompare:
                self.VerifyBuffersEquall( reconstructedRawRecord, parsedMsg[ DECRYPTED_RECORD ] + bytearray( [ parsedMsg[ DECRYPTED_RECORD_TYPE ]]))
            
            encryptedRecord = self.EncryptRecord(   reconstructedRawRecord, 
                                                    parsedMsg[ IV_AND_KEY ].IV,
                                                    parsedMsg[ IV_AND_KEY ].Key )

            recordHeader = bytearray( [  parsedMsg[ RECORD_TYPE ] ] )                           + \
                                                    parsedMsg[ PROTOCOL ]                       + \
                                                    struct.pack( ">H", len( encryptedRecord ) )  
            reconstructedRawRecord =  recordHeader + encryptedRecord                                 

        else:
            recordHeader            = bytearray( [  parsedMsg[ RECORD_TYPE ] ] )                        + \
                                                    parsedMsg[ PROTOCOL ]                               + \
                                                    struct.pack( ">H", len( reconstructedRawRecord ) )                      
            reconstructedRawRecord  = recordHeader + reconstructedRawRecord
            
        if doCompare:
            self.VerifyBuffersEquall( reconstructedRawRecord, parsedMsg[ RAW_RECORD ] )

        return reconstructedRawRecord
        
    def ConsumeAlert( self ):
        alert                 = AttrDict()
        alert[ RAW_CONTENTS ] = self.ConsumeRawBytes( SIZE_OF_UINT16 )

        alertLevelID          = alert[ RAW_CONTENTS ][ 0 ]
        alertDescriptionID    = alert[ RAW_CONTENTS ][ 1 ]

        if alertLevelID == 1:
            alert.Level = "warning"
        elif alertLevelID == 2:
            alert.Level = "fatal"
        else:
            alert.Level = "unknown alert level"

        alert.Type = self.GetAlertType( alertDescriptionID )

        return alert

    def IsAlertMsg( self, msg ):
        return ALERT in msg.keys()

    def ParseMsgBody( self, msg, fixedIVAndKey ):
        totalRecordSize     = TLS_RECORD_HEADER_SIZE + msg[ LENGTH ]
        msg[ RAW_RECORD ]   = self.PeekRawBytes( totalRecordSize - TLS_RECORD_HEADER_SIZE, TLS_RECORD_HEADER_SIZE )

        if msg[ RECORD_TYPE ] == TLS_RECORD_TYPE_HANDSHAKE:
            msg[ RECORD ] = [ self.ConsumeHandshake() ]
            self.VerifyEqual( self.curretPosition, totalRecordSize )
            # pprint( msg )
            self.ReconstructRecordAndCompareToOriginal( msg )

        elif msg[ RECORD_TYPE ] == TLS_RECORD_TYPE_APP_DATA:
            encryptedMsgBody             = self.ConsumeRawBytes( msg[ LENGTH ] ) 
            self.VerifyBuffersEquall( encryptedMsgBody, msg[ RAW_RECORD ][ TLS_RECORD_HEADER_SIZE: ] )

            rawDecryptedRecord, ivAndKey  = self.DecryptMsgBody( encryptedMsgBody, fixedIVAndKey ) 
            msg[ DECRYPTED_RECORD_TYPE ] = rawDecryptedRecord[ -1 ]
            msg[ DECRYPTED_RECORD      ] = rawDecryptedRecord[ : -1 ]
            msg[ IV_AND_KEY            ] = ivAndKey

            # replace encrypted message with derypted one:
            self.TrunctateConsumedBytes()
            self.recentBytes = msg[ DECRYPTED_RECORD ] + self.recentBytes

            if msg[ DECRYPTED_RECORD_TYPE ] == TLS_RECORD_TYPE_HANDSHAKE:
                msg[ RECORD ], _ = self.ConsumeHeadlessList( len( msg[ DECRYPTED_RECORD ] ), self.ConsumeHandshake )
                self.VerifyEqual( self.curretPosition, len( msg[ DECRYPTED_RECORD ] ) )
            elif msg[ DECRYPTED_RECORD_TYPE ] == TLS_RECORD_TYPE_ALERT:
                msg[ ALERT ] = self.ConsumeAlert()
                self.log.error( "Received ALERT inside app data: %s" % str( msg[ ALERT ] ) )
            elif msg[ DECRYPTED_RECORD_TYPE ] == TLS_RECORD_TYPE_APP_DATA:
                msg[ RECORD ] = self.ConsumeRawBytes( len( msg[ DECRYPTED_RECORD ] ) )
            else:
                raise TLSParserError( "Unknown DECRYPTED_RECORD_TYPE %d" % msg[ DECRYPTED_RECORD_TYPE ] )

            if not self.IsAlertMsg( msg ):
                self.ReconstructRecordAndCompareToOriginal( msg )

        elif msg[ RECORD_TYPE ] == TLS_RECORD_TYPE_ALERT:
            msg[ ALERT ] = self.ConsumeAlert()
            self.log.error( "Received ALERT: %s" % str( msg[ ALERT ] ) )
        else:
            raise TLSParserError( "Unknown RECORD_TYPE %d" % msg[ RECORD_TYPE ] )

        if config.LOG_LEVEL < logging.ERROR:
                self.PrintMsg( msg )

        return msg

    def VerifyAmountOfConsumedBytes( self, expectedAmount ):
        if self.curretPosition != expectedAmount:
            raise TLSParserError( "Consumed %d bytes instead of expected %d" % ( self.curretPosition, expectedAmount ))

    def TrunctateConsumedBytes( self ):
        self.recentBytes    = self.recentBytes[ self.curretPosition : ]
        self.curretPosition = 0

    def Digest( self, bytes, direction, printPacket = False, ivAndKey = None ):
        if config.LOG_LEVEL < logging.ERROR and printPacket:
            print( direction )
            sys.stdout.write( Green( self.FormatBuffer( bytes ) )  + "\n" )

        self.recentBytes += bytes

        msgs = []
        while len( self.recentBytes ) >= TLS_RECORD_HEADER_SIZE:         
            msg             = self.ParseMsgHeader( direction )
            totalRecordSize = TLS_RECORD_HEADER_SIZE + msg[ LENGTH ]
            # pprint( msg )
            if len( self.recentBytes ) >= totalRecordSize:
                try:
                    self.ParseMsgBody( msg, fixedIVAndKey = ivAndKey )
                except TLSParserDecryptionError as err:
                    pprint( traceback.format_tb( err.__traceback__ ) )
                    print( err )
                    self.PrintMsg( msg )
                    # exception is silenced
                    
                finally:
                    self.TrunctateConsumedBytes()                
                    msgs.append( msg )

            self.transcript.append( msg )
        
        return msgs

    def GetAlerts( self ):
        alerts = []
        for msg in self.transcript:
            if ALERT in msg.keys():
                alerts.append( msg )

        return alerts

    @staticmethod
    def FormatBuffer( buffer, prefix = "", lineSeperator = "\n" ):
        humanReadableBuffer = prefix
        for i, byte in enumerate( buffer ):
          humanReadableBuffer += "0x%2X, " % byte 
          if ( i + 1 ) % 8 == 0:
              humanReadableBuffer += lineSeperator
              if i + 1 < len( buffer ):
                humanReadableBuffer += prefix

        return humanReadableBuffer

    @staticmethod
    def DumpTranscript( transcript ):
        TRANSCRIPTS_DIR = "transcripts"
        MSG_FILENAME    = "msg-%02d-%s.bin"
        timestamp       = datetime.datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d_%H-%M-%S')
        transcriptsDir  =  TRANSCRIPTS_DIR + "/" + timestamp

        os.makedirs( transcriptsDir )
        
        print( "Dumping raw transcript to %s" % transcriptsDir )
        for msgIdx, msg in enumerate( transcript ):
            msgFileName = transcriptsDir + "/" + MSG_FILENAME % ( msgIdx, msg[ DIRECTION ] )
            print( "Dumping %s" % msgFileName )
            with open( msgFileName, "wb" ) as msgFile:
                msgFile.write( msg[ RAW_RECORD ] )

    def GetMsgFromFile( self, msgFilePath ):
        with open( msgFilePath, "rb" ) as msgFile:
            rawMsg = msgFile.read()

        if Direction.CLIENT_TO_SERVER in msgFilePath:
            direction = Direction.CLIENT_TO_SERVER
        elif Direction.SERVER_TO_CLIENT in msgFilePath:
            direction = Direction.SERVER_TO_CLIENT
        else:
            raise Exception( "Unknown direction" )

        return self.Digest( rawMsg, direction )

def CString( pythonString ):
    NULL_BYTE = b"\0"
    return c_char_p( bytes( pythonString, "ascii" ) + NULL_BYTE )

class FileSocket():
    SLEEP_INTERVAL_SECONDS = 0.05

    def __init__( self, clientToServerFilePathTemplate, serverToClientFilePathTemplate, readTimeout = 0.5 ):
        basePath = os.path.dirname( clientToServerFilePathTemplate )
        if not os.path.exists( basePath ):
            os.makedirs( basePath )

        basePath = os.path.dirname( serverToClientFilePathTemplate )
        if not os.path.exists( basePath ):
            os.makedirs( basePath )

        self.clientToServerFilePathTemplate = clientToServerFilePathTemplate
        self.serverToClientFilePathTemplate = serverToClientFilePathTemplate
        self.currentFileID                  = 0
        self.readTimeout                    = readTimeout

        self.client = AttrDict( { 'bufferAddr' : None, 'fileSize' : 0, 'offset' : 0 } )
        self.server = AttrDict( { 'bufferAddr' : None, 'fileSize' : 0, 'offset' : 0 } )

        self.cutils                         = CDLL( "cutils/cutils.dll" )
        self.cutils.ReadFromFile.restype    = c_uint32

        self.SetupLogger()

    def SetupLogger( self ):
        self.log = logging.getLogger( 'FileSocket' )
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL   )
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler)  

    def BytesLeftToRead( self, entity ):
        return entity.fileSize - entity.offset  

    def ReadBytesFromFile( self, entity, filePath ):
        if sys.platform == "win32":
            entity.bufferAddr      = c_voidp( None )
            entity.fileSize        = self.cutils.ReadFromFile( CString( filePath ), byref( entity.bufferAddr ) )
            entity.currentOffset   = 0
        else:
            raise NotImplementedError()

    def IsDataAvailable( self, entity, filePath ):
        startTime = time.time()
        while self.BytesLeftToRead( entity ) == 0 and os.path.exists( filePath ) == False:
            time.sleep( self.SLEEP_INTERVAL_SECONDS )
            if( time.time() - startTime > self.readTimeout ):
                self.log.error( "ReadFromClient: timeout expired" )
                return False

        return True

    def SendToClient( self, ctx, buffer, bufferSize ):
        self.log.debug( "SendToClient bufferSize = %d" % bufferSize ) 

        pyBuffer = bytearray( ( c_uint8 * bufferSize ).from_address( buffer ) )
        self.log.debug( "SendToClient -->\n" + TLSParser.FormatBuffer( pyBuffer ) ) 

        nextFilePath = self.serverToClientFilePathTemplate % self.currentFileID
        self.currentFileID += 1
        with open( nextFilePath, "wb" ) as msgFile:
            msgFile.write( pyBuffer )

        return bufferSize

    #Used by server to read from client:
    def ReadFromClient( self, ctx, buffer, bufferSize ):
        self.log.debug( "ReadFromClient, bufferSize = %d" % bufferSize )

        nextFilePath = self.clientToServerFilePathTemplate % self.currentFileID
        if not self.IsDataAvailable( self.client, nextFilePath ):
            return 0

        if self.BytesLeftToRead( self.client ) == 0:        
            self.ReadBytesFromFile( self.client, nextFilePath )
            self.currentFileID += 1 

        maxBytesToRead = min( bufferSize, self.BytesLeftToRead( self.client ) )
        self.cutils.DoMemcpy( c_voidp( buffer ), c_voidp( self.client.bufferAddr.value + self.client.offset ), c_uint32( maxBytesToRead ) )
        self.client.offset += maxBytesToRead    
        
        self.log.debug( "ReadFromClient: returned %d bytes" % maxBytesToRead )
        return maxBytesToRead

class MemorySocket():
    SLEEP_INTERVAL_SECONDS = 0.05

    def __init__( self, readTimeout = 1, logMsgs = LOG_TRANSMITTED_BYTES ):
        self.clientToServerPipe = bytearray()
        self.serverToClientPipe = bytearray()
        self.readTimeout        = readTimeout
        self.logMsgs            = logMsgs
        self.tlsParser          = TLSParser()

        self.SetupLogger()

    def SetupLogger( self ):
        self.log = logging.getLogger( 'MemorySocket' )
        self.log.setLevel( config.LOG_LEVEL )

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel( config.LOG_LEVEL )
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def FlushBuffers( self ):
        self.clientToServerPipe = bytearray()
        self.serverToClientPipe = bytearray()

    #Used by client to send to server:
    def SendToServer( self, ctx, buffer, bufferSize ):
        self.log.debug( "SendToServer bufferSize = %d" % bufferSize ) 
        
        pyBuffer = bytearray( ( c_uint8 * bufferSize ).from_address( buffer ) )        
        msgs     = self.tlsParser.Digest( pyBuffer[ : ], Direction.CLIENT_TO_SERVER )

        for msg in msgs:
            manipulatedWireFrame = self.tlsParser.ManipulateAndReconstruct( msg )
            if manipulatedWireFrame != None:
                self.clientToServerPipe += manipulatedWireFrame    
            else:            
                self.clientToServerPipe += msg[ RAW_RECORD ]
        return bufferSize

    #Used by server to read from client:
    def ReadFromClient( self, ctx, buffer, bufferSize ):
        self.log.debug( "ReadFromClient, bufferSize = %d" % bufferSize )

        # Wait for data to be available:
        startTime = time.time()
        while len( self.clientToServerPipe ) == 0:
            time.sleep( self.SLEEP_INTERVAL_SECONDS )
            if( time.time() - startTime > self.readTimeout ):
                self.log.error( "ReadFromClient: timeout expired" )
                return 0

        bytesToReturn = len( self.clientToServerPipe )
        if bufferSize < bytesToReturn:
            bytesToReturn = bufferSize

        pyBuffer = ( c_uint8 * bufferSize ).from_address( buffer )
        pyBuffer[ 0 : bytesToReturn ] = self.clientToServerPipe[ 0 : bytesToReturn ]

        # "flush" bytes read:
        self.clientToServerPipe = self.clientToServerPipe[ bytesToReturn : ]

        self.log.debug( "ReadFromClient: returned %d bytes; (%d bytes left for future reads)" % (bytesToReturn, len( self.clientToServerPipe ) ) )
        return bytesToReturn

    #Used by server to send to client:
    def SendToClient( self, ctx, buffer, bufferSize ):
        self.log.debug( "SendToClient bufferSize = %d" % bufferSize ) 
        pyBuffer = bytearray( ( c_uint8 * bufferSize ).from_address( buffer ) )
        msgs     = self.tlsParser.Digest( pyBuffer[ : ], Direction.SERVER_TO_CLIENT )
       
        if self.logMsgs:
            self.log.debug( "SendToClient -->\n" + TLSParser.FormatBuffer( pyBuffer ) ) 

        for msg in msgs:
            manipulatedWireFrame = self.tlsParser.ManipulateAndReconstruct( msg )

            if manipulatedWireFrame != None:
                self.serverToClientPipe += manipulatedWireFrame    
                if len( manipulatedWireFrame ) != len(  msg[ RAW_RECORD ] ):
                    self.log.warning( "len( manipulatedWireFrame ) != len(  msg[ RAW_RECORD ] ): %d != %d" % (len( manipulatedWireFrame ) , len(  msg[ RAW_RECORD ] )) )
            else:    
                self.serverToClientPipe += msg[ RAW_RECORD ]
        
        return bufferSize

    #Used by client to read from server:
    def ReadFromServer( self, ctx, buffer, bufferSize  ):
        self.log.debug( "ReadFromServer, bufferSize = %d" % bufferSize )

        # Wait for data to be available:
        startTime = time.time()
        while len( self.serverToClientPipe ) == 0:
            time.sleep( self.SLEEP_INTERVAL_SECONDS )
            if( time.time() - startTime > self.readTimeout ):
                self.log.error( "ReadFromServer: timeout expired" )
                return 0

        bytesToReturn = len( self.serverToClientPipe )
        if bufferSize < bytesToReturn:
            bytesToReturn = bufferSize

        pyBuffer = ( c_uint8 * bufferSize ).from_address( buffer )
        pyBuffer[ 0 : bytesToReturn ] = self.serverToClientPipe[ 0 : bytesToReturn ]

        # "flush" bytes:
        self.serverToClientPipe = self.serverToClientPipe[ bytesToReturn : ]

        self.log.debug( "ReadFromServer: returned %d bytes; ; (%d bytes left for future reads)" % (bytesToReturn, len( self.serverToClientPipe )) )
        return bytesToReturn
