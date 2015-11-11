#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, subprocess as sp

# --------------------------------------------------------------------
# BIN = './openssl-client.exe'
# BIN = 'java -classpath "3rdparty/bcprov-ext-jdk15on-148.jar;jsse-client" JSSEClient'
BIN = '../../BenchClient/bin/Release/BenchClient.exe'
# BIN = 'bc/BCClient/bin/Release/BCClient.exe'

CONFIGS = [
    ('rsa', 'rsa.cert-01.mitls.org', 'TLS_RSA_WITH_RC4_128_MD5'           ),
    ('rsa', 'rsa.cert-01.mitls.org', 'TLS_RSA_WITH_RC4_128_SHA'           ),
    ('rsa', 'rsa.cert-01.mitls.org', 'TLS_RSA_WITH_3DES_EDE_CBC_SHA'      ),
    ('rsa', 'rsa.cert-01.mitls.org', 'TLS_RSA_WITH_AES_128_CBC_SHA'       ),
    ('rsa', 'rsa.cert-01.mitls.org', 'TLS_RSA_WITH_AES_128_CBC_SHA256'    ),
    ('rsa', 'rsa.cert-01.mitls.org', 'TLS_RSA_WITH_AES_256_CBC_SHA'       ),
    ('rsa', 'rsa.cert-01.mitls.org', 'TLS_RSA_WITH_AES_256_CBC_SHA256'    ),
    ('dsa', 'dsa.cert-01.mitls.org', 'TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA'  ),
    ('dsa', 'dsa.cert-01.mitls.org', 'TLS_DHE_DSS_WITH_AES_128_CBC_SHA'   ),
    ('dsa', 'dsa.cert-01.mitls.org', 'TLS_DHE_DSS_WITH_AES_128_CBC_SHA256'),
    ('dsa', 'dsa.cert-01.mitls.org', 'TLS_DHE_DSS_WITH_AES_256_CBC_SHA'   ),
    ('dsa', 'dsa.cert-01.mitls.org', 'TLS_DHE_DSS_WITH_AES_256_CBC_SHA256'),
]

# --------------------------------------------------------------------
def _main():
    configs = CONFIGS[:]

    mode = os.environ.get('MODE', None)
    if mode is not None:
        cfilt = [x for x in mode.split(':') if x]
        for filt in cfilt:
            if filt.startswith('!'):
                configs = [x for x in configs if filt[1:] not in x[2]]
            else:
                configs = [x for x in configs if filt in x[2]]

    for config in configs:
        environ = os.environ.copy()
        environ['PKI']         = '../pki/%s' % (config[0],)
        environ['CERTNAME']    = config[1]
        environ['CIPHERSUITE'] = config[2]

        sp.check_call(BIN, env = environ, shell = True)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
