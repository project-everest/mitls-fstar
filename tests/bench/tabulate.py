#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re

# --------------------------------------------------------------------
CIPHERS = [
    ('TLS_RSA_WITH_RC4_128_MD5'           , ('RSA', 'RC4'   , 'MD5')),
    ('TLS_RSA_WITH_RC4_128_SHA'           , ('RSA', 'RC4'   , 'SHA')),
    ('TLS_RSA_WITH_3DES_EDE_CBC_SHA'      , ('RSA', '3DES'  , 'SHA')),
    ('TLS_RSA_WITH_AES_128_CBC_SHA'       , ('RSA', 'AES128', 'SHA')),
    ('TLS_RSA_WITH_AES_128_CBC_SHA256'    , ('RSA', 'AES128', 'SHA256')),
    ('TLS_RSA_WITH_AES_256_CBC_SHA'       , ('RSA', 'AES256', 'SHA')),
    ('TLS_RSA_WITH_AES_256_CBC_SHA256'    , ('RSA', 'AES256', 'SHA256')),
    ('TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA'  , ('DHE', '3DES'  , 'SHA')),
    ('TLS_DHE_DSS_WITH_AES_128_CBC_SHA'   , ('DHE', 'AES128', 'SHA')),
    ('TLS_DHE_DSS_WITH_AES_128_CBC_SHA256', ('DHE', 'AES128', 'SHA256')),
    ('TLS_DHE_DSS_WITH_AES_256_CBC_SHA'   , ('DHE', 'AES256', 'SHA')),
    ('TLS_DHE_DSS_WITH_AES_256_CBC_SHA256', ('DHE', 'AES256', 'SHA256')),
]

NAMES = ('mitls-bc', 'mitls-ossl', 'openssl', 'oracle-jsse-1.7')

# --------------------------------------------------------------------
def _main():
    if len(sys.argv)-1 not in (1, 2):
        print >>sys.stderr, 'Usage: %s <server> <client-filter>' % (sys.argv[0],)
        exit(1)

    server  = sys.argv[1]
    clients = NAMES[:]

    if len(sys.argv)-1 == 2:
        clfilter = sys.argv[2]
        if clfilter.startswith('!'):
            clfilter = set(clfilter[1:].split(','))
            clients = [x for x in clients if x not in clfilter]
        else:
            clfilter = set(clfilter.split(','))
            clients = [x for x in clients if x in clfilter]
        del clfilter

    contents = [os.path.join('results', server, x + '.txt') for x in clients]
    contents = [(x, open(x, 'rb').read().splitlines()) for x in contents]

    result = dict()

    for name, content in contents:
        name = os.path.splitext(os.path.basename(name))[0]
        for line in content:
            line = re.sub('#.*$', '', line)
            m1   = re.search('^(.*?): ((:?\d|\.)+) HS/s$' , line)
            m2   = re.search('^(.*?): ((:?\d|\.)+) MiB/s$', line)

            if m1 is not None:
                result.setdefault(name, {}).setdefault(m1.group(1), {})['HS'] = \
                    float(m1.group(2))

            if m2 is not None:
                result.setdefault(name, {}).setdefault(m2.group(1), {})['rate'] = \
                    float(m2.group(2))

    print '%% Server  : %s' % (server,)
    print '%% Clients : %s' % (', '.join(clients),)
    for cipher, name in CIPHERS:
        columns = [(' & '.join(name)).replace('_', '\\_')]
        for client in clients:
            hs = result.get(client, {}).get(cipher, {}).get('HS'  , None) 
            bw = result.get(client, {}).get(cipher, {}).get('rate', None)
            columns.append(' - ' if hs is None else '%.2f' % (hs,))
            columns.append(' - ' if bw is None else '%.2f' % (bw,))
        print ' & '.join(columns) + '\\\\'

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
