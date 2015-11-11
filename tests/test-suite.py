#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, time, socket, random, xsubprocess as sp, logging
import ConfigParser as cp, StringIO as sio, shutil, tempfile

# --------------------------------------------------------------------
class Object(object):
    def __init__(self, **kw):
        self.__dict__.update(kw)

# --------------------------------------------------------------------
OPENSSL_CIPHERS = {
    'TLS_RSA_WITH_NULL_MD5'               : 'NULL-MD5'               ,
    'TLS_RSA_WITH_NULL_SHA'               : 'NULL-SHA'               ,
    'TLS_RSA_WITH_NULL_SHA256'            : 'NULL-SHA256'            ,
    'TLS_RSA_WITH_RC4_128_MD5'            : 'RC4-MD5'                ,
    'TLS_RSA_WITH_RC4_128_SHA'            : 'RC4-SHA'                ,
    'TLS_RSA_WITH_3DES_EDE_CBC_SHA'       : 'DES-CBC3-SHA'           ,
    'TLS_RSA_WITH_AES_128_CBC_SHA'        : 'AES128-SHA'             ,
    'TLS_RSA_WITH_AES_128_CBC_SHA256'     : 'AES128-SHA256'          ,
    'TLS_RSA_WITH_AES_256_CBC_SHA'        : 'AES256-SHA'             ,
    'TLS_RSA_WITH_AES_256_CBC_SHA256'     : 'AES256-SHA256'          ,
    'TLS_RSA_WITH_AES_128_GCM_SHA256'     : 'AES128-GCM-SHA256'      ,
    'TLS_RSA_WITH_AES_256_GCM_SHA384'     : 'AES256-GCM-SHA384'      ,
    'TLS_DH_anon_WITH_3DES_EDE_CBC_SHA'   : 'ADH-DES-CBC3-SHA'       ,
    'TLS_DH_anon_WITH_AES_128_CBC_SHA'    : 'ADH-AES128-SHA'         ,
    'TLS_DH_anon_WITH_AES_128_CBC_SHA256' : 'ADH-AES128-SHA256'      ,
    'TLS_DH_anon_WITH_AES_256_CBC_SHA'    : 'ADH-AES256-SHA'         ,
    'TLS_DH_anon_WITH_AES_256_CBC_SHA256' : 'ADH-AES256-SHA256'      ,
    'TLS_DH_anon_WITH_RC4_128_MD5'        : 'ADH-RC4-MD5'            ,
    'TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA'   : 'EDH-DSS-DES-CBC3-SHA'   ,
    'TLS_DHE_DSS_WITH_AES_128_CBC_SHA'    : 'DHE-DSS-AES128-SHA'     ,
    'TLS_DHE_DSS_WITH_AES_128_CBC_SHA256' : 'DHE-DSS-AES128-SHA256'  ,
    'TLS_DHE_DSS_WITH_AES_256_CBC_SHA'    : 'DHE-DSS-AES256-SHA'     ,
    'TLS_DHE_DSS_WITH_AES_256_CBC_SHA256' : 'DHE-DSS-AES256-SHA256'  ,
    'TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA'   : 'EDH-RSA-DES-CBC3-SHA'   ,
    'TLS_DHE_RSA_WITH_AES_128_CBC_SHA'    : 'DHE-RSA-AES128-SHA'     ,
    'TLS_DHE_RSA_WITH_AES_128_CBC_SHA256' : 'DHE-RSA-AES128-SHA256'  ,
    'TLS_DHE_RSA_WITH_AES_256_CBC_SHA'    : 'DHE-RSA-AES256-SHA'     ,
    'TLS_DHE_RSA_WITH_AES_256_CBC_SHA256' : 'DHE-RSA-AES256-SHA256'  ,
}

# --------------------------------------------------------------------
class MI_MI_TLS(object):
    name     = 'MI_MI_TLS'
    miserver = True
    miclient = True

class MI_C_TLS(object):
    name     = 'MI_C_TLS'
    miserver = False
    miclient = True

VENDORS_MODE = (MI_MI_TLS, MI_C_TLS)
VENDORS_MODE = dict((x.name, x) for x in VENDORS_MODE)

# --------------------------------------------------------------------
def cygpath(mode, path):
    command = ['cygpath', '-%s' % (mode,), path]
    subp    = sp.Popen(command, stdout = sp.PIPE)
    return subp.communicate()[0].splitlines()[0]

# --------------------------------------------------------------------
def _openssl_ciphers():
    ciphers = sp.Popen(['openssl', 'ciphers', 'ALL:NULL'], stdout = sp.PIPE)
    ciphers = ciphers.communicate()[0]
    ciphers = ciphers.splitlines()[0].split(':')

    return ciphers

# --------------------------------------------------------------------
def _check_for_config(mode, config):
    assert mode.miclient        # Non miTLS client unsupported

    subpc, subps = None, None
    sessiondir   = None

    if sys.platform.lower() not in ('cygwin', 'win32'):
        if 'nomono' in config.options:
            logging.warning('Test disabled under Mono')
            return True

    try:
        logging.debug('Creating empty session directory...')
        sessiondir = tempfile.mkdtemp()
        os.mkdir(os.path.join(sessiondir, 'client'))
        os.mkdir(os.path.join(sessiondir, 'server'))
        logging.debug('...created [%s/{client,server}]' % (sessiondir,))

        def build_command(mivendor, isclient):
            assert not (not mivendor and isclient)

            mysessiondir = os.path.join(sessiondir, 'client' if isclient else 'server')
            dhdir        = os.path.join('..','data','dh')
            win32        = sys.platform.lower() in ('cygwin', 'win32')
            cipher       = config.cipher

            if win32 and sys.platform.lower() == 'cygwin':
                mysessiondir = cygpath('w', mysessiondir)

            if not mivendor:
                cipher = OPENSSL_CIPHERS[cipher]

            if mivendor:
                pgm = '../apps/echo/bin/Debug/echo.exe'
            else:
                pgm = 'i686-pc-mingw32-echo.exe' if win32 else 'echo'
                pgm = os.path.join('c-stub', pgm)

            command  = [pgm]
            command += ['--address'      , str(config.address[0]),
                        '--port'         , str(config.address[1]),
                        '--ciphers'      , cipher,
                        '--tlsversion'   , config.version,
                        '--sessionDB-dir', mysessiondir,
                        '--dhDB-dir'     , dhdir]

            if config.servname is not None:
                command += ['--server-name'  , config.servname,]


            if not mivendor and config.pki is not None:
                command += ['--pki', config.pki]

            if mivendor and not win32:
                command = ['mono', '--debug'] + command

            if isclient:
                command += ['--client']

            return command

        c_command = build_command(mode.miclient, True )
        s_command = build_command(mode.miserver, False)

        logging.debug('Starting echo server [%s]' % (' '.join(s_command)))

        try:
            subps = sp.Popen(s_command)
        except OSError, e:
            logging.error('Cannot start echo server: %s' % (e,))
            return False

    	logging.debug('Waiting echo server to set up...')
        time.sleep(1.5)

        logging.debug('Starting echo client [%s]' % (' '.join(c_command)))

        try:
            subpc = sp.Popen(c_command, stdin = sp.PIPE, stdout = sp.PIPE)
        except OSError, e:
            logging.error('Cannot start echo client: %s' % (e,))
            return False

        logging.debug('Waiting echo client to set up...')
        time.sleep(1.5)

        logging.debug('Client <-> server communication...')

        CRLN  = '\r\n'
        DATA  = 'dohj3do0aiF9eishilaiPh2aid2eidahch2eivaonevohmoovainazoo8Ooyoo9O'
        REGN  = '<renegotiate>'

        if config.reneg:
            INPUT = CRLN.join([DATA, REGN, DATA]) + CRLN
        else:
            INPUT = DATA + CRLN

        try:
            contents = subpc.communicate(INPUT, timeout = 3)[0].splitlines()
        except (IOError, OSError), e:
            logging.error('Error while interacting with server: %s' % (e,))
            return False

        return DATA in contents

    finally:
        for subp, who in [(subpc, 'client'), (subps, 'server')]:
            if subp is not None:
                logging.debug('Waiting echo %s to shutdown...' % (who,))
                try:
                    subp.terminate(); subp.kill(); subp.wait()
                except OSError:
                    pass
                
        if sessiondir is not None:
            shutil.rmtree(sessiondir, ignore_errors = True)

    logging.info('Test successful')
    return True

# --------------------------------------------------------------------
DEFAULTS = '''\
[DEFAULT]
bind     = 127.0.0.1:?
servname =
modes    = MI_MI_TLS MI_C_TLS
reneg    = False
pki      =
options  =
'''

def _main():
    logging.basicConfig(stream = sys.stderr,
                        level  = logging.DEBUG,
                        format = '%(asctime)-15s - %(levelname)s - %(message)s')

    parser = cp.ConfigParser()
    parser.readfp(sio.StringIO(DEFAULTS))
    if not parser.read('test-suite.ini'):
        print >>sys.stderr, 'Cannot read configuration file'
        exit(1)


    if not parser.has_option('config', 'scenarios'):
        print >>sys.stderr, "Missing `[config].scenarios' option"
        exit(1)

    bind      = parser.get('config', 'bind')
    scennames = parser.get('config', 'scenarios').split()
    scenarios = []

    if len(sys.argv)-1 > 0:
        scennames = sys.argv[1:]

    for scenario in scennames:
        if not parser.has_section(scenario):
            print >>sys.stderr, "No section for scenario `%s'" % (scenario,)
            exit(1)

    for scenario in scennames:
        for x in ('versions', 'ciphers'):
            if not parser.has_option(scenario, x):
                print >>sys.stderr, "Missing `[%s].%s' option" % (scenario, x)
                exit(1)
        scendata = Object(
            servname = parser.get(scenario, 'servname').strip() or None,
            versions = parser.get(scenario, 'versions').split(),
            ciphers  = parser.get(scenario, 'ciphers' ).split(),
            modes    = parser.get(scenario, 'modes'   ).split(),
            reneg    = parser.getboolean(scenario, 'reneg'),
            pki      = parser.get(scenario, 'pki').strip() or None,
            options  = set(parser.get(scenario, 'options').split()) or [],
        )

        if 'PKIBASE' in os.environ:
            scendata.pki = os.path.join(os.environ['PKIBASE'], scendata.pki or '')

        try:
            scendata.modes = [VENDORS_MODE[x] for x in scendata.modes]
        except KeyError, e:
            print >>sys.stderr, "Unknown mode: `%s'" % (e.args[0])
            exit(1)

        scenarios.append((scenario, scendata))

    del scendata

    if ':' in bind:
        bind = tuple(bind.split(':', 1))
        if bind[1] == '?':
            bind = (bind[0], random.randint(32768, 65535))
    else:
        bind = (bind, 6000)

    try:
        bind = \
            socket.getaddrinfo(bind[0], bind[1]  ,
                               socket.AF_INET    ,
                               socket.SOCK_STREAM,
                               socket.SOL_TCP    )[0][4]
    except socket.error, e:
        logging.fatal("cannot resolve `%s': %s" % (':'.join(bind), e))
        exit(1)

    logging.info("----- OPENSSL CIPHERS -----")
    logging.info(':'.join(_openssl_ciphers()))
    logging.info("----- END OF OPENSSL CIPHERS -----")

    logging.info("----- CONFIGURATION -----")
    logging.info("Binding address is: %s" % ':'.join(map(str, bind)))
    for i, (name, scendata) in enumerate(scenarios):
        logging.info("Scenario %.2d (%s)" % (i+1, name))
        logging.info("* TLS Servname: %s" % (scendata.servname or '<none>',))
        logging.info("* TLS versions: %s" % ", ".join(scendata.versions))
        logging.info("* TLS ciphers : %s" % ", ".join(scendata.ciphers))
        logging.info("* TLS vendors : %s" % ", ".join([x.name for x in scendata.modes]))
        logging.info("* TLS reneg   : %r" % (scendata.reneg,))
    logging.info("----- END OF CONFIGURATION -----")

    nerrors = 0

    for name, scendata in scenarios:
        for cipher in scendata.ciphers:
            for version in scendata.versions:
                for mode in scendata.modes:
                    logging.info("Checking for cipher: `%s'" % (cipher,))
                    logging.info("* Client is miTLS: %r" % (mode.miclient,))
                    logging.info("* Server is miTLS: %r" % (mode.miserver,))
                    logging.info("* TLS version is : %s" % (version,))
                    logging.info("* TLS reneg      : %r" % (scendata.reneg,))
                    logging.info("* servname is    : %s" % (scendata.servname or '<none>',))
                    logging.info("* PKI located at : %s" % (scendata.pki or '<none>',))
        
                    config = Object(cipher   = cipher,
                                    version  = version,
                                    address  = bind,
                                    servname = scendata.servname,
                                    reneg    = scendata.reneg,
                                    pki      = scendata.pki,
                                    options  = scendata.options)
    
                    success  = _check_for_config(mode, config)
                    nerrors += int(not success)
    
                    if not success:
                        logging.error('---------- FAILURE ----------')

    logging.info('# errors: %d' % (nerrors,))
    exit(2 if nerrors else 0)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
