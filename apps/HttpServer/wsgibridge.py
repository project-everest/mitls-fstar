# ------------------------------------------------------------------------
import sys, os, socket, urlparse
import System as DotNet

# ------------------------------------------------------------------------
__all__ = []

# ------------------------------------------------------------------------
def iterfun(f, pred):
    while True:
        x = f()
        if pred(x): yield x
        else: break

# ------------------------------------------------------------------------
class WSGIErrorStream(object):
    def __init__(self, basestream):
        assert isinstance(basestream, DotNet.IO.TextWriter)
        self._basestream = basestream

    def write(self, s):
        self._basestream.Write(s)

    def writelines(self, seq):
        # Not that [writelines] must NOT add CRLF
        for x in seq:
            self._basestream.Write(x)

    def flush(self):
        self._basestream.Flush()

# ------------------------------------------------------------------------
class WSGIInputStream(object):
    def __init__(self, basestream):
        assert isinstance(basestream, DotNet.IO.Stream)
        assert basestream.CanRead
        enc = DotNet.Text.Encoding.GetEncoding("iso-8859-1")
        self._basestream = basestream
        self._txtstream  = DotNet.IO.StreamReader(basestream, enc)

    basestream = property(lambda self : self._basestream)

    def read(self, size = -1):
        if size < 0:
            return self._txtstream.ReadToEnd()

    def readline(self, size = -1):
        # In WSGI 1.0, [size] can be omitted
        aout = self._txtstream.ReadLine()
        if aout is None:
            return ''
        return aout + DotNet.Environment.NewLine

    def readlines(self, size = -1):
        # In WSGI 1.0, [size] can be omitted
        return list(self)

    def __iter__(self):
        return iterfun(self.readline, lambda x : len(x) != 0)

# ------------------------------------------------------------------------
class WSGIOutputStream(object):
    def __init__(self, basestream):
        assert isinstance(basestream, DotNet.IO.Stream)
        assert basestream.CanWrite
        enc = DotNet.Text.Encoding.GetEncoding("iso-8859-1")
        self._basestream = basestream
        self._txtstream  = DotNet.IO.StreamWriter(basestream, enc)

    basestream = property(lambda self : self._basestream)

    def write(self, data):
        self._txtstream.Write(data)

    def flush(self):
        self._txtstream.Flush()

    def close(self):
        try:
            self._txtstream .Close()
            self._basestream.Close()
        finally:
            self._txtstream  = None
            self._basestream = None

# ------------------------------------------------------------------------
class Bridge(object):
    def __init__(self, config):
        self._url     = urlparse.urlparse(config['url'])
        self._input   = WSGIInputStream(config['input'])
        self._output  = WSGIOutputStream(config['output'])
        self._error   = WSGIErrorStream(config['error'])
        self._request = config['request']
        self._sinfo   = config['sinfo']
        self._headers = None
        self._hdsent  = False

    url     = property(lambda self : self._url)
    input   = property(lambda self : self._input)
    output  = property(lambda self : self._output)
    error   = property(lambda self : self._error)
    request = property(lambda self : self._request)

    def send_headers(self):
        if self._headers is None:
            raise AssertionError("send_headers() without headers set")
        if self._hdsent:
            raise AssertionError("send_headers() with headers already sent")

        status, headers = self._headers
        try:
            self._output.write('%s %s\r\n' % ("HTTP/1.0", status,))
            for hk, hv in headers:
                self._output.write('%s: %s\r\n' % (hk, hv))
            self._output.write('\r\n')
            self._output.flush()
        finally:
            self._hdsent = True

    def write(self, data):
        if self._headers is None:
            raise AssertionError("write() before start_response()")
        if not self._hdsent:
            self.send_headers()
        self._output.write(data)
        self._output.flush()

    def start_response(self, status, headers, exc_info=None):
        if exc_info is None:
            if self._headers is not None:
                raise AssertionError("start_response(exc_info=None) called a 2nd time")
        elif self._hdsent:
            raise exc_info[1].with_traceback(exc_info[2])

        self._headers = (status, headers[:])
        # TODO: check headers here
        return self.write

    def __call__(self, application):
        path = [x for x in self.url.path.split('/') if x]
        if path[:1] != ['wsgi']:
            raise AssertionError("path does not start with `/wsgi'")

        environ = dict(os.environ.items())
        environ['wsgi.input'  ]       = self._input
        environ['wsgi.errors' ]       = self._error
        environ['wsgi.version']       = (1, 0)
        environ['wsgi.multithreaded'] = True
        environ['wsgi.multiprocess' ] = False
        environ['wsgi.run_once'     ] = True
        environ['wsgi.url_scheme'   ] = self.url.scheme
        environ['mitls.sinfo']        = self._sinfo
        environ['HTTPS']              = '1' if self.url.scheme == 'https' else '0'

        environ['REQUEST_METHOD']  = self._request.mthod
        environ['SCRIPT_NAME']     = '/%s' % path[0]
        environ['PATH_INFO']       = '/%s' % '/'.join(path[1:])
        environ['CONTENT_TYPE']    = self._request.headers.GetDfl("Content-Type", "")
        environ['CONTENT_LENGTH']  = self._request.headers.GetDfl("Content-Length", "")
        environ['QUERY_STRING']    = self.url.query
        environ['SERVER_NAME']     = self.url.hostname
        environ['SERVER_PORT']     = self.url.port or socket.getservbyname(self.url.scheme, 'tcp')
        environ['SERVER_PROTOCOL'] = 'HTTP/1.0'

        result = application(environ, self.start_response)
        try:
            for data in result:
                if data:
                    self.write(data)
            if not self._hdsent:
                self.write('')
        finally:
            if hasattr(result, 'close'):
                result.close()

    def __repr__(self):
        fields = ['url', 'input', 'output', 'error']
        fields = ["%s = %r" % (k, getattr(self, k)) for k in fields]
        return "Bridge[%s]" % ", ".join(fields)

# ------------------------------------------------------------------------
def _entry(config, application):
    Bridge(config)(application)
