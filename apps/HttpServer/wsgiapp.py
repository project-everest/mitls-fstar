# ------------------------------------------------------------------------
class BaseApplication(object):
    @staticmethod
    def create():
        def application(environ, start_response):
            start_response("200 OK", [])
            return ['Hello World!']
        return application

# ------------------------------------------------------------------------
class miTLSApplication(object):
    @staticmethod
    def create():
        import sys, os, mitls, pyramid.paster as paster

        inifile = '/opt/mitls/bridge/development.ini'
        env     = paster.bootstrap(inifile)

        return env['app']

# ------------------------------------------------------------------------
main = miTLSApplication.create
