import unittest
import threading
import time
import traceback
import logging
import argparse
import sys
import logging 

from mitls_tester import MITLS, MonitorLeakedKeys, memorySocket
from nss_tester   import NSS

import mitls_tester
import tlsparser
import config

runMITLS_NSS_test                   = False
runMITLS_NSS_CipherSuites           = False
runMITLS_NSS_SignatureAlgorithms    = False
runMITLS_NSS_NamedGroups            = False
runNSS_MITLS_CipherSuites           = False
runNSS_MITLS_SignatureAlgorithms    = False
runNSS_MITLS_NamedGroups            = False
runMITLS_NSS_parameters_matrix      = False
runNSS_MITLS_parameters_matrix      = False

DATA_CLIENT_TO_SERVER = b"Client->Server\x00"
DATA_SERVER_TO_CLIENT = b"Server->Client\x00"

class InterOperabilityTester(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super(InterOperabilityTester, self).__init__(*args, **kwargs)
        self.SetupLogger()

    def setUp(self):
        self.tlsServer = None
        self.tlsClient = None

    def tearDown(self):
        if self.tlsServer is not None:
            self.tlsServer.Cleanup()
        if self.tlsClient is not None:
            self.tlsClient.Cleanup()

    def SetupLogger( self ):
        self.log = logging.getLogger( 'InterOpTester' )
        self.log.setLevel(logging.DEBUG)

        formatter      = logging.Formatter('%(asctime)s %(name)-20s %(levelname)-10s %(message)s')
        consoleHandler = logging.StreamHandler()
        consoleHandler.setLevel(logging.DEBUG)
        consoleHandler.setFormatter(formatter)

        self.log.handlers = []
        self.log.addHandler(consoleHandler) 

    def test_MITLSClient_NSS_server( self ):
        if not runMITLS_NSS_test:
            return

        hostName = "test_server.com"

        self.tlsServer = NSS( "server" )
        self.tlsServer.InitServer( memorySocket )

        self.tlsClient = MITLS( "client" )
        self.tlsClient.InitClient( hostName )

        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        serverThread = threading.Thread(target = self.tlsServer.AcceptConnection )
        serverThread.start()

        time.sleep( 0.1 )

        self.tlsClient.Connect()

        keysMonitor.StopMonitorStdoutForLeakedKeys()
        serverThread.join()

        if config.LOG_LEVEL < logging.ERROR:
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )

    def RunSingleTest_MITLS_NSS(self, 
                                supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                                supportedSignatureAlgorithms    = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS,
                                supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS ):
        self.tlsServer = NSS( "server" )
        self.tlsServer.InitServer( memorySocket )

        applicationData = DATA_SERVER_TO_CLIENT
        serverThread    = threading.Thread(target = self.tlsServer.AcceptConnection, args = [ applicationData ] )
        serverThread.start()

        time.sleep( 0.1 )

        self.tlsClient = MITLS( "client" )
        self.tlsClient.InitClient(  "test_server.com", 
                                    supportedCipherSuites,
                                    supportedSignatureAlgorithms,
                                    supportedNamedGroups )
        self.tlsClient.Connect()
        self.tlsClient.Send( DATA_CLIENT_TO_SERVER )            
        self.tlsClient.dataReceived = self.tlsClient.Receive()
    
        serverThread.join()

        if self.tlsServer.acceptConnectionSucceeded == False:
            raise Exception( "Server failed to connect" )

        if self.tlsClient.dataReceived != DATA_SERVER_TO_CLIENT:
            raise Exception( "self.tlsClient.dataReceived = %s, instead of expected %s" % ( self.tlsClient.dataReceived, DATA_SERVER_TO_CLIENT ) )           

        if self.tlsServer.dataReceived != DATA_CLIENT_TO_SERVER:
            raise Exception( "self.tlsServer.dataReceived = %s, instead of expected %s" % ( self.tlsServer.dataReceived, DATA_CLIENT_TO_SERVER ) )
            

    def RunSingleTest_NSS_MITLS(self, 
                                supportedCipherSuites           = mitls_tester.SUPPORTED_CIPHER_SUITES,
                                supportedSignatureAlgorithms    = mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS,
                                supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS ):
        hostName     = "test_server.com"
        mitlsTester  = mitls_tester.MITLSTester()
        serverThread = mitlsTester.StartServerThread(   supportedCipherSuites,
                                                        supportedSignatureAlgorithms,
                                                        supportedNamedGroups,
                                                        applicationData = DATA_SERVER_TO_CLIENT )

        time.sleep( 0.2 )

        self.tlsClient = NSS( "client" )
        self.tlsClient.InitClient( memorySocket, hostName )

        self.tlsClient.Connect()

        self.tlsClient.Send( DATA_CLIENT_TO_SERVER )            
        self.tlsClient.dataReceived = self.tlsClient.Recv()
    
        serverThread.join()

        if config.LOG_LEVEL < logging.ERROR:
            for msg in memorySocket.tlsParser.transcript:
                memorySocket.tlsParser.PrintMsg( msg )

        if mitlsTester.tlsServer.acceptConnectionSucceeded == False:
            raise Exception( "Server failed to connect" )

        if self.tlsClient.dataReceived != DATA_SERVER_TO_CLIENT:
            raise Exception( "self.tlsClient.dataReceived = %s, instead of expected %s" % ( self.tlsClient.dataReceived, DATA_SERVER_TO_CLIENT ) )           

        if mitlsTester.tlsServer.dataReceived != DATA_CLIENT_TO_SERVER:
            raise Exception( "mitlsTester.tlsServer.dataReceived = %s, instead of expected %s" % ( mitlsTester.tlsServer.dataReceived, DATA_CLIENT_TO_SERVER ) )
            

    def test_MITLS_NSS_CipherSuites( self ):
        if not runMITLS_NSS_CipherSuites:
            return
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        knownGoodSignatureAlgorithm = [ 'ECDSA+SHA256' ]
        knownGoodNamedGroup         = [ "X25519" ]

        with open( "cipher_suites_MITLS_NSS.txt", "w" ) as logFile:
            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                logFile.write( "cipherSuite = %-40s" % cipherSuite )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest_MITLS_NSS(   supportedCipherSuites        = [ cipherSuite ],
                                                    supportedSignatureAlgorithms = knownGoodSignatureAlgorithm,
                                                    supportedNamedGroups         = knownGoodNamedGroup)
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_exc()
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_NSS_MITLS_CipherSuites( self ):
        if not runNSS_MITLS_CipherSuites:
            return
        
        knownGoodSignatureAlgorithm = [ 'ECDSA+SHA256' ]
        knownGoodNamedGroup         = [ "X25519" ]

        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "cipher_suites_NSS_MITLS.txt", "w" ) as logFile:
            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                logFile.write( "cipherSuite = %-40s" % cipherSuite )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest_NSS_MITLS(   supportedCipherSuites        = [ cipherSuite ],
                                                    supportedSignatureAlgorithms = knownGoodSignatureAlgorithm,
                                                    supportedNamedGroups         = knownGoodNamedGroup )
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_exc()
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_NSS_MITLS_SignatureAlgorithms( self ):
        if not runNSS_MITLS_SignatureAlgorithms:
            return
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "signature_algorithms_NSS_MITLS.txt", "w" ) as logFile:
            for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                logFile.write( "algorithm = %-40s" % algorithm )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest_NSS_MITLS( supportedSignatureAlgorithms = [ algorithm ])
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_MITLS_NSS_SignatureAlgorithms( self ):
        if not runMITLS_NSS_SignatureAlgorithms:
            return
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "signature_algorithms_MITLS_NSS.txt", "w" ) as logFile:
            for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                logFile.write( "algorithm = %-40s" % algorithm )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest_MITLS_NSS( supportedSignatureAlgorithms = [ algorithm ])
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_NSS_MITLS_NamedGroups( self ):
        if not runNSS_MITLS_NamedGroups:
            return
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "named_groups_NSS_MITLS.txt", "w" ) as logFile:
            for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                logFile.write( "group = %-40s" % group )
                self.log.info( "test_NSS_MITLS_NamedGroups: group = %-40s" % group )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest_NSS_MITLS( supportedNamedGroups = [ group ] )
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_MITLS_NSS_NamedGroups( self ):
        if not runMITLS_NSS_NamedGroups:
            return
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "named_groups_MITLS_NSS.txt", "w" ) as logFile:
            for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                logFile.write( "group = %-40s" % group )
                memorySocket.FlushBuffers()
                memorySocket.tlsParser = tlsparser.TLSParser()
                try:
                    self.RunSingleTest_MITLS_NSS( supportedNamedGroups = [ group ] )
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_MITLS_NSS_parameters_matrix( self ):
        if not runMITLS_NSS_parameters_matrix:
            return
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "parameters_matrix_MITLS_NSS.txt", "w" ) as logFile:
            logFile.write( "%-40s, %-40s, %-40s, %-10s\n" % ("CipherSuite", "SignatureAlgorithm", "NamedGroup", "PassFail") )
            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                    for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                        logFile.write( "%-40s, %-40s, %-40s, " % ( cipherSuite, algorithm, group ) )
                        memorySocket.FlushBuffers()
                        memorySocket.tlsParser = tlsparser.TLSParser()
                        try:
                            self.RunSingleTest_MITLS_NSS(   supportedCipherSuites        = [ cipherSuite ],
                                                            supportedSignatureAlgorithms = [ algorithm ],
                                                            supportedNamedGroups         = [ group ] )
                            logFile.write( "%-10s\n" % "OK" )
                        except Exception as err: 
                            traceback.print_tb(err.__traceback__)
                            logFile.write( "%-10s\n" % "FAILED" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_NSS_MITLS_parameters_matrix( self ):
        if not runNSS_MITLS_parameters_matrix:
            return
        
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "parameters_matrix_NSS_MITLS.txt", "w" ) as logFile:
            logFile.write( "%-40s, %-40s, %-40s, %-10s\n" % ("CipherSuite", "SignatureAlgorithm", "NamedGroup", "PassFail") )
            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                    for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                        logFile.write( "%-40s, %-40s, %-40s, " % ( cipherSuite, algorithm, group ) )
                        memorySocket.FlushBuffers()
                        memorySocket.tlsParser = tlsparser.TLSParser()
                        try:
                            self.RunSingleTest_NSS_MITLS(   supportedCipherSuites        = [ cipherSuite ],
                                                            supportedSignatureAlgorithms = [ algorithm ],
                                                            supportedNamedGroups         = [ group ] )
                            logFile.write( "%-10s\n" % "OK" )
                        except Exception as err: 
                            traceback.print_tb(err.__traceback__)
                            logFile.write( "%-10s\n" % "FAILED" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    mitls_tester.ConfigureMITLSArguments( parser )

    args   = parser.parse_args()
    mitls_tester.HandleMITLSArguments( args )

    memorySocket.log.setLevel( config.LOG_LEVEL )    
    
    # SI: reset args, else unittest.main complains of flags not being valid.
    sys.argv[1:] = args.unittest_args

    # runMITLS_NSS_test                   = True
    # runMITLS_NSS_CipherSuites           = True 
    # runMITLS_NSS_SignatureAlgorithms    = True
    # runMITLS_NSS_NamedGroups            = True
    # runNSS_MITLS_CipherSuites           = True
    # runNSS_MITLS_SignatureAlgorithms    = True
    # runNSS_MITLS_NamedGroups            = True
    runMITLS_NSS_parameters_matrix      = True
    runNSS_MITLS_parameters_matrix      = True
    unittest.main()
