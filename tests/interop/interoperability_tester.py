import unittest
import threading
import time
import traceback
import logging
import argparse
import sys
import logging 

from pprint       import pprint
from mitls_tester import MITLS, MonitorLeakedKeys, memorySocket
from nss_tester   import NSS

import mitls_tester
import tlsparser
import config

WriteToMultipleSinks = mitls_tester.MITLSTester.WriteToMultipleSinks

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
                                supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS,
                                msgManipulators                 = [] ):
        memorySocket.FlushBuffers()
        memorySocket.tlsParser = tlsparser.TLSParser()
        memorySocket.tlsParser.SetMsgManipulators( msgManipulators )

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
                                supportedNamedGroups            = mitls_tester.SUPPORTED_NAMED_GROUPS,
                                msgManipulators                 = [] ):
        memorySocket.FlushBuffers()
        memorySocket.tlsParser = tlsparser.TLSParser()
        memorySocket.tlsParser.SetMsgManipulators( msgManipulators )
        hostName     = "test_server.com"
        mitlsTester  = mitls_tester.MITLSTester()
        serverThread = mitlsTester.StartServerThread(   supportedCipherSuites,
                                                        supportedSignatureAlgorithms,
                                                        supportedNamedGroups,
                                                        applicationData = DATA_SERVER_TO_CLIENT )

        time.sleep( 0.2 )

        self.tlsClient = NSS( "client" )
        self.tlsClient.InitClient( memorySocket, hostName )

        self.tlsClient.Connect( supportedNamedGroups )

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
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        knownGoodSignatureAlgorithm = [ 'ECDSA+SHA256' ]
        knownGoodNamedGroup         = [ "X25519" ]

        with open( "cipher_suites_MITLS_NSS.txt", "w" ) as logFile:
            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                logFile.write( "cipherSuite = %-40s" % cipherSuite )

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
        knownGoodSignatureAlgorithm = [ 'ECDSA+SHA256' ]
        knownGoodNamedGroup         = [ "X25519" ]

        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "cipher_suites_NSS_MITLS.txt", "w" ) as logFile:
            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                logFile.write( "cipherSuite = %-40s" % cipherSuite )
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
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "signature_algorithms_NSS_MITLS.txt", "w" ) as logFile:
            for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                logFile.write( "algorithm = %-40s" % algorithm )
                try:
                    self.RunSingleTest_NSS_MITLS( supportedSignatureAlgorithms = [ algorithm ])
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_MITLS_NSS_SignatureAlgorithms( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "signature_algorithms_MITLS_NSS.txt", "w" ) as logFile:
            for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                logFile.write( "algorithm = %-40s" % algorithm )

                try:
                    self.RunSingleTest_MITLS_NSS( supportedSignatureAlgorithms = [ algorithm ])
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_NSS_MITLS_NamedGroups( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "named_groups_NSS_MITLS.txt", "w" ) as logFile:
            for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                logFile.write( "group = %-40s" % group )
                self.log.info( "test_NSS_MITLS_NamedGroups: group = %-40s" % group )
                try:
                    self.RunSingleTest_NSS_MITLS( supportedNamedGroups = [ group ] )
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_MITLS_NSS_NamedGroups( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "named_groups_MITLS_NSS.txt", "w" ) as logFile:
            for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                logFile.write( "group = %-40s" % group )

                try:
                    self.RunSingleTest_MITLS_NSS( supportedNamedGroups = [ group ] )
                    logFile.write( "OK\n" )
                except Exception as err: 
                    traceback.print_tb(err.__traceback__)
                    logFile.write( "FAILED\n" )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_MITLS_NSS_parameters_matrix( self ):
        sys.stderr.write( "Running test_MITLS_NSS_parameters_matrix\n" )
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "parameters_matrix_MITLS_NSS.txt", "w" ) as logFile:
            outputSinks = [ sys.stderr, logFile ]
            WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s %-15s%-6s\n" % ("CipherSuite,", "SignatureAlgorithm,", "NamedGroup,", "PassFail,", "Time (seconds)") )

            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                    for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                        WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s " % ( cipherSuite+",", algorithm+",", group+"," ) )

                        memorySocket.tlsParser.DeleteLeakedKeys()
                        try:
                            startTime = time.time()
                            self.RunSingleTest_MITLS_NSS(   supportedCipherSuites        = [ cipherSuite ],
                                                            supportedSignatureAlgorithms = [ algorithm ],
                                                            supportedNamedGroups         = [ group ] )
                            WriteToMultipleSinks( outputSinks, "%-15s" % ("OK,") )
                        except Exception as err: 
                            print( traceback.format_tb( err.__traceback__ ) )
                            WriteToMultipleSinks( outputSinks, "%-15s" % "FAILED," )
                        finally:
                            totalTime = time.time() - startTime
                            WriteToMultipleSinks( outputSinks, "%-6f\n" % totalTime )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_NSS_MITLS_parameters_matrix( self ):
        sys.stderr.write( "Running test_NSS_MITLS_parameters_matrix\n" )
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        with open( "parameters_matrix_NSS_MITLS.txt", "w" ) as logFile:
            outputSinks = [ sys.stderr, logFile ]
            WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s %-15s%-6s\n" % ("CipherSuite,", "SignatureAlgorithm,", "NamedGroup,", "PassFail,", "Time (seconds)") )

            for cipherSuite in mitls_tester.SUPPORTED_CIPHER_SUITES:
                for algorithm in mitls_tester.SUPPORTED_SIGNATURE_ALGORITHMS:
                    for group in mitls_tester.SUPPORTED_NAMED_GROUPS:
                        WriteToMultipleSinks( outputSinks, "%-30s %-20s %-20s " % ( cipherSuite+",", algorithm+",", group+"," ) )

                        try:
                            startTime = time.time()
                            self.RunSingleTest_NSS_MITLS(   supportedCipherSuites        = [ cipherSuite ],
                                                            supportedSignatureAlgorithms = [ algorithm ],
                                                            supportedNamedGroups         = [ group ] )
                            WriteToMultipleSinks( outputSinks, "%-15s" % ("OK,") )
                        except Exception as err: 
                            print( traceback.format_tb( err.__traceback__ ) )
                            WriteToMultipleSinks( outputSinks, "%-15s" % "FAILED," )
                        finally:
                            totalTime = time.time() - startTime
                            WriteToMultipleSinks( outputSinks, "%-6f\n" % totalTime )
              
        keysMonitor.StopMonitorStdoutForLeakedKeys()

    def test_CompareResponses_ReorderPieces_ClientHello( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        mitlsExperiments = []
        NSSExperiments   = []
        try:
            mitlsTester                     = mitls_tester.MITLSTester()
            clientHelloReorderManipulations = mitlsTester.GetClientHelloReorderManipulations( mitlsTester.RunSingleTest )
            
            mitlsExperiments                = mitlsTester.RunManipulationTest(  clientHelloReorderManipulations, 
                                                                                numExpectedSharedKeys   = 0, 
                                                                                runTestFunction         = mitlsTester.RunSingleTest )

            NSSExperiments                  = mitlsTester.RunManipulationTest(  clientHelloReorderManipulations, 
                                                                                numExpectedSharedKeys   = 0, 
                                                                                runTestFunction         = self.RunSingleTest_MITLS_NSS )
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( mitlsExperiments )
        pprint( NSSExperiments )

        self.PrintMsgManipulationComparison( mitlsExperiments, NSSExperiments, "manipulationTest_CompareResponses_ReorderPieces_ClientHello.csv" )

    def PrintMultilineList( self, items ):
        result = '"'
        for item in items:
            result += item + "\n"

        result = result.strip() + '"'

        return result

    def PrintMsgManipulationComparison( self, mitlsExperiments, NSSExperiments, reportFilePath = None ):
        resultsText = "miTLS$ NSS$ miTLS alerts$ nssAlerts$ miTLS shared keys$ NSS shared keys$miTLS transcript$ NSS transcript\n"
        for mitlsRun, nssRun in zip( mitlsExperiments, NSSExperiments ):
            resultsText += "%s$ %s$ " % (mitlsRun[ 'Manipulation' ][ 'Description' ], nssRun[ 'Manipulation' ][ 'Description' ] ) 
            resultsText += "%s$ %s$ " % ( self.PrintMultilineList( mitlsRun[ 'Alerts' ] ),                    
                                          self.PrintMultilineList( nssRun[ 'Alerts' ] )  )
            resultsText += "%s$ %s$ " % (mitlsRun[ 'SuccessfulSharedKeys' ],          nssRun[ 'SuccessfulSharedKeys' ] ) 
            resultsText += "%s$ %s$ " % ( self.PrintMultilineList( mitlsRun[ 'Transcript' ] ),                    
                                          self.PrintMultilineList( nssRun[ 'Transcript' ] )  )
            resultsText += "\n"

        resultsText = resultsText.replace( ",", ";" ).replace( "$", "," )

        if reportFilePath is None:
            print( resultsText )
            return
        # else:
        with open( reportFilePath, "w" ) as reportFile:
            reportFile.write( resultsText + "\n" )            

    def test_CompareResponses_ReorderPieces_ServerEncryptedHello( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        mitlsExperiments = []
        NSSExperiments   = []
        try:
            mitlsTester                     = mitls_tester.MITLSTester()

            reorderManipulations = mitlsTester.GetServerEncryptedHelloReorderManipulations( mitlsTester.RunSingleTest )
            mitlsExperiments     = mitlsTester.RunManipulationTest( reorderManipulations, 
                                                                    numExpectedSharedKeys   = None, 
                                                                    runTestFunction         = mitlsTester.RunSingleTest,
                                                                    assertExceptionThrown   = False )


            # NSSExperiments       = mitlsTester.RunManipulationTest( reorderManipulations, 
            #                                                         numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
            #                                                         runTestFunction         = self.RunSingleTest_MITLS_NSS,
            #                                                         assertExceptionThrown   = False ) 
            NSSExperiments       = mitlsTester.RunManipulationTest( reorderManipulations, 
                                                                    numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
                                                                    runTestFunction         = self.RunSingleTest_NSS_MITLS,
                                                                    assertExceptionThrown   = False ) 
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( mitlsExperiments )
        pprint( NSSExperiments )

        self.PrintMsgManipulationComparison( mitlsExperiments, NSSExperiments, "manipulationTest_CompareResponses_ReorderPieces_ServerEncryptedHello.csv" )

    def test_CompareResponses_ReorderServerHandshakes( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        mitlsExperiments = []
        NSSExperiments   = []
        try:
            mitlsTester                     = mitls_tester.MITLSTester()

            reorderManipulations = mitlsTester.GetServerReorderHandshakesManipulations( mitlsTester.RunSingleTest )
            mitlsExperiments     = mitlsTester.RunManipulationTest( reorderManipulations, 
                                                                    numExpectedSharedKeys   = None, 
                                                                    runTestFunction         = mitlsTester.RunSingleTest,
                                                                    assertExceptionThrown   = False )


            # NSSExperiments       = mitlsTester.RunManipulationTest( reorderManipulations, 
            #                                                         numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
            #                                                         runTestFunction         = self.RunSingleTest_MITLS_NSS,
            #                                                         assertExceptionThrown   = False ) 
            NSSExperiments       = mitlsTester.RunManipulationTest( reorderManipulations, 
                                                                    numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
                                                                    runTestFunction         = self.RunSingleTest_NSS_MITLS,
                                                                    assertExceptionThrown   = False ) 
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( mitlsExperiments )
        pprint( NSSExperiments )

        self.PrintMsgManipulationComparison( mitlsExperiments, NSSExperiments, "manipulationTest_CompareResponses_ReorderServerHandshakes.csv" )

    def test_CompareResponses_SkipServerResponsePieces( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        mitlsExperiments = []
        NSSExperiments   = []
        try:
            mitlsTester                     = mitls_tester.MITLSTester()

            skipManipulations    = mitlsTester.GetServerSkipPiecesManipulations( mitlsTester.RunSingleTest )
            mitlsExperiments     = mitlsTester.RunManipulationTest( skipManipulations, 
                                                                    numExpectedSharedKeys   = None, 
                                                                    runTestFunction         = mitlsTester.RunSingleTest,
                                                                    assertExceptionThrown   = False )
            # NSSExperiments       = mitlsTester.RunManipulationTest( skipManipulations, 
            #                                                         numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
            #                                                         runTestFunction         = self.RunSingleTest_MITLS_NSS,
            #                                                         assertExceptionThrown   = False ) 
            NSSExperiments       = mitlsTester.RunManipulationTest( skipManipulations, 
                                                                    numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
                                                                    runTestFunction         = self.RunSingleTest_NSS_MITLS,
                                                                    assertExceptionThrown   = False ) 
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( mitlsExperiments )
        pprint( NSSExperiments )

        self.PrintMsgManipulationComparison( mitlsExperiments, NSSExperiments, "manipulationTest_CompareResponses_SkipServerResponsePieces.csv" )

    def test_CompareResponses_ExtractToPlaintext( self ):
        keysMonitor = MonitorLeakedKeys()
        keysMonitor.MonitorStdoutForLeakedKeys()

        mitlsExperiments = []
        NSSExperiments   = []
        try:
            mitlsTester                     = mitls_tester.MITLSTester()

            skipManipulations    = mitlsTester.GetServerExtractPiecesToPlaintextManipulations()
            mitlsExperiments     = mitlsTester.RunManipulationTest( skipManipulations, 
                                                                    numExpectedSharedKeys   = None, 
                                                                    runTestFunction         = mitlsTester.RunSingleTest,
                                                                    assertExceptionThrown   = False )
            # NSSExperiments       = mitlsTester.RunManipulationTest( skipManipulations, 
            #                                                         numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
            #                                                         runTestFunction         = self.RunSingleTest_MITLS_NSS,
            #                                                         assertExceptionThrown   = False ) 
            NSSExperiments       = mitlsTester.RunManipulationTest( skipManipulations, 
                                                                    numExpectedSharedKeys   = None, # prevent assertion failure on numExpectedSharedKeys
                                                                    runTestFunction         = self.RunSingleTest_NSS_MITLS,
                                                                    assertExceptionThrown   = False ) 
        finally:
            keysMonitor.StopMonitorStdoutForLeakedKeys()

        pprint( mitlsExperiments )
        pprint( NSSExperiments )

        self.PrintMsgManipulationComparison( mitlsExperiments, NSSExperiments, "manipulationTest_CompareResponses_ExtractToPlaintext.csv" )


from output_redirector import stdout_redirector

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    mitls_tester.ConfigureMITLSArguments( parser )

    args   = parser.parse_args()
    mitls_tester.HandleMITLSArguments( args )

    memorySocket.log.setLevel( config.LOG_LEVEL )    



    suite = unittest.TestSuite()    
    suite.addTest( InterOperabilityTester( "test_MITLS_NSS_parameters_matrix" ) )
    suite.addTest( InterOperabilityTester( "test_NSS_MITLS_parameters_matrix" ) )
    

    # suite.addTest( InterOperabilityTester( "test_CompareResponses_ReorderPieces_ClientHello" ) )
    # suite.addTest( InterOperabilityTester( "test_CompareResponses_ReorderPieces_ServerEncryptedHello" ) )
    # suite.addTest( InterOperabilityTester( "test_CompareResponses_ReorderServerHandshakes" ) )
    # suite.addTest( InterOperabilityTester( "test_CompareResponses_SkipServerResponsePieces" ) )
    # suite.addTest( InterOperabilityTester( "test_CompareResponses_ExtractToPlaintext" ) )

    # suite.addTest( InterOperabilityTester( "test_MITLSClient_NSS_server" ) )
    # suite.addTest( InterOperabilityTester( "test_MITLS_NSS_SignatureAlgorithms" ) )
    # suite.addTest( InterOperabilityTester( "test_MITLS_NSS_NamedGroups" ) )
    # suite.addTest( InterOperabilityTester( "test_NSS_MITLS_CipherSuites" ) )
    # suite.addTest( InterOperabilityTester( "test_NSS_MITLS_SignatureAlgorithms" ) )
    # suite.addTest( InterOperabilityTester( "test_NSS_MITLS_NamedGroups" ) )
    
    
    # suite.addTest( InterOperabilityTester( "" ) )
    
    runner=unittest.TextTestRunner()

    if args.supress_output:
        devNull = open( "/dev/null", "wb" )
        with stdout_redirector( devNull ):
            runner.run(suite)
    else:
        runner.run(suite)

