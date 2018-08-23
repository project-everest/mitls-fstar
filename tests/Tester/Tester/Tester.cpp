
//**********************************************************************************************************************************
//
//   Purpose: TESTER OBJECT source code file
//
//   Project: Everest
//
//  Filename: Tester.cpp
//
//   Authors: Caroline.M.Mathieson (CMM)
//
//**********************************************************************************************************************************
//
//  Description
//  -----------
//
//! \file Tester.cpp
//! \brief Contains the complete implementation of the TESTER Object. This covers generic tester attributes and functions.
//!
//**********************************************************************************************************************************

#include "stdafx.h"
#include "time.h"     // for time and local_time
#include "winsock2.h" // for WSAStartup and WSACleanup
#include "windows.h"  // for sleep

#include "InteropTester.h"
#include "Tester.h"

//**********************************************************************************************************************************

extern int PrintSocketError ( void ); // in simpleserver.cpp

//**********************************************************************************************************************************

TESTER::TESTER ( FILE *NewDebugFile, FILE * NewComponentStatisticsFile, FILE *NewRecordedMeasurementsFile )
{
    DebugFile                = NewDebugFile;
    ComponentStatisticsFile  = NewComponentStatisticsFile;
    RecordedMeasurementsFile = NewRecordedMeasurementsFile;

    // initialise basic measurement variables

    memset ( &StartTime, 0, sizeof ( StartTime ) );
    memset ( &EndTime,   0, sizeof ( EndTime   ) );
    memset ( &Frequency, 0, sizeof ( Frequency ) );

    // initialise debug and console flags

    VerboseConsoleOutput = FALSE;

    ConsoleDebugging = FALSE;

    RedirectedStandardOutputFile = NULL;

    RedirectedStandardOutputFilename [ 0 ] = '\0';
 }

//**********************************************************************************************************************************

TESTER::~TESTER ( void )
{
    // nothing to do yet!
}

//**********************************************************************************************************************************

FILE *TESTER::GetDebugFile ( void )
{
    return ( DebugFile );
}

//**********************************************************************************************************************************

bool TESTER::Setup ( char *DateAndTimeString )
{
    int        ResultCode = 0;
    WSADATA    WindowsSocketsData;
    time_t     CurrentTime;
    struct tm *LocalTime;

    ResultCode = WSAStartup ( MAKEWORD ( 2, 2 ), &WindowsSocketsData );

    if ( ResultCode == 0 )
    {
        fprintf ( DebugFile, "Windows Sockets Interface Started:-\n");
        fprintf ( DebugFile, "\n" );
        fprintf ( DebugFile, "    Major Version: 0x%04X\n", WindowsSocketsData.wVersion       );
        fprintf ( DebugFile, "    Minor Version: 0x%04X\n", WindowsSocketsData.wHighVersion   );
        fprintf ( DebugFile, "      Max Sockets: %d\n",     WindowsSocketsData.iMaxSockets    );
        fprintf ( DebugFile, "   Max UDP Packet: %d\n",     WindowsSocketsData.iMaxUdpDg      );
        fprintf ( DebugFile, "      Description: %s\n",     WindowsSocketsData.szDescription  );
        fprintf ( DebugFile, "    System Status: %s\n",     WindowsSocketsData.szSystemStatus );
        fprintf ( DebugFile, "\n" );

        if ( VerboseConsoleOutput )
        {
            printf ( "Runnning!\n" );
        }
        else
        {
            if ( ! ConsoleDebugging ) // if console debugging is enabled then we "DO" want the output on the console!
            {
                // get the current date and time

                time ( &CurrentTime );

                LocalTime = localtime ( &CurrentTime );

                // and create a filename based on that for the redirected standard output

                sprintf ( RedirectedStandardOutputFilename,
                          "RedirectedStandardOutput_%02d_%02d_%2d_at_%02d_%02d_%02d.txt",
                          LocalTime->tm_wday,
                          LocalTime->tm_mday,
                          LocalTime->tm_year,
                          LocalTime->tm_hour,
                          LocalTime->tm_min,
                          LocalTime->tm_sec );

                 // now redirect the standard output stream into the capture file to hide the debug output from the dlls

                 RedirectedStandardOutputFile = freopen ( RedirectedStandardOutputFilename, "a", stdout );
            }
        }

        // you only need to get this once as it will not change for a given machine and os

        QueryPerformanceFrequency ( &Frequency ); // clock ticks per second

        QueryPerformanceCounter ( &StartTime );   // in clock ticks

        return ( TRUE );
    }
    else
    {
        fprintf ( DebugFile, "Could not initialise Windows Sockets! ( ResultCode = %d )\n", ResultCode );

        PrintSocketError ();

        return ( FALSE );
    }
}

//**********************************************************************************************************************************

bool TESTER::TearDown ( void )
{
    QueryPerformanceCounter ( &EndTime ); // in clock ticks

    // now work out the run time

    fprintf ( DebugFile, "Total Run Time was: %u microseconds\n", CalculateExecutionTime ( StartTime, EndTime ) );

    PrintMeasurementResults ( RecordedMeasurementsFile );

    fprintf ( DebugFile, "Closing Windows Sockets!\n" );

    WSACleanup ();

    return ( TRUE );
}

//**********************************************************************************************************************************

long TESTER::CalculateExecutionTime ( LARGE_INTEGER StartingTime, LARGE_INTEGER EndingTime )
{
    LARGE_INTEGER ElapsedMicroseconds;
    __int64       ScaledTime;
    double        ElapsedTime;

    ElapsedMicroseconds.QuadPart = EndingTime.QuadPart - StartingTime.QuadPart; // calculate delta time
    ElapsedMicroseconds.QuadPart *= 1000000;                                    // convert it to clock ticks
    ElapsedMicroseconds.QuadPart /= Frequency.QuadPart;                         // convert to microseconds

    ScaledTime = ( (EndingTime.QuadPart) - (StartingTime.QuadPart) ) * 1000000;

    ElapsedTime = (double) ScaledTime / (double) ( Frequency.QuadPart );

    return ( long ( ElapsedTime ) );
}

//**********************************************************************************************************************************

