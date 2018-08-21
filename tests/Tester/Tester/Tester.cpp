
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
//! \brief Contains the complete implementation of the TESTER Object.
//!
//**********************************************************************************************************************************

#include "stdafx.h"
#include "winsock2.h" // for WSAStartup and WSACleanup
#include "windows.h" // for sleep

#include "InteropTester.h"
#include "Tester.h"

//**********************************************************************************************************************************

extern int PrintSocketError ( void );

//**********************************************************************************************************************************

TESTER::TESTER ( FILE *NewDebugFile, FILE * NewComponentStatisticsFile, FILE *NewRecordedMeasurementsFile )
{
   DebugFile                = NewDebugFile;
   ComponentStatisticsFile  = NewComponentStatisticsFile;
   RecordedMeasurementsFile = NewRecordedMeasurementsFile;
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

bool TESTER::Setup ( void )
{
    int     ResultCode = 0;
    WSADATA WindowsSocketsData;

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

        printf ( "Runnning!\n" );

        // you only need to get this once as it will not change for a given machine and os

        QueryPerformanceFrequency ( &Frequency ); // clock ticks per second

        QueryPerformanceCounter ( &StartTime );  // in clock ticks

        return ( TRUE );
    }
    else
    {
        fprintf ( DebugFile, "Could not initialise Windows Sockets! (ResultCode=%d)\n", ResultCode );

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

    return ( FALSE );
}

//**********************************************************************************************************************************

long TESTER::CalculateExecutionTime ( LARGE_INTEGER StartingTime, LARGE_INTEGER EndingTime )
{
    LARGE_INTEGER ElapsedMicroseconds;
    __int64       ScaledTime;
    double        ElapsedTime;

    ElapsedMicroseconds.QuadPart = EndingTime.QuadPart - StartingTime.QuadPart;
    ElapsedMicroseconds.QuadPart *= 1000000;
    ElapsedMicroseconds.QuadPart /= Frequency.QuadPart;

    ScaledTime = ( (EndingTime.QuadPart) - (StartingTime.QuadPart) ) * 1000000;

    ElapsedTime = (double) ScaledTime / (double) ( Frequency.QuadPart );

    return ( long ( ElapsedTime ) );
}

//**********************************************************************************************************************************

