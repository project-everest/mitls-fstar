
//**********************************************************************************************************************************
//
//   Purpose: Interoperability Tester header file
//
//   Project: Everest
//
//  Filename: InteropTester.h
//
//   Authors: Caroline.M.Mathieson (CMM)
//
//**********************************************************************************************************************************
//
//  Description
//  -----------
//
//! \file InteropTester.h
//! \brief Contains the complete implementation of the Interoperability Tester.
//!
//**********************************************************************************************************************************

#include "stdafx.h"

//**********************************************************************************************************************************

FILE *OpenStatisticsFile ( const char *StatisticsFileName );

FILE *OpenDebugFile ( const char *DebugFileName );

void OperatorConfidence ( void );

void ProcessCommandLine ( int   ArgumentCount,
                          char *ArgumentList         [],
                          char *EnvironmentVariables [],
                          bool  Silent );

//**********************************************************************************************************************************

#pragma once
