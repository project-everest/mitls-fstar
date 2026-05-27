#!/bin/bash
# Test: Bundle TLS13.Connection with all other TLS13 modules as internal

cd _output

# Try the correct bundle pattern:
# TLS13.Connection is the API module (functions without prefix)
# All other TLS13.* modules become internal (bundled into Connection)

krml \
  -tmpdir ../test-bundle \
  -skip-compilation \
  -warn-error -2-9-17 \
  -bundle 'TLS13.Connection=TLS13.Connection.Driver,TLS13.Connection.StateDriver,TLS13.Handshake,TLS13.Handshake.ByteDriver,TLS13.Handshake.Driver,TLS13.Handshake.FlightState,TLS13.Handshake.Framing,TLS13.Handshake.StateDriver,TLS13.Handshake.Transcript,TLS13.KeySchedule,TLS13.Record,TLS13.Record.Framing,TLS13.State[rename=TLS13]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
  -no-prefix TLS13.Connection \
  TLS13_Connection.krml \
  TLS13_Connection_Driver.krml \
  TLS13_Connection_StateDriver.krml \
  TLS13_Handshake.krml \
  TLS13_Handshake_ByteDriver.krml \
  TLS13_Handshake_Driver.krml \
  TLS13_Handshake_FlightState.krml \
  TLS13_Handshake_Framing.krml \
  TLS13_Handshake_StateDriver.krml \
  TLS13_Handshake_Transcript.krml \
  TLS13_KeySchedule.krml \
  TLS13_Record.krml \
  TLS13_Record_Framing.krml \
  TLS13_State.krml \
  FStar_Pervasives_Native.krml

echo ""
echo "=== Generated files ==="
ls -lh ../test-bundle/TLS13.*
echo ""
echo "=== Public API in TLS13.h ==="
grep "^[a-zA-Z_].*client_" ../test-bundle/TLS13.h | head -10
echo ""
echo "=== Internal TLS13_* functions ==="
grep "^[a-zA-Z_].*TLS13_" ../test-bundle/TLS13.h | wc -l
