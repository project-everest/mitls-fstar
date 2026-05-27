# Bug Reports

This directory contains reproductions and documentation of bugs encountered during the agentic-tls project.

## karamel-bundle-nth-failure/

Attempted to create a minimal reproduction of a KaRaMeL bundling bug (`Failure("nth")` during pattern match compilation) encountered when bundling TLS13 modules.

**Status**: The bug does NOT reproduce with simple pattern matching examples. The issue appears specific to the complexity of the actual TLS13 code.

**For bug reporting**: Use the full TLS13 project as the reproduction case.  The bug occurs when bundling `TLS13.Handshake.FlightState`, `TLS13.Record`, or `TLS13.KeySchedule` with `TLS13.Connection`.

See `karamel-bundle-nth-failure/UNABLE_TO_REPRODUCE.md` for details.
