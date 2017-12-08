module KeySchedule

// Specifying and statefully growing the whole TLS derivation
// tree. TODO! see also KDF.Rekey.fst

// What used to be here is now in Handshake.Secret.fst, handling
// larger sequences of key derivations for each message flight.
