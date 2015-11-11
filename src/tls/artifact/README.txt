This snapshot includes 8 verified modules (out of 45) of the miTLS
project, plus various supporting files.

TLSError.fst: error messages returned by miTLS 

TLSConstants.fst : constants used by TLS, and their wire formats

Nonce.fst: random nonces used as unique identifiers, including the
           modelling of collision-avoidance.

TLSInfo.fst : indexing for keys and sessions, plus user-customizable
              protocol behavior, which captures partially specified
              parts (MAY) of the RFC.

Range.fst: reasoning about the range of lengths of plaintext
           bytestrings; this matter for modelling lenght-hiding
           encryption mechanisms in TLS.

StatefulPlain.fsti: an interface hiding TLS formats for encrypted payloads.

LHAEPlain.fst: an implementation of encrypted payloads for
               authenticated encryption based on StatefulPlain.fsti

AEAD_GCM.fst : authenticated encryption with additional data
               implemented using GCM

StatefulLHAE.fst : part of TLS record protocol implementing stateful
                   length-hiding AEAD, dealing with sequence numbers

These modules concern the record layer; the most interesting are
AEAD_GCM and StatefulLHAE, showing our application of hyperheaps. The
others are simpler but still illustrate the re-use of code in
specifications and implementations.

We believe these modules are fairly self-contained and can be read
without the need to understand the full miTLS stack.
