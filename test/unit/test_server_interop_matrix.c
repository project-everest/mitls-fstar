/* Verified-server capability matrix.
 *
 * WHAT THIS IS FOR
 *
 * `test_extracted_server_openssl_client` proves the verified server completes
 * one handshake -- against an OpenSSL client pinned, by hand, to exactly one
 * profile (TLS_CHACHA20_POLY1305_SHA256 / X25519 / rsa_pss_rsae_sha256,
 * middlebox-compatibility mode on, one TLS record per flight).  That test cannot answer the question that matters for interop:
 * *which* offers does the verified server accept, and which does it refuse?
 * Pinning the peer to the server's own profile makes every gap invisible.
 *
 * This harness answers that question by construction.  It drives an OpenSSL
 * client across a matrix of offers -- cipher suites, key-exchange groups,
 * signature schemes, middlebox-compatibility mode, and TCP/record framing --
 * and asserts the OBSERVED outcome of each cell against a recorded
 * expectation.
 *
 * THE EXPECTATIONS ARE TWO-SIDED ON PURPOSE
 *
 * A cell recorded as EXPECT_FAIL is a known parity gap with the verified
 * client, and the test fails if that cell starts SUCCEEDING.  That is not
 * pedantry: it is how the ledger stays honest.  When someone implements
 * secp256r1 or an ECDSA credential on the server, this test tells them exactly
 * which line to flip, and the diff records the capability change in the same
 * commit as the implementation.  A one-sided "known failures are skipped"
 * harness would let the gap close silently and then let it reopen silently.
 * The `aes128-only` cell is the worked example: it was EXPECT_FAIL until the
 * server became cipher-suite agile, and flipped to OK in that same commit.
 * `no-middlebox-compat` is the second: it flipped when the server learned to
 * echo the offered legacy_session_id verbatim.
 *
 * THE FRAMING AXIS
 *
 * Cipher suites and groups are what a peer offers; framing is what the network
 * does to the offer.  Two framings are distinguished, because the verified
 * server treats them completely differently:
 *
 *   FRAMING_TCP_DRIBBLE   one TLS record delivered in many small TCP segments.
 *                         The server's retained receive buffer and its
 *                         NeedMoreInput retry loop handle this, and this cell
 *                         guards that loop against regression.
 *
 *   FRAMING_RECORD_SPLIT  one handshake message delivered as two TLS records.
 *                         Refused today (gap G3).  It is tempting to call this
 *                         "the server-side mirror of the reassembly the client
 *                         gained for the top-100 sweep", but that overstates
 *                         what the client has.  `protected_handshake_buffering`
 *                         is confined to the PROTECTED path and to stages after
 *                         ServerHello (`protected_handshake_buffering_stage` =
 *                         HsServerHelloReceived, HsEncryptedExtensionsReceived,
 *                         HsCertificateValidated, HsCertificateVerifyVerified),
 *                         so a ServerHello split across two records would be
 *                         refused by the CLIENT just as a ClientHello is by the
 *                         server.  There is no cleartext reassembly in the tree
 *                         for either role.
 *
 *                         The reason the client's step cannot simply be reused
 *                         is structural, not just the `config_role ==
 *                         ClientEndpoint` guard on
 *                         `legal_protected_handshake_step`: the protected event
 *                         `ConnProtectedHandshake` carries bytes (fragment,
 *                         offset, consumed), whereas the cleartext event
 *                         `ConnNetworkEvent` carries an already-PARSED
 *                         tls_message, and `parse_tls_message` requires
 *                         consumed == length fragment.  A cleartext record IS
 *                         exactly one whole message, so there is nowhere to put
 *                         a partial one.  See docs/server-client-parity.md, G3.
 *
 * The split is performed by an in-process TCP proxy that re-frames the
 * client->server byte stream at the record layer.  It only ever re-frames
 * CLEARTEXT handshake records: a protected record is a single AEAD-sealed
 * unit, so splitting its ciphertext would test nothing but the AEAD tag.
 *
 * WHAT THE KEY-SHARE AXIS DOES AND DOES NOT COVER.  The cells whose group list
 * is "X25519:P-256" configure the client's *supported_groups*, not the number
 * of KeyShareEntry values it sends.  This was measured rather than assumed:
 * OpenSSL 3.0 emits exactly ONE key_share, for the first group in the list, in
 * every configuration above (X25519:P-256 -> one 32-byte 0x001d entry;
 * P-256:X25519 -> one 65-byte 0x0017 entry).  The "*" key-share prefix that
 * would ask for two is an OpenSSL 3.2 feature.  So those cells exercise "one
 * share offered, a second group merely listed".  Before G2 that shape was
 * predicted to need a HelloRetryRequest for p256-first-x25519-listed; it does
 * not, because the server follows the share that was actually sent rather than
 * the client's preference order, so that cell now completes at secp256r1
 * directly.  HelloRetryRequest remains unimplemented and unexercised here.
 *
 * The genuinely multi-KeyShareEntry ClientHello is exercised by
 * test_atlas_loopback, because the verified CLIENT's canonical ClientHello
 * carries two entries -- [kse; pkse], X25519 and secp256r1, at
 * TLS13.Impl.ConnectionState.Model.client_hello_of_start.  That is the path
 * the server's group-tagged acceptance scan and its 65-byte secp256r1 mirror
 * slot are on, so the two tests are complementary and neither subsumes the
 * other.
 */

#include "tls13_server_driver.h"

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <openssl/err.h>
#include <openssl/obj_mac.h>
#include <openssl/objects.h>
#include <signal.h>
#include <openssl/ssl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

/* One application record each way is enough here: this harness measures which
   offers reach an established connection, not how the connection behaves once
   established.  Post-handshake behaviour (KeyUpdate epochs, multi-record echo)
   is covered by test_extracted_server_openssl_client and test_atlas_loopback. */
static const uint8_t k_ping[] = {'p', 'i', 'n', 'g'};

/* Which server credential a cell runs against.  See the credential axis in
   the matrix below. */
typedef enum {
  CRED_RSA = 0,
  CRED_ECDSA_P256,
} server_credential;

typedef enum {
  FRAMING_NORMAL = 0,
  FRAMING_TCP_DRIBBLE,
  FRAMING_RECORD_SPLIT,
} framing_mode;

struct case_spec {
  const char *name;
  const char *ciphersuites; /* NULL: OpenSSL's own TLS 1.3 default list */
  const char *groups;       /* NULL: OpenSSL's own default group list */
  const char *sigalgs;      /* NULL: OpenSSL's own default sigalg list */
  /* Which credential the verified server is started with.  The server's
     allowed signature schemes are exactly the one its own key can produce
     (TLS13.Crypto.Spec.credential_signature_scheme), so this axis and the
     sigalgs axis have to agree for a cell to succeed. */
  server_credential credential;
  bool middlebox_compat;    /* RFC 8446 D.4 compatibility mode */
  framing_mode framing;
  bool expect_ok;
  /* When the cell is expected to succeed, the parameters the server must have
     selected, as OpenSSL names them (SSL_get_cipher_name /
     SSL_get_negotiated_group_name).  NULL means "do not check".  Asserting
     these is what makes an OK cell say something: without them a cell would
     still pass if the server had negotiated a different suite or group than
     the one the case is about, which is exactly the confusion a capability
     matrix exists to prevent. */
  const char *expect_cipher;
  const char *expect_group;
  const char *note;
  /* The single protocol version the OpenSSL client is pinned to (min == max),
     as an OpenSSL version constant.  Every cell but the version-axis one is
     TLS13_ONLY.  TLS1_2_VERSION produces a ClientHello with no
     supported_versions entry naming TLS 1.3, which the verified server must
     refuse -- it implements exactly one protocol version. */
  int version;
};

/* ── The matrix ────────────────────────────────────────────────────────────
 *
 * Every EXPECT_FAIL row cites the reason in `note`; see
 * docs/server-client-parity.md for the full analysis behind each one.
 */
#define OK true
#define FAIL false
/* The protocol version every cell but the version-axis one offers. */
#define TLS13_ONLY TLS1_3_VERSION

static const struct case_spec k_cases[] = {
    /* --- Baseline: the profile the verified server implements. ----------- */
    {"baseline-chacha-x25519", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "the server's single supported profile", TLS13_ONLY},

    /* --- What a real peer actually offers. ------------------------------ */
    {"openssl-defaults", NULL, NULL, NULL, CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "OpenSSL's stock TLS 1.3 offer; the server must pick chacha out of it", TLS13_ONLY},

    /* The verified CLIENT's own offer, transcribed.  This is the same shape
       test_atlas_loopback drives through the real client; having it here too
       localises a failure to the negotiation surface rather than the driver. */
    {"atlas-client-offer",
     "TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256", "X25519:P-256",
     "rsa_pss_rsae_sha256:ecdsa_secp256r1_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "the offer TLS13.Impl.ConnectionState.Repr.default_connection_config makes", TLS13_ONLY},

    /* --- Cipher-suite axis. --------------------------------------------- */
    /* CLOSED (gap G1).  The server's negotiation is now the deterministic
       policy TLS13.Impl.ConnectionState.Model.server_selected_suite: prefer
       ChaCha20-Poly1305, fall back to AES-128-GCM.  It is a function of the
       stored ClientHello alone, so the ServerHello writer recovers it at
       runtime (CQ.read_negotiated_server_suite) from the same mirror the
       selection was made from -- no suite parameter is threaded through the
       driver.  TLS13.Spec.StateMachine.server_hello_matches_selection now
       requires only H.is_supported_cipher_suite. */
    {"aes128-only", "TLS_AES_128_GCM_SHA256", "X25519", "rsa_pss_rsae_sha256",
     CRED_RSA, true, FRAMING_NORMAL, OK, "TLS_AES_128_GCM_SHA256", "X25519",
     "fallback arm of the negotiation policy: no chacha offered", TLS13_ONLY},
    {"aes256-only", "TLS_AES_256_GCM_SHA384", "X25519", "rsa_pss_rsae_sha256",
     CRED_RSA, true, FRAMING_NORMAL, FAIL, NULL, NULL,
     "neither endpoint implements TLS_AES_256_GCM_SHA384 (SHA-384 schedule)", TLS13_ONLY},
    /* Suite preference: chacha is offered but listed last.  The server selects
       by its own preference, not the client's, which RFC 8446 4.1.1 permits. */
    {"aes-first-chacha-last",
     "TLS_AES_256_GCM_SHA384:TLS_AES_128_GCM_SHA256:TLS_CHACHA20_POLY1305_SHA256",
     "X25519", "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "server preference wins: chacha selected though offered last", TLS13_ONLY},
    /* The fallback arm again, but with the unsupported AES-256 listed first:
       exercises "skip what I cannot do, then fall back" rather than "the offer
       had exactly one entry". */
    {"aes256-then-aes128", "TLS_AES_256_GCM_SHA384:TLS_AES_128_GCM_SHA256",
     "X25519", "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_AES_128_GCM_SHA256", "X25519",
     "AES-128-GCM selected past an unsupported AES-256-GCM offer", TLS13_ONLY},
    /* AES-128-GCM on the non-trivial framing path, so the fallback arm is
       covered end-to-end through the retry loop as well. */
    {"aes128-tcp-dribble", "TLS_AES_128_GCM_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_TCP_DRIBBLE, OK,
     "TLS_AES_128_GCM_SHA256", "X25519",
     "AES-128-GCM record layer driven through the NeedMoreInput retry loop", TLS13_ONLY},

    /* --- Key-exchange axis. --------------------------------------------- */
    /* G2 closed (stage S6.8d): TLS13.Wire.Spec.ch_key_share_pick accepts a
       ClientHello whose only key_share is a well-formed secp256r1 one, and the
       whole server path -- ECDH, ServerHello group tag, and record length --
       follows the group the acceptance gate picked. */
    {"p256-only", "TLS_CHACHA20_POLY1305_SHA256", "P-256",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "prime256v1",
     "secp256r1-only offer completed at secp256r1", TLS13_ONLY},
    {"x25519-and-p256", "TLS_CHACHA20_POLY1305_SHA256", "X25519:P-256",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "X25519 share offered with P-256 also in supported_groups", TLS13_ONLY},
    /* Both agile axes at once: AES-128-GCM selected while a second group is
       also on offer.  Guards against a regression where the suite fallback is
       reachable only when supported_groups names one group. */
    {"aes128-x25519-and-p256", "TLS_AES_128_GCM_SHA256", "X25519:P-256",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_AES_128_GCM_SHA256", "X25519",
     "suite fallback and a two-group supported_groups together", TLS13_ONLY},
    /* P-256 listed first makes OpenSSL send its key_share for P-256 only and
       list X25519 in supported_groups.  Before G2 that needed a
       HelloRetryRequest; now the server simply takes the offered group. */
    {"p256-first-x25519-listed", "TLS_CHACHA20_POLY1305_SHA256",
     "P-256:X25519", "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "prime256v1",
     "only a secp256r1 key_share was sent, so secp256r1 is what gets used",
     TLS13_ONLY},
    /* The same case under a different credential.  G2 was a key-exchange gap,
       so its closure must not depend on the signature axis; recording it twice
       is what makes a partial fix (P-256 that only works for RSA, say) visible
       rather than silently accepted. */
    {"ecdsa-credential-p256-only", "TLS_CHACHA20_POLY1305_SHA256", "P-256",
     "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "prime256v1",
     "secp256r1 key exchange is independent of the credential axis", TLS13_ONLY},

    /* --- Signature-scheme axis. ----------------------------------------- */
    {"rsa-pss-only", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "the scheme the RSA test credential is signed under", TLS13_ONLY},
    {"ecdsa-only-rsa-credential", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ecdsa_secp256r1_sha256", CRED_RSA, true, FRAMING_NORMAL, FAIL, NULL, NULL,
     "correctly refused: an RSA credential cannot satisfy an ECDSA-only offer", TLS13_ONLY},

    /* --- Credential axis (gap G5). --------------------------------------
     *
     * CLOSED.  The server's allowed signature scheme is no longer the literal
     * rsa_pss_rsae_sha256: it is TLS13.Crypto.Spec.credential_signature_scheme
     * applied to the credential the server was configured with, and the wire
     * code written into CertificateVerify comes from the same credential
     * (TLS13.OpenSSL.server_credential_signature_scheme).  The spec-level
     * scheme and the wire code therefore cannot drift, and
     * TLS13.Spec.StateMachine.server_selection_acceptable still demands that
     * the scheme appear in the client's signature_algorithms.
     *
     * These four cells are the two-sided statement of that: the same offer
     * succeeds or is refused purely as a function of which key the server
     * holds. */
    {"ecdsa-only", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, true, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ECDSA P-256 credential signs CertificateVerify under ecdsa_secp256r1_sha256", TLS13_ONLY},
    {"rsa-pss-only-ecdsa-credential", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_ECDSA_P256, true, FRAMING_NORMAL, FAIL, NULL,
     NULL,
     "correctly refused: an ECDSA credential cannot satisfy an RSA-only offer", TLS13_ONLY},
    /* Both schemes offered: the server picks the one its own key supports,
       which is the whole point of making the scheme follow the credential. */
    {"both-sigalgs-ecdsa-credential", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256:ecdsa_secp256r1_sha256", CRED_ECDSA_P256, true,
     FRAMING_NORMAL, OK, "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ECDSA selected out of a two-scheme offer because the credential is EC", TLS13_ONLY},
    {"both-sigalgs-rsa-credential", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256:ecdsa_secp256r1_sha256", CRED_RSA, true,
     FRAMING_NORMAL, OK, "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "same offer, RSA credential: the other arm of the same negotiation", TLS13_ONLY},
    /* The credential axis crossed with the other closed gaps, so an ECDSA
       credential is not quietly confined to the baseline profile. */
    {"ecdsa-credential-aes128", "TLS_AES_128_GCM_SHA256", "X25519",
     "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, true, FRAMING_NORMAL, OK,
     "TLS_AES_128_GCM_SHA256", "X25519",
     "ECDSA credential with the AES-128-GCM fallback arm (gap G1)", TLS13_ONLY},
    {"ecdsa-credential-no-middlebox-compat", "TLS_CHACHA20_POLY1305_SHA256",
     "X25519", "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, false,
     FRAMING_NORMAL, OK, "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ECDSA credential with an empty legacy_session_id echo (gap G4)", TLS13_ONLY},
    {"ecdsa-credential-dribble", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, true, FRAMING_TCP_DRIBBLE, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ECDSA CertificateVerify driven through the NeedMoreInput retry loop", TLS13_ONLY},
    {"ecdsa-credential-openssl-defaults", NULL, NULL, NULL, CRED_ECDSA_P256,
     true, FRAMING_NORMAL, OK, "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "a stock OpenSSL client against an ECDSA-credentialled verified server", TLS13_ONLY},
    /* The credential axis crossed with the remaining two negotiation axes, so
       that "the scheme follows the credential" cannot silently become "the
       scheme follows the credential, but only when nothing else varies". */
    {"ecdsa-credential-x25519-and-p256", "TLS_CHACHA20_POLY1305_SHA256",
     "X25519:P-256", "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, true,
     FRAMING_NORMAL, OK, "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ECDSA credential with a two-group supported_groups", TLS13_ONLY},
    {"ecdsa-credential-aes-first-chacha-last",
     "TLS_AES_256_GCM_SHA384:TLS_AES_128_GCM_SHA256:TLS_CHACHA20_POLY1305_SHA256",
     "X25519", "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, true, FRAMING_NORMAL,
     OK, "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "ECDSA credential with the server's own suite preference exercised", TLS13_ONLY},
    /* All three closed gaps at once: ECDSA credential (G5), the AES-128-GCM
       fallback arm (G1) and the empty legacy_session_id echo (G4), on the
       retry loop (framing).  If any one of them is only reachable when the
       others are at their default, this cell is the one that says so. */
    {"ecdsa-credential-aes128-no-middlebox-dribble", "TLS_AES_128_GCM_SHA256",
     "X25519", "ecdsa_secp256r1_sha256", CRED_ECDSA_P256, false,
     FRAMING_TCP_DRIBBLE, OK, "TLS_AES_128_GCM_SHA256", "X25519",
     "gaps G1, G4 and G5 crossed with the NeedMoreInput retry loop", TLS13_ONLY},

    /* --- Middlebox-compatibility axis (RFC 8446 D.4). -------------------- */
    /* CLOSED (gap G4).  With compatibility mode off OpenSSL sends an EMPTY
       legacy_session_id and no ChangeCipherSpec.  RFC 8446 4.1.3 requires the
       ServerHello's legacy_session_id_echo to be the offered id VERBATIM, so a
       fixed 32-byte mirror could not serve both widths.  The mirror now carries
       the id as a 32-byte zero-padded buffer plus an explicit width
       (TLS13.Wire.Semantics.pad_session_id_32 / clientHello_session_id, the
       same shape CryptoSpec.pad_share_65 uses for key shares), and the width is
       stored in the connection as a box alongside the other ClientHello
       metadata lengths.  The ServerHello message is therefore 90 + |sid| bytes
       and its record 95 + |sid| -- 122/127 only in the compatibility case --
       so the send path sizes its output buffer at run time. */
    {"no-middlebox-compat", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, false, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "empty legacy_session_id echoed verbatim: a 90-byte ServerHello", TLS13_ONLY},
    /* The empty-id path crossed with the two other agile axes, so a regression
       that reintroduced a fixed-width echo cannot hide behind the compat case
       on any one of them. */
    {"no-middlebox-compat-aes128", "TLS_AES_128_GCM_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, false, FRAMING_NORMAL, OK,
     "TLS_AES_128_GCM_SHA256", "X25519",
     "empty session id and the AES-128-GCM fallback arm together", TLS13_ONLY},
    {"no-middlebox-compat-dribble", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, false, FRAMING_TCP_DRIBBLE, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "empty session id driven through the NeedMoreInput retry loop", TLS13_ONLY},
    {"no-middlebox-compat-x25519-and-p256", "TLS_CHACHA20_POLY1305_SHA256",
     "X25519:P-256", "rsa_pss_rsae_sha256", CRED_RSA, false, FRAMING_NORMAL, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "empty session id with a two-group supported_groups", TLS13_ONLY},

    /* --- Framing axis. --------------------------------------------------- */
    {"tcp-dribble", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_TCP_DRIBBLE, OK,
     "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "one record split across many TCP segments: the NeedMoreInput retry loop", TLS13_ONLY},
    {"clienthello-across-two-records", "TLS_CHACHA20_POLY1305_SHA256", "X25519",
     "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_RECORD_SPLIT, FAIL, NULL, NULL,
     "GAP: no server-side cross-record handshake reassembly (the client has it)", TLS13_ONLY},
    /* G3 is a record-layer gap, so it must not depend on the suite axis
       either.  Same reasoning as ecdsa-credential-p256-only above. */
    {"aes128-clienthello-across-two-records", "TLS_AES_128_GCM_SHA256",
     "X25519", "rsa_pss_rsae_sha256", CRED_RSA, true, FRAMING_RECORD_SPLIT,
     FAIL, NULL, NULL,
     "GAP (G3): the reassembly gap is independent of the cipher-suite axis", TLS13_ONLY},

    /* --- Protocol-version axis. ------------------------------------------
     *
     * The verified server implements exactly one protocol version.  A TLS 1.2
     * ClientHello carries no supported_versions extension naming TLS 1.3, and
     * TLS13.Wire.Spec.clientHello_representable requires the scan to have seen
     * one (`saw_supported_versions`), so the ClientHello is refused at the
     * parser rather than downgraded.  This cell is a negative capability
     * assertion: it fails loudly if the server ever starts accepting an offer
     * that does not name TLS 1.3. */
    {"tls12-only", NULL, NULL, NULL, CRED_RSA, true, FRAMING_NORMAL, FAIL,
     NULL, NULL,
     "correctly refused: no supported_versions entry naming TLS 1.3",
     TLS1_2_VERSION},
};

#define CASE_COUNT (sizeof k_cases / sizeof k_cases[0])

/* ── Utilities ─────────────────────────────────────────────────────────── */

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return 1;
  }
  if (fseek(f, 0, SEEK_END) != 0 || ftell(f) < 0) {
    perror("fseek");
    fclose(f);
    return 1;
  }
  long len = ftell(f);
  rewind(f);
  uint8_t *buf = calloc((size_t)len == 0 ? 1u : (size_t)len, sizeof(uint8_t));
  if (buf == NULL) {
    fclose(f);
    return 1;
  }
  if (fread(buf, 1u, (size_t)len, f) != (size_t)len) {
    perror("fread");
    free(buf);
    fclose(f);
    return 1;
  }
  fclose(f);
  *out = buf;
  *out_len = (size_t)len;
  return 0;
}

static int reserve_loopback_port(uint16_t *port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    perror("socket");
    return -1;
  }
  int one = 1;
  (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(0);
  if (bind(fd, (struct sockaddr *)&addr, sizeof addr) != 0) {
    perror("bind");
    close(fd);
    return -1;
  }
  struct sockaddr_in bound;
  socklen_t bound_len = sizeof bound;
  if (getsockname(fd, (struct sockaddr *)&bound, &bound_len) != 0) {
    perror("getsockname");
    close(fd);
    return -1;
  }
  *port = ntohs(bound.sin_port);
  close(fd);
  return 0;
}

static int connect_loopback(uint16_t port) {
  for (int attempt = 0; attempt < 200; ++attempt) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
      return -1;
    }
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof addr);
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons(port);
    if (connect(fd, (struct sockaddr *)&addr, sizeof addr) == 0) {
      return fd;
    }
    close(fd);
    usleep(20000);
  }
  return -1;
}

static int write_all(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, buf + off, len - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    if (n == 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

static int read_exact(int fd, uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = read(fd, buf + off, len - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    if (n == 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

/* ── The re-framing proxy ──────────────────────────────────────────────────
 *
 * Listens on `listen_port`, connects to `server_port`, and applies `framing`
 * to the FIRST client->server TLS record (the ClientHello); everything after
 * that -- including every protected record -- is relayed byte for byte.
 */
static int run_proxy(uint16_t listen_port, uint16_t server_port, framing_mode framing) {
  alarm(30);
  int rc = 1;
  int listen_fd = -1;
  int client_fd = -1;
  int server_fd = -1;

  listen_fd = socket(AF_INET, SOCK_STREAM, 0);
  if (listen_fd < 0) {
    perror("proxy socket");
    goto done;
  }
  int one = 1;
  (void)setsockopt(listen_fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(listen_port);
  if (bind(listen_fd, (struct sockaddr *)&addr, sizeof addr) != 0 ||
      listen(listen_fd, 1) != 0) {
    perror("proxy bind/listen");
    goto done;
  }
  client_fd = accept(listen_fd, NULL, NULL);
  if (client_fd < 0) {
    perror("proxy accept");
    goto done;
  }
  server_fd = connect_loopback(server_port);
  if (server_fd < 0) {
    perror("proxy connect");
    goto done;
  }
  (void)setsockopt(server_fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);

  /* Read the first record whole: 5-byte header then the declared fragment. */
  uint8_t header[5];
  if (read_exact(client_fd, header, sizeof header) != 0) {
    fprintf(stderr, "proxy: short record header\n");
    goto done;
  }
  size_t frag_len = ((size_t)header[3] << 8) | (size_t)header[4];
  uint8_t *fragment = malloc(frag_len == 0 ? 1u : frag_len);
  if (fragment == NULL || read_exact(client_fd, fragment, frag_len) != 0) {
    fprintf(stderr, "proxy: short record fragment\n");
    free(fragment);
    goto done;
  }

  if (framing == FRAMING_RECORD_SPLIT && header[0] == 22 /* handshake */ &&
      frag_len >= 2) {
    /* Emit the same fragment as TWO handshake records.  The split point is
       deliberately inside the ClientHello body rather than on a message
       boundary -- a ClientHello is a single handshake message, so any split
       lands mid-message and is exactly the reassembly case under test.  It is
       past the 4-byte handshake header so the receiver has the message's
       declared length in the first record and can tell it is truncated rather
       than malformed. */
    size_t first = frag_len / 2;
    if (first < 8) {
      first = frag_len > 8 ? 8 : frag_len - 1;
    }
    uint8_t head[5];
    memcpy(head, header, 5);
    head[3] = (uint8_t)((first >> 8) & 0xffu);
    head[4] = (uint8_t)(first & 0xffu);
    size_t rest = frag_len - first;
    uint8_t tail[5];
    memcpy(tail, header, 5);
    tail[3] = (uint8_t)((rest >> 8) & 0xffu);
    tail[4] = (uint8_t)(rest & 0xffu);
    if (write_all(server_fd, head, 5) != 0 ||
        write_all(server_fd, fragment, first) != 0) {
      free(fragment);
      goto done;
    }
    /* A pause between the two records, so the receiver genuinely sees the
       first one on its own and cannot accidentally succeed by having both in
       its buffer when it first parses. */
    usleep(50000);
    if (write_all(server_fd, tail, 5) != 0 ||
        write_all(server_fd, fragment + first, rest) != 0) {
      free(fragment);
      goto done;
    }
  } else if (framing == FRAMING_TCP_DRIBBLE) {
    /* One TLS record, many TCP segments: header byte by byte, then the
       fragment in small chunks, with a pause after each so the receiver's
       read() genuinely returns short. */
    for (size_t i = 0; i < 5; ++i) {
      if (write_all(server_fd, header + i, 1) != 0) {
        free(fragment);
        goto done;
      }
      usleep(2000);
    }
    size_t off = 0;
    while (off < frag_len) {
      size_t chunk = frag_len - off < 7 ? frag_len - off : 7;
      if (write_all(server_fd, fragment + off, chunk) != 0) {
        free(fragment);
        goto done;
      }
      off += chunk;
      usleep(2000);
    }
  } else {
    if (write_all(server_fd, header, 5) != 0 ||
        write_all(server_fd, fragment, frag_len) != 0) {
      free(fragment);
      goto done;
    }
  }
  free(fragment);

  /* Verbatim bidirectional relay for the rest of the connection. */
  bool client_open = true;
  bool server_open = true;
  while (client_open || server_open) {
    fd_set rfds;
    FD_ZERO(&rfds);
    int maxfd = -1;
    if (client_open) {
      FD_SET(client_fd, &rfds);
      maxfd = client_fd > maxfd ? client_fd : maxfd;
    }
    if (server_open) {
      FD_SET(server_fd, &rfds);
      maxfd = server_fd > maxfd ? server_fd : maxfd;
    }
    struct timeval tv = {.tv_sec = 10, .tv_usec = 0};
    int ready = select(maxfd + 1, &rfds, NULL, NULL, &tv);
    if (ready < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }
    if (ready == 0) {
      break;
    }
    uint8_t buf[8192];
    if (client_open && FD_ISSET(client_fd, &rfds)) {
      ssize_t n = read(client_fd, buf, sizeof buf);
      if (n <= 0) {
        client_open = false;
        shutdown(server_fd, SHUT_WR);
      } else if (write_all(server_fd, buf, (size_t)n) != 0) {
        break;
      }
    }
    if (server_open && FD_ISSET(server_fd, &rfds)) {
      ssize_t n = read(server_fd, buf, sizeof buf);
      if (n <= 0) {
        server_open = false;
        shutdown(client_fd, SHUT_WR);
      } else if (write_all(client_fd, buf, (size_t)n) != 0) {
        break;
      }
    }
  }
  rc = 0;

done:
  if (client_fd >= 0) {
    close(client_fd);
  }
  if (server_fd >= 0) {
    close(server_fd);
  }
  if (listen_fd >= 0) {
    close(listen_fd);
  }
  return rc;
}

/* ── The verified server under test ────────────────────────────────────── */

static int run_verified_server(
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key,
    size_t private_key_len) {
  alarm(30);
  tls13_server_driver *server = NULL;
  uint8_t received[TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE] = {0};
  int rc = 1;

  if (tls13_server_driver_accept(
          &server, "127.0.0.1", port, certificate_chain, certificate_chain_len,
          private_key, private_key_len) != 0) {
    goto done;
  }
  size_t received_len = 0;
  if (tls13_server_driver_receive_application_data(
          server, received, sizeof received, &received_len) != 0 ||
      received_len != sizeof k_ping ||
      memcmp(received, k_ping, sizeof k_ping) != 0) {
    goto done;
  }
  if (tls13_server_driver_send_application_data(server, received, received_len) != 0) {
    goto done;
  }
  if (tls13_server_driver_close(server, true) == 0) {
    rc = 0;
  }

done:
  tls13_server_driver_free(server);
  return rc;
}

/* ── The OpenSSL client under each offer ───────────────────────────────── */

static int run_openssl_client(const struct case_spec *spec, uint16_t port,
                              const char *ca_path) {
  alarm(30);
  int rc = 1;
  SSL_CTX *ctx = NULL;
  SSL *ssl = NULL;
  int fd = -1;

  ctx = SSL_CTX_new(TLS_client_method());
  if (ctx == NULL) {
    goto done;
  }
  if (SSL_CTX_set_min_proto_version(ctx, spec->version) != 1 ||
      SSL_CTX_set_max_proto_version(ctx, spec->version) != 1 ||
      SSL_CTX_load_verify_locations(ctx, ca_path, NULL) != 1) {
    goto done;
  }
  if (spec->ciphersuites != NULL &&
      SSL_CTX_set_ciphersuites(ctx, spec->ciphersuites) != 1) {
    goto done;
  }
  if (spec->groups != NULL && SSL_CTX_set1_groups_list(ctx, spec->groups) != 1) {
    goto done;
  }
  if (spec->sigalgs != NULL && SSL_CTX_set1_sigalgs_list(ctx, spec->sigalgs) != 1) {
    goto done;
  }
  if (!spec->middlebox_compat) {
    SSL_CTX_clear_options(ctx, SSL_OP_ENABLE_MIDDLEBOX_COMPAT);
  }
  SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, NULL);

  fd = connect_loopback(port);
  if (fd < 0) {
    goto done;
  }
  struct timeval timeout = {.tv_sec = 10, .tv_usec = 0};
  (void)setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof timeout);
  (void)setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof timeout);

  ssl = SSL_new(ctx);
  if (ssl == NULL || SSL_set_fd(ssl, fd) != 1 ||
      SSL_set_tlsext_host_name(ssl, "localhost") != 1 ||
      SSL_set1_host(ssl, "localhost") != 1) {
    goto done;
  }
  if (SSL_connect(ssl) != 1) {
    goto done;
  }
  /* The handshake succeeded; now check that it succeeded on the parameters the
     cell is about.  A cell that merely connects proves much less than a cell
     that connects on a named suite and a named group. */
  if (spec->expect_cipher != NULL) {
    const char *cipher = SSL_get_cipher_name(ssl);
    if (cipher == NULL || strcmp(cipher, spec->expect_cipher) != 0) {
      fprintf(stderr, "  %s: negotiated cipher %s, expected %s\n", spec->name,
              cipher == NULL ? "(none)" : cipher, spec->expect_cipher);
      goto done;
    }
  }
  if (spec->expect_group != NULL) {
    /* OpenSSL 3.0 has no SSL_get0_group_name (3.2+), so go through the NID's
       short name: "X25519" / "prime256v1". */
    const char *group = OBJ_nid2sn(SSL_get_negotiated_group(ssl));
    if (group == NULL || strcmp(group, spec->expect_group) != 0) {
      fprintf(stderr, "  %s: negotiated group %s, expected %s\n", spec->name,
              group == NULL ? "(none)" : group, spec->expect_group);
      goto done;
    }
  }
  if (SSL_write(ssl, k_ping, (int)sizeof k_ping) != (int)sizeof k_ping) {
    goto done;
  }
  uint8_t echoed[sizeof k_ping] = {0};
  if (SSL_read(ssl, echoed, (int)sizeof echoed) != (int)sizeof echoed ||
      memcmp(echoed, k_ping, sizeof k_ping) != 0) {
    goto done;
  }
  (void)SSL_shutdown(ssl);
  rc = 0;

done:
  ERR_clear_error();
  if (ssl != NULL) {
    SSL_free(ssl);
  }
  if (fd >= 0) {
    close(fd);
  }
  if (ctx != NULL) {
    SSL_CTX_free(ctx);
  }
  return rc;
}

/* ── One cell ──────────────────────────────────────────────────────────── */

/* Returns true when the connection was established AND echoed.  Both peers
   must agree: a client that thinks it succeeded while the server aborted is a
   failure of the cell, not a success. */
struct credential_material {
  uint8_t *certificate_chain;
  size_t certificate_chain_len;
  uint8_t *private_key;
  size_t private_key_len;
};

static bool run_case(const struct case_spec *spec,
                     const struct credential_material *creds,
                     const char *ca_path) {
  const uint8_t *certificate_chain = creds->certificate_chain;
  size_t certificate_chain_len = creds->certificate_chain_len;
  const uint8_t *private_key = creds->private_key;
  size_t private_key_len = creds->private_key_len;
  uint16_t server_port = 0;
  uint16_t proxy_port = 0;
  if (reserve_loopback_port(&server_port) != 0) {
    return false;
  }
  bool proxied = spec->framing != FRAMING_NORMAL;
  if (proxied && reserve_loopback_port(&proxy_port) != 0) {
    return false;
  }

  pid_t server_pid = fork();
  if (server_pid < 0) {
    perror("fork");
    return false;
  }
  if (server_pid == 0) {
    _exit(run_verified_server(server_port, certificate_chain, certificate_chain_len,
                              private_key, private_key_len) == 0
              ? 0
              : 1);
  }

  pid_t proxy_pid = -1;
  if (proxied) {
    proxy_pid = fork();
    if (proxy_pid < 0) {
      perror("fork");
      kill(server_pid, SIGKILL);
      (void)waitpid(server_pid, NULL, 0);
      return false;
    }
    if (proxy_pid == 0) {
      _exit(run_proxy(proxy_port, server_port, spec->framing) == 0 ? 0 : 1);
    }
  }

  int client_rc = run_openssl_client(spec, proxied ? proxy_port : server_port, ca_path);

  int server_status = 0;
  /* The verified server is expected to hang up quickly on a rejected offer;
     its own alarm(30) bounds the pathological case. */
  if (waitpid(server_pid, &server_status, 0) < 0) {
    perror("waitpid");
    return false;
  }
  if (proxy_pid > 0) {
    kill(proxy_pid, SIGKILL);
    (void)waitpid(proxy_pid, NULL, 0);
  }
  bool server_ok = WIFEXITED(server_status) && WEXITSTATUS(server_status) == 0;
  return client_rc == 0 && server_ok;
}

int main(int argc, char **argv) {
  bool report_only = (argc > 1 && strcmp(argv[1], "--report") == 0);
  uint8_t *certificate_chain = NULL;
  uint8_t *private_key = NULL;
  size_t certificate_chain_len = 0;
  size_t private_key_len = 0;
  uint8_t *ec_certificate_chain = NULL;
  uint8_t *ec_private_key = NULL;
  size_t ec_certificate_chain_len = 0;
  size_t ec_private_key_len = 0;
  int rc = 1;

  if (read_file("test/certs/leaf.der", &certificate_chain, &certificate_chain_len) != 0 ||
      read_file("test/certs/leaf.key", &private_key, &private_key_len) != 0) {
    goto done;
  }
  /* The ECDSA credential is issued by the same test CA, so the client's trust
     anchor does not vary across the credential axis: only the leaf key does. */
  if (read_file("test/certs/ec-leaf.der", &ec_certificate_chain,
                &ec_certificate_chain_len) != 0 ||
      read_file("test/certs/ec-leaf.key", &ec_private_key, &ec_private_key_len) != 0) {
    fprintf(stderr,
            "missing ECDSA test credential; run scripts/generate-test-certs.sh\n");
    goto done;
  }

  const struct credential_material credentials[] = {
      [CRED_RSA] = {certificate_chain, certificate_chain_len, private_key,
                    private_key_len},
      [CRED_ECDSA_P256] = {ec_certificate_chain, ec_certificate_chain_len,
                           ec_private_key, ec_private_key_len},
  };

  printf("Verified TLS 1.3 server: capability matrix (%zu cells)\n", CASE_COUNT);
  printf("%-38s %-6s %-8s %-8s %s\n", "CASE", "CRED", "EXPECT", "ACTUAL",
         "VERDICT");

  size_t mismatches = 0;
  for (size_t i = 0; i < CASE_COUNT; ++i) {
    const struct case_spec *spec = &k_cases[i];
    bool actual =
        run_case(spec, &credentials[spec->credential], "test/certs/ca.pem");
    bool agrees = actual == spec->expect_ok;
    if (!agrees) {
      mismatches += 1;
    }
    printf("%-38s %-6s %-8s %-8s %s\n", spec->name,
           spec->credential == CRED_ECDSA_P256 ? "ecdsa" : "rsa",
           spec->expect_ok ? "ok" : "refused", actual ? "ok" : "refused",
           agrees ? "MATCH" : "*** MISMATCH ***");
    if (!agrees) {
      fprintf(stderr,
              "  %s: expected the server to %s this offer but it %s it.\n"
              "    recorded reason: %s\n",
              spec->name, spec->expect_ok ? "accept" : "refuse",
              actual ? "accepted" : "refused", spec->note);
      if (actual) {
        fprintf(stderr,
                "    A cell recorded as a gap now SUCCEEDS.  If that is the\n"
                "    intended effect of your change, flip this row to OK in\n"
                "    test/unit/test_server_interop_matrix.c and update\n"
                "    docs/server-client-parity.md in the same commit.\n");
      }
    }
  }

  if (mismatches == 0) {
    printf("server capability matrix: all %zu cells match the recorded ledger\n",
           CASE_COUNT);
    rc = 0;
  } else {
    fprintf(stderr, "server capability matrix: %zu of %zu cells disagree with the ledger\n",
            mismatches, CASE_COUNT);
    rc = report_only ? 0 : 1;
  }

done:
  free(certificate_chain);
  free(private_key);
  free(ec_certificate_chain);
  free(ec_private_key);
  return rc;
}
