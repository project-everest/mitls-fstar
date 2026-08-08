#!/usr/bin/env python3
"""Emit the single system root CA that anchors a host's certificate chain.

The verified ATLAS driver caps its trust store at 64 KiB, which is smaller than
a full system bundle, so the interop harness is given exactly the one root each
host needs.  This narrows the trust store, not the trust decision: the root is
taken from the platform store, unmodified.
"""
import subprocess
import sys

from cryptography import x509
from cryptography.hazmat.primitives.serialization import Encoding

SYSTEM_BUNDLE = "/etc/ssl/certs/ca-certificates.crt"


def split_pem(data: bytes):
    out, cur, inside = [], [], False
    for line in data.splitlines(keepends=True):
        if line.startswith(b"-----BEGIN CERTIFICATE-----"):
            inside, cur = True, [line]
        elif line.startswith(b"-----END CERTIFICATE-----") and inside:
            cur.append(line)
            out.append(b"".join(cur))
            inside = False
        elif inside:
            cur.append(line)
    return out


# The offer ATLAS actually makes.  A server holding both an RSA and an ECDSA
# credential serves a *different* chain -- anchored at a different root -- for
# each, so the chain must be fetched under the same offer the driver will make.
ATLAS_OFFER = ["-tls1_3", "-groups", "X25519",
               "-ciphersuites", "TLS_CHACHA20_POLY1305_SHA256"]


def fetch_chain(host: str, port: int, extra):
    proc = subprocess.run(
        ["openssl", "s_client", "-connect", f"{host}:{port}",
         "-servername", host, "-showcerts"] + extra,
        input=b"", capture_output=True, timeout=25)
    return split_pem(proc.stdout)


def fetch_chains(host: str, port: int = 443):
    """Every chain the host will serve under an offer ATLAS could make."""
    variants = [
        ATLAS_OFFER + ["-sigalgs", "rsa_pss_rsae_sha256"],
        ATLAS_OFFER + ["-sigalgs", "ecdsa_secp256r1_sha256"],
        ATLAS_OFFER,
        [],
    ]
    seen, chains = set(), []
    for extra in variants:
        try:
            chain = fetch_chain(host, port, extra)
        except subprocess.TimeoutExpired:
            continue
        if not chain:
            continue
        key = chain[-1]
        if key in seen:
            continue
        seen.add(key)
        chains.append(chain)
    return chains


def main() -> int:
    host = sys.argv[1]
    out_path = sys.argv[2]

    chains = fetch_chains(host)
    if not chains:
        print(f"{host}: no chain", file=sys.stderr)
        return 1

    roots = split_pem(open(SYSTEM_BUNDLE, "rb").read())
    by_subject = {}
    for pem in roots:
        try:
            cert = x509.load_pem_x509_certificate(pem)
        except Exception:
            continue
        by_subject.setdefault(cert.subject.rfc4514_string(), pem)

    # The server may or may not send the root itself.  Prefer the issuer of the
    # topmost cert; fall back to the topmost cert when it is already the root.
    # Every chain the host can serve contributes its anchor, so the bundle is
    # correct whichever credential the server ends up selecting.
    # Walk each chain from the top down.  A host may chain up to a legacy root
    # that the platform has since removed (forms.gle cross-signs to the retired
    # "GlobalSign Root CA"); the first cert on the path that the platform still
    # trusts is the correct anchor, and the ATLAS trust store enables
    # X509_V_FLAG_PARTIAL_CHAIN so an intermediate anchor terminates the path.
    picked, names = [], []
    for chain in chains:
        for pem in reversed(chain):
            try:
                cert = x509.load_pem_x509_certificate(pem)
            except Exception:
                continue
            hit = None
            for want in (cert.issuer.rfc4514_string(),
                         cert.subject.rfc4514_string()):
                if want in by_subject:
                    hit = want
                    break
            if hit is None:
                continue
            if by_subject[hit] not in picked:
                picked.append(by_subject[hit])
                names.append(hit)
            break
    if not picked:
        print(f"{host}: root not in system bundle", file=sys.stderr)
        return 1
    with open(out_path, "wb") as handle:
        handle.write(b"".join(picked))
    print("; ".join(names))
    return 0


if __name__ == "__main__":
    sys.exit(main())
