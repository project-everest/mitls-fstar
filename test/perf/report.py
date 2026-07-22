#!/usr/bin/env python3

import csv
import statistics
import sys
from collections import defaultdict
from pathlib import Path


def median(rows, key):
    return statistics.median(float(row[key]) for row in rows)


def main():
    if len(sys.argv) not in {4, 5}:
        raise SystemExit(
            "usage: report.py RESULTS.csv SYSTEM.txt OUTPUT.md [MEMORY.csv]"
        )

    csv_path = Path(sys.argv[1])
    system_path = Path(sys.argv[2])
    output_path = Path(sys.argv[3])
    with csv_path.open(newline="") as source:
        rows = list(csv.DictReader(source))
    if not rows:
        raise SystemExit("benchmark CSV is empty")
    memory_rows = []
    if len(sys.argv) == 5:
        with Path(sys.argv[4]).open(newline="") as source:
            memory_rows = list(csv.DictReader(source))

    groups = defaultdict(list)
    for row in rows:
        groups[(row["case"], int(row["message_size"]))].append(row)

    lines = [
        "# TLS 1.3 benchmark report",
        "",
        "Each result is the median of repeated, sequential loopback runs. "
        "Throughput uses MiB (2^20 bytes). The verified rows exercise the "
        "extracted public C drivers; the baseline uses OpenSSL 3 on both ends.",
        "",
        "## Handshake performance",
        "",
        "| implementation | role | handshakes/s | p50 (ms) | p95 (ms) | "
        "CPU/handshake (ms) | max RSS (MiB) |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    handshake_groups = [
        rows
        for (case_name, size), rows in groups.items()
        if size == 0 and case_name.endswith("-handshake")
    ]
    handshake_groups.sort(
        key=lambda group: (
            group[0]["role"],
            0 if group[0]["implementation"] == "verified" else 1,
        )
    )
    for group in handshake_groups:
        first = group[0]
        operations = int(first["operations"])
        cpu_ms = median(group, "cpu_seconds") * 1000.0 / operations
        lines.append(
            f"| {first['implementation']} | {first['role']} | "
            f"{median(group, 'ops_per_second'):.1f} | "
            f"{median(group, 'p50_us') / 1000.0:.3f} | "
            f"{median(group, 'p95_us') / 1000.0:.3f} | "
            f"{cpu_ms:.3f} | {median(group, 'max_rss_kb') / 1024.0:.2f} |"
        )

    if memory_rows:
        counts = sorted({int(row["operations"]) for row in memory_rows})
        memory_groups = defaultdict(list)
        for row in memory_rows:
            memory_groups[(row["implementation"], row["role"])].append(row)
        lines.extend(
            [
                "",
                "## Handshake memory scaling",
                "",
                "RSS is measured in a fresh process for each count. A positive "
                "per-handshake slope indicates connection lifecycle memory "
                "that is not released back to the process.",
                "",
                "| implementation | role | "
                + " | ".join(f"{count} handshakes (MiB)" for count in counts)
                + " | growth (KiB/handshake) |",
                "|---|---:|"
                + "|".join("---:" for _ in counts)
                + "|---:|",
            ]
        )
        for key in sorted(memory_groups):
            group = memory_groups[key]
            by_count = {
                int(row["operations"]): float(row["max_rss_kb"])
                for row in group
            }
            first_count = counts[0]
            last_count = counts[-1]
            growth = (
                (by_count[last_count] - by_count[first_count])
                / (last_count - first_count)
                if last_count != first_count
                else 0.0
            )
            lines.append(
                f"| {key[0]} | {key[1]} | "
                + " | ".join(f"{by_count[count] / 1024.0:.2f}" for count in counts)
                + f" | {growth:.1f} |"
            )

    lines.extend(
        [
            "",
            "## Application-data throughput",
            "",
            "| size | implementation | role | direction | MiB/s | "
            "vs OpenSSL | K records/s | CPU ns/record |",
            "|---:|---|---:|---:|---:|---:|---:|---:|",
        ]
    )
    transfer_groups = [
        (size, rows)
        for (case_name, size), rows in groups.items()
        if size != 0 and not case_name.endswith("-handshake")
    ]
    transfer_groups.sort(
        key=lambda item: (
            item[0],
            item[1][0]["role"],
            item[1][0]["operation"],
            0 if item[1][0]["implementation"] == "verified" else 1,
        )
    )
    transfer_baselines = {
        (
            size,
            group[0]["role"],
            group[0]["operation"],
        ): median(group, "mib_per_second")
        for size, group in transfer_groups
        if group[0]["implementation"] == "openssl"
    }
    for size, group in transfer_groups:
        first = group[0]
        operations = int(first["operations"])
        cpu_ns = median(group, "cpu_seconds") * 1.0e9 / operations
        throughput = median(group, "mib_per_second")
        baseline = transfer_baselines[
            (size, first["role"], first["operation"])
        ]
        relative = throughput / baseline
        lines.append(
            f"| {size} | {first['implementation']} | {first['role']} | "
            f"{first['operation']} | {throughput:.2f} | {relative:.2f}x | "
            f"{median(group, 'ops_per_second') / 1000.0:.2f} | "
            f"{cpu_ns:.0f} |"
        )

    verified_handshakes = {
        group[0]["role"]: median(group, "ops_per_second")
        for group in handshake_groups
        if group[0]["implementation"] == "verified"
    }
    openssl_handshakes = {
        group[0]["role"]: median(group, "ops_per_second")
        for group in handshake_groups
        if group[0]["implementation"] == "openssl"
    }
    lines.extend(["", "## Relative performance", ""])
    for role in ("client", "server"):
        if role in verified_handshakes and role in openssl_handshakes:
            ratio = verified_handshakes[role] / openssl_handshakes[role]
            difference = (ratio - 1.0) * 100.0
            if abs(difference) < 0.05:
                comparison = "equal within reporting precision"
            elif difference > 0.0:
                comparison = f"{difference:.1f}% faster"
            else:
                comparison = f"{-difference:.1f}% slower"
            lines.append(
                f"- Verified {role} handshake throughput is "
                f"{ratio:.3f}x the OpenSSL/OpenSSL baseline "
                f"({comparison})."
            )

    lines.extend(
        [
            "",
            "## Methodology and scope",
            "",
            "- TLS 1.3 only; `TLS_CHACHA20_POLY1305_SHA256`, X25519, and "
            "`rsa_pss_rsae_sha256`; session tickets and resumption disabled.",
            "- Handshake throughput includes per-connection public API lifecycle "
            "and cleanup. OpenSSL reuses `SSL_CTX`, as production servers and "
            "clients normally do. The current verified server API also creates "
            "and destroys its listener and parses credentials per connection.",
            "- Transfer measurements exclude handshake and shutdown, use one "
            "connection, apply backpressure through a receiving peer, and use "
            "an out-of-band readiness barrier. Received plaintext is validated "
            "after the timed interval.",
            "- Both endpoints run on loopback. These numbers measure software "
            "cost, not WAN latency, packet loss, or congestion behavior.",
            "- RSS is the process high-water mark; CPU and scheduler counters "
            "cover only the measured endpoint, not the forked OpenSSL peer.",
            "- Linear verified-handshake RSS growth is retained process memory, "
            "not merely a larger fixed connection object. The close/free "
            "lifecycle should be audited before concurrency testing.",
            "",
            "## Additional measurements to add",
            "",
            "- Concurrency scaling at 1, 2, 4, 8, 16, and 32 simultaneous "
            "connections, reporting aggregate throughput and tail latency.",
            "- Session resumption and 0-RTT handshakes when implemented, kept "
            "separate from full authenticated handshakes.",
            "- AES-128-GCM alongside ChaCha20-Poly1305, plus ECDSA and Ed25519 "
            "certificates, to separate protocol overhead from algorithm choice.",
            "- Allocation count/bytes per handshake and per record, retained "
            "heap per live connection, and sustained RSS under connection load.",
            "- WAN-shaped runs with RTT, jitter, packet loss, and constrained "
            "bandwidth; loopback results measure software cost only.",
            "- Long-lived connections with key updates, bidirectional traffic, "
            "record fragmentation/coalescing, and multi-gigabyte sequence "
            "number progression.",
            "",
            "## Host",
            "",
            "```text",
            system_path.read_text().strip(),
            "```",
            "",
        ]
    )
    output_path.write_text("\n".join(lines))


if __name__ == "__main__":
    main()
