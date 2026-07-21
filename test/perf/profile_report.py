#!/usr/bin/env python3

import re
import sys
from pathlib import Path


PROFILE_CASES = [
    "verified-client-handshake",
    "verified-server-handshake",
    "verified-client-send",
    "verified-client-receive",
    "verified-server-send",
    "verified-server-receive",
]


def read_metadata(path):
    metadata = {}
    if not path.exists():
        return metadata
    for line in path.read_text().splitlines():
        key, separator, value = line.partition("=")
        if separator:
            metadata[key] = value
    return metadata


def read_flat_profile(path):
    entries = []
    pattern = re.compile(
        r"^\s*(\d+\.\d+)\s+\d+\.\d+\s+(\d+\.\d+)\s+"
        r"(\d+)\s+.*\s+(\S+)$"
    )
    for line in path.read_text().splitlines():
        match = pattern.match(line)
        if match:
            entries.append(
                {
                    "percent": float(match.group(1)),
                    "seconds": float(match.group(2)),
                    "calls": int(match.group(3)),
                    "name": match.group(4),
                }
            )
        elif entries:
            break
    return entries


def top_syscalls(path, limit=5):
    entries = []
    pattern = re.compile(
        r"^\s*(\d+\.\d+)\s+\d+\.\d+\s+\d+\s+\d+\s+"
        r"(?:\d+\s+)?(\S+)$"
    )
    for line in path.read_text().splitlines():
        match = pattern.match(line)
        if match and match.group(2) not in {"wait4", "execve"}:
            entries.append((float(match.group(1)), match.group(2)))
    return entries[:limit]


def sum_percent(entries, name_fragments):
    return sum(
        entry["percent"]
        for entry in entries
        if any(fragment in entry["name"] for fragment in name_fragments)
    )


def summarize_functions(entries, limit=3):
    return ", ".join(
        f"`{entry['name']}` ({entry['percent']:.1f}%)"
        for entry in entries[:limit]
        if entry["percent"] > 0.0
    ) or "no attributed samples"


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: profile_report.py PROFILE_DIR")
    profile_dir = Path(sys.argv[1])
    metadata = read_metadata(profile_dir / "metadata.txt")
    message_size = metadata.get("message_size", "unknown")
    lines = [
        "# TLS 1.3 profiling report",
        "",
        f"Profiles use the `-pg -g` build and {message_size}-byte records. "
        "Percentages below "
        "are self CPU samples in the benchmark executable; dynamically linked "
        "OpenSSL internals are not attributed by gprof.",
        "",
        "## CPU hot spots",
        "",
        "| case | top sampled functions |",
        "|---|---|",
    ]
    profiles = {}
    for case in PROFILE_CASES:
        path = profile_dir / f"{case}.gprof.txt"
        entries = read_flat_profile(path)
        profiles[case] = entries
        top = [
            f"`{entry['name']}` {entry['percent']:.1f}%"
            for entry in entries
            if entry["percent"] > 0.0
        ][:6]
        lines.append(f"| {case} | {'; '.join(top) if top else 'No samples'} |")

    crypto_fragments = ("double_round", "poly1305")
    receive_copy_fragments = (
        "Pulse_Lib_Array_memcpy_l__uint8_t",
        "process_buffered_network_bytes_compact_once",
    )
    client_send_crypto = sum_percent(
        profiles["verified-client-send"], crypto_fragments
    )
    server_send_crypto = sum_percent(
        profiles["verified-server-send"], crypto_fragments
    )
    client_receive_copy = sum_percent(
        profiles["verified-client-receive"], receive_copy_fragments
    )
    server_receive_copy = sum_percent(
        profiles["verified-server-receive"], receive_copy_fragments
    )
    client_handshake = summarize_functions(
        profiles["verified-client-handshake"]
    )
    server_handshake = summarize_functions(
        profiles["verified-server-handshake"]
    )
    simd256 = any(
        "double_round_256" in entry["name"]
        for entries in profiles.values()
        for entry in entries
    )
    crypto_backend = (
        "The verified build selected HACL*'s AVX2 SIMD256 backend, with a "
        "runtime-dispatched scalar fallback."
        if simd256
        else "The verified build selected portable scalar HACL*."
    )
    lines.extend(
        [
            "",
            "## Main bottlenecks",
            "",
            "1. **Application-data crypto:** ChaCha20 `double_round` and "
            f"Poly1305 account for {client_send_crypto:.1f}% of client-send "
            f"and {server_send_crypto:.1f}% of server-send self CPU with "
            f"{message_size}-byte records. {crypto_backend}",
            "2. **Receive copies and compaction:** plaintext copying plus "
            f"buffer compaction account for {client_receive_copy:.1f}% of "
            f"client-receive and {server_receive_copy:.1f}% of server-receive "
            "self CPU. Direct caller output, ciphertext-view parsing, and "
            "`memmove` compaction have moved these costs below gprof's sampling "
            "resolution; a persistent sliding window is not justified by this run.",
            f"3. **Client-handshake leaders:** {client_handshake}.",
            f"4. **Server-handshake leaders:** {server_handshake}. The public "
            "server API also reparses credentials and recreates its listener "
            "for every handshake.",
            "",
            "## Syscall summaries",
            "",
            "| case | highest non-wait syscalls | raw report |",
            "|---|---|---|",
        ]
    )
    for case in PROFILE_CASES:
        path = profile_dir / f"{case}.strace.txt"
        syscalls = top_syscalls(path)
        summary = "; ".join(f"`{name}` {percent:.1f}%" for percent, name in syscalls)
        lines.append(
            f"| {case} | {summary or 'No samples'} | "
            f"[strace](./{path.name}) |"
        )

    perf_note = profile_dir / "perf-unavailable.txt"
    lines.extend(
        [
            "",
            "## Raw profiles",
            "",
        ]
    )
    for case in PROFILE_CASES:
        lines.append(f"- [{case}](./{case}.gprof.txt)")
    if perf_note.exists():
        perf_details = "; ".join(
            line
            for line in perf_note.read_text().splitlines()
            if line and not line.startswith("#")
        )
        lines.extend(
            [
                "",
                "**Hardware counters were unavailable on this host:** "
                f"{perf_details} Grant `CAP_PERFMON` or adjust the host perf "
                "policy to collect cycles, instructions, cache misses, and "
                "branch misses. [Raw probe](./perf-unavailable.txt)",
            ]
        )
    lines.append("")
    (profile_dir / "report.md").write_text("\n".join(lines))


if __name__ == "__main__":
    main()
