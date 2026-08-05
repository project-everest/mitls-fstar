#!/usr/bin/env python3

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path


EVENTS = {
    1000: "record.state.new",
    1001: "record.state.free",
    1010: "record.sequence.advance",
    1011: "record.sequence.restore",
    1020: "record.keys.handshake",
    1021: "record.keys.application",
    1030: "record.seal.begin",
    1031: "record.seal.success",
    1032: "record.seal.failure",
    1040: "record.open.begin",
    1041: "record.open.success",
    1042: "record.open.failure",
    2000: "client.new",
    2001: "client.free",
    2010: "client.local.begin",
    2011: "client.local.end",
    2020: "client.network.begin",
    2021: "client.network.need_more",
    2022: "client.network.decode_error",
    2023: "client.network.record",
    2024: "client.network.end",
    2030: "client.protected.head",
    2031: "client.protected.drain",
    2032: "client.protected.empty",
    2033: "client.protected.error",
    2040: "client.handshake.message",
    2100: "engine.new",
    2110: "engine.poll.begin",
    2111: "engine.poll.end",
    2120: "engine.feed.begin",
    2121: "engine.feed.end",
    2130: "engine.certificate.chain",
    2131: "engine.certificate.verified",
    2132: "engine.certificate_signature.verified",
    2140: "engine.application.send",
    2141: "engine.close.send",
    2150: "engine.free",
    3000: "server.new",
    3001: "server.free",
    3010: "server.local.begin",
    3011: "server.local.end",
    3020: "server.network.begin",
    3021: "server.network.need_more",
    3022: "server.network.decode_error",
    3023: "server.network.record",
    3024: "server.network.end",
    3040: "server.handshake.message",
}


def parse_trace(path: Path) -> list[dict]:
    events = []
    with path.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            if '"atlas_trace":1' not in line:
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(f"{path}:{line_number}: {error}") from error
            event["name"] = EVENTS.get(event["event"], f"unknown.{event['event']}")
            events.append(event)
    return events


def main() -> None:
    parser = argparse.ArgumentParser(description="Analyze an ATLAS JSONL trace")
    parser.add_argument("trace", type=Path)
    parser.add_argument("--connection", type=int)
    parser.add_argument("--timeline", action="store_true")
    args = parser.parse_args()

    events = parse_trace(args.trace)
    if args.connection is not None:
        events = [
            event for event in events
            if event["connection"] == args.connection
        ]
    if not events:
        raise SystemExit("No ATLAS trace events matched")

    by_connection = defaultdict(list)
    for event in events:
        by_connection[event["connection"]].append(event)

    print(f"events: {len(events)}")
    print(f"connections: {len(by_connection)}")
    for connection, connection_events in sorted(by_connection.items()):
        counts = Counter(event["name"] for event in connection_events)
        duration = (
            max(event["ts_ns"] for event in connection_events)
            - min(event["ts_ns"] for event in connection_events)
        )
        print(
            f"connection {connection}: {len(connection_events)} events, "
            f"{duration / 1_000_000:.3f} ms"
        )
        for name, count in sorted(counts.items()):
            print(f"  {name}: {count}")

    if args.timeline:
        origin = min(event["ts_ns"] for event in events)
        for event in sorted(events, key=lambda value: (value["ts_ns"], value["seq"])):
            elapsed_ms = (event["ts_ns"] - origin) / 1_000_000
            print(
                f"{elapsed_ms:12.3f}ms "
                f"pid={event['pid']} tid={event['tid']} "
                f"conn={event['connection']} {event['name']} "
                f"a0={event['a0']} a1={event['a1']} a2={event['a2']}"
            )


if __name__ == "__main__":
    main()
