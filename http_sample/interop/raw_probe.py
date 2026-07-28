#!/usr/bin/env python3
"""Raw HTTP request probe for the request-smuggling interop test.

curl cannot craft a request that carries BOTH Content-Length and
Transfer-Encoding, so this sends a raw request over a socket and prints the
numeric status code from the response status line ("HTTP/1.1 <code> ...").

Usage:  raw_probe.py <host> <port> <smuggle|clean|badreq|notimpl|toolarge|lenreq|toobig|chunked|badchunk>

  smuggle  -- a CL.TE vector (both Content-Length and Transfer-Encoding present),
              which the server's verified framing guard must reject with 400.
  clean    -- a well-formed single-Content-Length request, which must get 200.
  badreq   -- a malformed request line, which must get 400.
  notimpl  -- a valid line with an unsupported method, which must get 501.
  toolarge -- a request with an over-long header line, which must get 431.
  lenreq   -- a POST with no Content-Length/Transfer-Encoding, which must get 411.
  toobig   -- a POST whose Content-Length exceeds the body cap, which must get 413.
  chunked  -- a well-formed chunked upload, which must get 200.
  badchunk -- a chunked upload with a non-hex chunk size, which must get 400.
"""
import socket
import sys


def send(host, port, payload):
    with socket.create_connection((host, port), timeout=5) as s:
        s.sendall(payload)
        s.shutdown(socket.SHUT_WR)
        buf = b""
        while len(buf) < 4096:
            chunk = s.recv(4096)
            if not chunk:
                break
            buf += chunk
    return buf


def status_code(resp):
    # Status line: "HTTP/1.1 <code> ..."
    line = resp.split(b"\r\n", 1)[0]
    parts = line.split(b" ")
    if len(parts) >= 2 and parts[1].isdigit():
        return int(parts[1])
    return -1


def main():
    host, port, mode = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    if mode == "smuggle":
        payload = (
            b"POST /submit HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            b"Content-Length: 5\r\n"
            b"Transfer-Encoding: chunked\r\n"
            b"\r\n"
            b"0\r\n\r\n"
        )
    elif mode == "clean":
        payload = (
            b"POST /submit HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            b"Content-Length: 5\r\n"
            b"\r\n"
            b"hello"
        )
    elif mode == "badreq":
        # Malformed request line (no spaces / no HTTP-version) -> 400.
        payload = b"GET/HTTP\r\nHost: 127.0.0.1\r\n\r\n"
    elif mode == "notimpl":
        # Syntactically valid line, unsupported method -> 501.
        payload = (
            b"FROBNICATE / HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            b"\r\n"
        )
    elif mode == "toolarge":
        # A single header line far exceeding the server's per-line cap -> 431.
        big = b"X-Big: " + (b"a" * 9000) + b"\r\n"
        payload = (
            b"GET / HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            + big +
            b"\r\n"
        )
    elif mode == "lenreq":
        # POST with neither Content-Length nor Transfer-Encoding -> 411.
        payload = (
            b"POST /submit HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            b"\r\n"
        )
    elif mode == "toobig":
        # POST whose Content-Length exceeds the server body cap -> 413.
        # (No body is sent; the server rejects from the head before reading.)
        payload = (
            b"POST /submit HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            b"Content-Length: 2000000\r\n"
            b"\r\n"
        )
    elif mode == "chunked":
        # A well-formed chunked upload -> 200, body decoded to "hello world".
        payload = (
            b"POST /submit HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            b"Transfer-Encoding: chunked\r\n"
            b"\r\n"
            b"6\r\nhello \r\n5\r\nworld\r\n0\r\n\r\n"
        )
    elif mode == "badchunk":
        # A chunked upload whose chunk-size line is not hex -> 400.
        payload = (
            b"POST /submit HTTP/1.1\r\n"
            b"Host: 127.0.0.1\r\n"
            b"Transfer-Encoding: chunked\r\n"
            b"\r\n"
            b"zz\r\nhello\r\n0\r\n\r\n"
        )
    else:
        print(-1)
        return 2

    try:
        resp = send(host, port, payload)
    except OSError as e:
        sys.stderr.write("probe error: %s\n" % e)
        print(-1)
        return 1

    print(status_code(resp))
    return 0


if __name__ == "__main__":
    sys.exit(main())
