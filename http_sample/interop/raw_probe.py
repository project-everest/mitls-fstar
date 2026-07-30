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
  timeout  -- a partial request head left open, which must get 408 (read timeout).
  keepalive-- two GETs over one persistent connection, which must both get 200.
  connclose-- a GET with Connection: close, which must get 200 then be closed.
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


def read_one_message(s):
    # Read exactly one HTTP response: the head up to CRLF-CRLF, then Content-Length
    # body bytes, so the socket is left positioned at the start of the next
    # response (needed to read multiple responses over one keep-alive connection).
    buf = b""
    while b"\r\n\r\n" not in buf:
        chunk = s.recv(4096)
        if not chunk:
            return buf
        buf += chunk
    head, rest = buf.split(b"\r\n\r\n", 1)
    clen = 0
    for line in head.split(b"\r\n"):
        if line.lower().startswith(b"content-length:"):
            try:
                clen = int(line.split(b":", 1)[1].strip())
            except ValueError:
                clen = 0
    body = rest
    while len(body) < clen:
        chunk = s.recv(4096)
        if not chunk:
            break
        body += chunk
    return head + b"\r\n\r\n" + body[:clen]


def send_keepalive(host, port, nreq):
    # Send nreq successive GET requests (no Connection: close, so keep-alive) over
    # a SINGLE connection, reading each full response before sending the next
    # (non-pipelined).  Returns the list of status codes observed.
    codes = []
    req = b"GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n"
    with socket.create_connection((host, port), timeout=10) as s:
        s.settimeout(10)
        for _ in range(nreq):
            s.sendall(req)
            resp = read_one_message(s)
            codes.append(status_code(resp))
    return codes


def send_then_check_closed(host, port):
    # Send a single GET with Connection: close, read the response, then check the
    # server closed the connection (recv returns b"").  Returns (code, closed?).
    req = b"GET / HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n"
    with socket.create_connection((host, port), timeout=10) as s:
        s.settimeout(10)
        s.sendall(req)
        resp = read_one_message(s)
        try:
            extra = s.recv(4096)
        except socket.timeout:
            extra = b"?"
        return status_code(resp), (extra == b"")


def send_stall(host, port, partial):
    # Send a PARTIAL request head and deliberately leave the write side open so
    # the head never completes.  Block reading the response with a socket timeout
    # comfortably longer than the server's read timeout, so the server's 408
    # (once its SO_RCVTIMEO fires) is what we observe.
    with socket.create_connection((host, port), timeout=30) as s:
        s.sendall(partial)
        s.settimeout(30)
        buf = b""
        while len(buf) < 4096:
            try:
                chunk = s.recv(4096)
            except socket.timeout:
                break
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
    elif mode == "timeout":
        # A partial request head that is never completed (no CRLF-CRLF) and whose
        # write side is left OPEN: the server's read timeout (SO_RCVTIMEO) must
        # fire and answer 408 Request Timeout rather than hanging forever.
        try:
            resp = send_stall(host, port, b"GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n")
        except OSError as e:
            sys.stderr.write("probe error: %s\n" % e)
            print(-1)
            return 1
        print(status_code(resp))
        return 0
    elif mode == "keepalive":
        # Two GET requests over a SINGLE persistent connection: both must get 200,
        # proving the server kept the connection alive between requests.
        try:
            codes = send_keepalive(host, port, 2)
        except OSError as e:
            sys.stderr.write("probe error: %s\n" % e)
            print(-1)
            return 1
        print(" ".join(str(c) for c in codes))
        return 0
    elif mode == "connclose":
        # A GET with Connection: close: must get 200 AND the server must then close
        # the connection (recv returns EOF).
        try:
            code, closed = send_then_check_closed(host, port)
        except OSError as e:
            sys.stderr.write("probe error: %s\n" % e)
            print(-1)
            return 1
        print("%d %s" % (code, "closed" if closed else "open"))
        return 0
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
