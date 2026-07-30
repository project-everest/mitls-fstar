# ═══════════════════════════════════════════════════════════════════
# HTTP/1.1 interop test: a real `curl` client against our verified server
# ═══════════════════════════════════════════════════════════════════
# `http_server` is an origin server whose request PARSE and RESPONSE are BOTH
# produced by VERIFIED, extracted Pulse code: each exchange runs through
# `http_server_exchange_length_head` in ../_extract/HTTP_Verified.c, which parses
# the client's request head with the verified headers-tolerant leaf
# `http_recv_request_head` (recovering the request target, ignoring headers) and
# then writes the Content-Length response head + body.  The bind/accept loop and
# the socket read of the request head are thin UNVERIFIED glue (http_server.c) —
# a real client (curl) sends headers and a request of unknown length, so reading
# it off the socket is glue, but the buffered bytes are then parsed IN-MODEL by
# the verified leaf, and the response is verified byte-exact.
#
# `make test` starts http_server on a loopback port, issues a real `curl`
# request, and PASSES only if curl reports HTTP 200 AND the body it received is
# byte-identical to the body the server was told to serve.  `curl` must be on
# PATH; a run that cannot find it reports SKIP.

PARENT       := ..
EXTRACT_DIR  := $(PARENT)/_extract
STUBS_DIR    := $(PARENT)/../c_stubs
VERIFIED_DIR := $(PARENT)/verified
EVERPARSE_HOME ?= $(abspath $(PARENT)/../tools/everparse)
KRML_HOME   ?= $(firstword $(wildcard $(EVERPARSE_HOME)/opt/karamel $(EVERPARSE_HOME)/opt/FStar/karamel) $(EVERPARSE_HOME)/opt/karamel)
KRML_INCLUDE = $(KRML_HOME)/include
KRML_RUNTIME = $(KRML_HOME)/krmllib/dist/minimal

SRV_OUR := $(abspath $(EXTRACT_DIR)/http_server)

PORT    ?= 8080
TIMEOUT ?= 30
CC      ?= gcc
CFLAGS_INTEROP = -std=c11 -D_DEFAULT_SOURCE -DCOMMON_TCP_KARAMEL_FULL_DECLS \
  -include $(STUBS_DIR)/common_tcp_karamel.h -Wall -Wno-unused-function \
  -Wno-unused-parameter -Wno-implicit-function-declaration \
  -I$(KRML_INCLUDE) -I$(KRML_INCLUDE)/krml -I$(KRML_RUNTIME) -I$(EXTRACT_DIR) -I$(STUBS_DIR)

RUN_DIR := _run_http
RUN_DIR_ABS := $(abspath $(RUN_DIR))
RUN_DIR_POST := _run_http_post
RUN_DIR_POST_ABS := $(abspath $(RUN_DIR_POST))
PORT_POST ?= $(shell echo $$(( $(PORT) + 1 )))
RUN_DIR_SMUG := _run_http_smug
RUN_DIR_SMUG_ABS := $(abspath $(RUN_DIR_SMUG))
PORT_SMUG ?= $(shell echo $$(( $(PORT) + 2 )))
RUN_DIR_METH := _run_http_meth
RUN_DIR_METH_ABS := $(abspath $(RUN_DIR_METH))
PORT_METH ?= $(shell echo $$(( $(PORT) + 3 )))
RUN_DIR_LIM := _run_http_lim
RUN_DIR_LIM_ABS := $(abspath $(RUN_DIR_LIM))
PORT_LIM ?= $(shell echo $$(( $(PORT) + 4 )))
RUN_DIR_ERR := _run_http_err
RUN_DIR_ERR_ABS := $(abspath $(RUN_DIR_ERR))
PORT_ERR ?= $(shell echo $$(( $(PORT) + 5 )))
RUN_DIR_CHK := _run_http_chk
RUN_DIR_CHK_ABS := $(abspath $(RUN_DIR_CHK))
PORT_CHK ?= $(shell echo $$(( $(PORT) + 6 )))
RUN_DIR_TMO := _run_http_tmo
RUN_DIR_TMO_ABS := $(abspath $(RUN_DIR_TMO))
PORT_TMO ?= $(shell echo $$(( $(PORT) + 7 )))
RUN_DIR_KA := _run_http_ka
RUN_DIR_KA_ABS := $(abspath $(RUN_DIR_KA))
PORT_KA ?= $(shell echo $$(( $(PORT) + 8 )))
RUN_DIR_TLS := _run_http_tls
RUN_DIR_TLS_ABS := $(abspath $(RUN_DIR_TLS))
PORT_TLS ?= $(shell echo $$(( $(PORT) + 9 )))

.PHONY: all test test-get test-post test-smuggle test-method test-limits test-errors test-chunked test-timeout test-keepalive test-tls build-progs clean help

all: test

# Build the extracted verified bundle (via the parent) then our server program.
build-progs:
	@$(MAKE) --no-print-directory -C $(PARENT) extract-loops
	@echo "Compiling the HTTP server over the VERIFIED response driver..."
	$(CC) $(CFLAGS_INTEROP) -o $(EXTRACT_DIR)/http_server \
	  http_server.c \
	  $(EXTRACT_DIR)/HTTP_Verified.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c \
	  -lssl -lcrypto
	@echo "Server http_server (verified response) compiled to $(EXTRACT_DIR)/."

# ── curl <-> our verified-response server ─────────────────────────────────────
test: test-get test-post test-smuggle test-method test-limits test-errors test-chunked test-timeout test-keepalive test-tls

test-get: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " HTTP interop test:  curl (client)  ->  http_server (verified parse + response)"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v curl >/dev/null 2>&1 || { echo "  SKIP: 'curl' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR); mkdir -p $(RUN_DIR)
	@printf 'verified-http-body payload %s\n' "$$(date +%s)" > $(RUN_DIR)/body.txt
	@echo "  serving body.txt ($$(wc -c < $(RUN_DIR)/body.txt) bytes) with our verified-response server; fetching with curl ..."
	@cd $(RUN_DIR) && \
	  HTTP_PARSE_STATUS_FILE=parse.status \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT) body.txt & srv=$$!; sleep 0.5; \
	    code=$$(curl -s -o recv.txt -w "%{http_code}" --max-time 5 http://127.0.0.1:$(PORT)/); rc=$$?; \
	    echo "curl exit=$$rc http_code=$$code" > curl.log; \
	    for i in $$(seq 1 40); do [ -s parse.status ] && break; sleep 0.05; done; \
	    exit $$rc' \
	    > run.log 2>&1; \
	  st=$$?; \
	  code=$$(sed -n "s/.*http_code=//p" curl.log 2>/dev/null); \
	  if cmp -s recv.txt body.txt; then content=match; else content=differ; fi; \
	  status=$$(cat parse.status 2>/dev/null); \
	  if [ "$$status" = "ok 1" ]; then parsed=ok; else parsed=no; fi; \
	  if [ $$st -eq 0 ] && [ "$$code" = 200 ] && [ "$$content" = match ] && [ "$$parsed" = ok ]; then \
	    echo "  RESULT: PASS - curl got HTTP $$code + byte-identical body, and the VERIFIED parser accepted curl's real request head (parse.status='$$status', target '/' = 1 byte)"; \
	    rm -rf $(RUN_DIR_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/curl did not terminate: killed after $(TIMEOUT)s (code=$$code content=$$content parsed=$$parsed status='$$status')"; \
	    else echo "  RESULT: FAIL - exit=$$st http_code=$$code content=$$content parsed=$$parsed status='$$status'"; fi; \
	    echo "  --- curl.log ---"; cat curl.log 2>/dev/null; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── curl POST (real request body) <-> our verified-response server ────────────
# The server DETECTS the method with the verified request-line parser
# (http_method_eq), recovers Content-Length with the verified header decoder
# (http_header_dec), reads the body, and ECHOES it back in a verified 200
# response.  PASS iff curl gets HTTP 200, the echoed body is byte-identical to
# what we POSTed, and parse.status shows the verified path handled a POST.
test-post: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " HTTP POST interop:  curl -d (client)  ->  http_server (verified method+CL parse, body echo)"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v curl >/dev/null 2>&1 || { echo "  SKIP: 'curl' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_POST); mkdir -p $(RUN_DIR_POST)
	@printf 'verified-http POST payload %s: the quick brown fox jumps over the lazy dog\n' "$$(date +%s)" > $(RUN_DIR_POST)/payload.txt
	@echo "  POSTing payload.txt ($$(wc -c < $(RUN_DIR_POST)/payload.txt) bytes); server echoes it back ..."
	@cd $(RUN_DIR_POST) && \
	  HTTP_PARSE_STATUS_FILE=parse.status \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_POST) & srv=$$!; sleep 0.5; \
	    code=$$(curl -s -o recv.txt -w "%{http_code}" --max-time 5 --data-binary @payload.txt http://127.0.0.1:$(PORT_POST)/submit); rc=$$?; \
	    echo "curl exit=$$rc http_code=$$code" > curl.log; \
	    for i in $$(seq 1 40); do [ -s parse.status ] && break; sleep 0.05; done; \
	    exit $$rc' \
	    > run.log 2>&1; \
	  st=$$?; \
	  code=$$(sed -n "s/.*http_code=//p" curl.log 2>/dev/null); \
	  if cmp -s recv.txt payload.txt; then content=match; else content=differ; fi; \
	  status=$$(cat parse.status 2>/dev/null); \
	  case "$$status" in post\ *) parsed=ok;; *) parsed=no;; esac; \
	  if [ $$st -eq 0 ] && [ "$$code" = 200 ] && [ "$$content" = match ] && [ "$$parsed" = ok ]; then \
	    echo "  RESULT: PASS - curl POST got HTTP $$code + byte-identical echoed body, and the VERIFIED method+Content-Length parser handled it (parse.status='$$status')"; \
	    rm -rf $(RUN_DIR_POST_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/curl did not terminate: killed after $(TIMEOUT)s (code=$$code content=$$content parsed=$$parsed status='$$status')"; \
	    else echo "  RESULT: FAIL - exit=$$st http_code=$$code content=$$content parsed=$$parsed status='$$status'"; fi; \
	    echo "  --- curl.log ---"; cat curl.log 2>/dev/null; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_POST_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── raw request-smuggling probe <-> our verified-framing guard ────────────────
# curl cannot craft a request that carries BOTH Content-Length and
# Transfer-Encoding (a classic CL.TE smuggling vector), so we send a RAW request
# over a python3 socket.  The server's VERIFIED http_request_framing_ok rejects
# it and answers a verified 400.  PASS iff the response status line is
# "HTTP/1.1 400" and parse.status shows the smuggling path fired.  As a control,
# we ALSO send a clean single-Content-Length request and require HTTP 200.
test-smuggle: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " Smuggling guard:  raw CL+TE request  ->  http_server (verified framing check -> 400)"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v python3 >/dev/null 2>&1 || { echo "  SKIP: 'python3' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_SMUG); mkdir -p $(RUN_DIR_SMUG)
	@cp raw_probe.py $(RUN_DIR_SMUG)/raw_probe.py
	@echo "  sending a raw Content-Length + Transfer-Encoding request; expecting a verified 400 ..."
	@cd $(RUN_DIR_SMUG) && \
	  HTTP_PARSE_STATUS_FILE=parse.status \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_SMUG) & srv=$$!; sleep 0.5; \
	    python3 raw_probe.py 127.0.0.1 $(PORT_SMUG) smuggle > smug.code 2>err.log; rc=$$?; \
	    for i in $$(seq 1 40); do [ -s parse.status ] && break; sleep 0.05; done; \
	    cp parse.status smug.status 2>/dev/null; \
	    python3 raw_probe.py 127.0.0.1 $(PORT_SMUG) clean > clean.code 2>>err.log; \
	    exit $$rc' \
	    > run.log 2>&1; \
	  st=$$?; \
	  scode=$$(cat smug.code 2>/dev/null); ccode=$$(cat clean.code 2>/dev/null); \
	  status=$$(cat smug.status 2>/dev/null); \
	  case "$$status" in smuggling\ *) parsed=ok;; *) parsed=no;; esac; \
	  if [ "$$scode" = 400 ] && [ "$$ccode" = 200 ] && [ "$$parsed" = ok ]; then \
	    echo "  RESULT: PASS - the VERIFIED framing guard rejected the CL+TE request with HTTP 400 (parse.status='$$status'), and a clean single-CL request still got HTTP 200"; \
	    rm -rf $(RUN_DIR_SMUG_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/probe did not terminate: killed after $(TIMEOUT)s (smuggle=$$scode clean=$$ccode parsed=$$parsed status='$$status')"; \
	    else echo "  RESULT: FAIL - smuggle=$$scode (want 400) clean=$$ccode (want 200) parsed=$$parsed status='$$status'"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_SMUG_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── request-line / method guard  ->  400 Bad Request + 501 Not Implemented ────
# The server runs the VERIFIED http_request_line_ok / http_method_known
# validators before handling: a malformed request line gets a verified 400, and
# a syntactically valid but unsupported method gets a verified 501.  We probe an
# unsupported method with a real `curl -X FROBNICATE` (expecting 501) and a
# malformed request line with a raw socket (expecting 400), and re-check that a
# normal GET still gets 200 as a control.
test-method: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " Method/line guard:  curl -X FROBNICATE -> 501, raw bad line -> 400"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v curl >/dev/null 2>&1 || { echo "  SKIP: 'curl' not found on PATH"; exit 3; }
	@command -v python3 >/dev/null 2>&1 || { echo "  SKIP: 'python3' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_METH); mkdir -p $(RUN_DIR_METH)
	@cp raw_probe.py $(RUN_DIR_METH)/raw_probe.py
	@echo "  probing an unsupported method (501) and a malformed request line (400) ..."
	@cd $(RUN_DIR_METH) && \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_METH) & srv=$$!; sleep 0.5; \
	    ncode=$$(curl -s -o /dev/null -w "%{http_code}" --max-time 5 -X FROBNICATE http://127.0.0.1:$(PORT_METH)/); echo $$ncode > notimpl.code; \
	    bcode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_METH) badreq 2>err.log); echo $$bcode > badreq.code; \
	    gcode=$$(curl -s -o /dev/null -w "%{http_code}" --max-time 5 http://127.0.0.1:$(PORT_METH)/); echo $$gcode > get.code; \
	    exit 0' \
	    > run.log 2>&1; \
	  st=$$?; \
	  ncode=$$(cat notimpl.code 2>/dev/null); bcode=$$(cat badreq.code 2>/dev/null); gcode=$$(cat get.code 2>/dev/null); \
	  if [ "$$ncode" = 501 ] && [ "$$bcode" = 400 ] && [ "$$gcode" = 200 ]; then \
	    echo "  RESULT: PASS - the VERIFIED validators answered 501 to an unsupported method and 400 to a malformed request line, while a normal GET still got 200"; \
	    rm -rf $(RUN_DIR_METH_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/probe did not terminate: killed after $(TIMEOUT)s (notimpl=$$ncode badreq=$$bcode get=$$gcode)"; \
	    else echo "  RESULT: FAIL - notimpl=$$ncode (want 501) badreq=$$bcode (want 400) get=$$gcode (want 200)"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_METH_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── header-block limits  ->  431 Request Header Fields Too Large ──────────────
# The server runs the VERIFIED http_header_limits_ok enforcer before handling.
# We send a raw request with an over-long header line (expecting 431) and
# re-check a normal GET (expecting 200) as a control.
test-limits: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " Header limits:  raw over-long header line  ->  431, GET -> 200"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v curl >/dev/null 2>&1 || { echo "  SKIP: 'curl' not found on PATH"; exit 3; }
	@command -v python3 >/dev/null 2>&1 || { echo "  SKIP: 'python3' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_LIM); mkdir -p $(RUN_DIR_LIM)
	@cp raw_probe.py $(RUN_DIR_LIM)/raw_probe.py
	@echo "  probing an over-long header line (431) ..."
	@cd $(RUN_DIR_LIM) && \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_LIM) & srv=$$!; sleep 0.5; \
	    lcode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_LIM) toolarge 2>err.log); echo $$lcode > toolarge.code; \
	    gcode=$$(curl -s -o /dev/null -w "%{http_code}" --max-time 5 http://127.0.0.1:$(PORT_LIM)/); echo $$gcode > get.code; \
	    exit 0' \
	    > run.log 2>&1; \
	  st=$$?; \
	  lcode=$$(cat toolarge.code 2>/dev/null); gcode=$$(cat get.code 2>/dev/null); \
	  if [ "$$lcode" = 431 ] && [ "$$gcode" = 200 ]; then \
	    echo "  RESULT: PASS - the VERIFIED limit enforcer answered 431 to an over-long header line, while a normal GET still got 200"; \
	    rm -rf $(RUN_DIR_LIM_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/probe did not terminate: killed after $(TIMEOUT)s (toolarge=$$lcode get=$$gcode)"; \
	    else echo "  RESULT: FAIL - toolarge=$$lcode (want 431) get=$$gcode (want 200)"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_LIM_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── method/body error responses  ->  405 + 411 + 413 ─────────────────────────
# 405 Method Not Allowed (recognized but unsupported method, via VERIFIED
# http_method_allowed), 411 Length Required (POST without Content-Length/
# Transfer-Encoding), 413 Payload Too Large (Content-Length beyond the cap).
# curl -X DELETE probes 405; raw sockets probe 411/413; a normal GET is the
# 200 control.
test-errors: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " Error responses:  DELETE -> 405, no-length POST -> 411, huge POST -> 413"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v curl >/dev/null 2>&1 || { echo "  SKIP: 'curl' not found on PATH"; exit 3; }
	@command -v python3 >/dev/null 2>&1 || { echo "  SKIP: 'python3' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_ERR); mkdir -p $(RUN_DIR_ERR)
	@cp raw_probe.py $(RUN_DIR_ERR)/raw_probe.py
	@echo "  probing 405 (DELETE), 411 (no-length POST), 413 (oversized POST) ..."
	@cd $(RUN_DIR_ERR) && \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_ERR) & srv=$$!; sleep 0.5; \
	    acode=$$(curl -s -o /dev/null -w "%{http_code}" --max-time 5 -X DELETE http://127.0.0.1:$(PORT_ERR)/); echo $$acode > notallowed.code; \
	    lcode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_ERR) lenreq 2>>err.log); echo $$lcode > lenreq.code; \
	    tcode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_ERR) toobig 2>>err.log); echo $$tcode > toobig.code; \
	    gcode=$$(curl -s -o /dev/null -w "%{http_code}" --max-time 5 http://127.0.0.1:$(PORT_ERR)/); echo $$gcode > get.code; \
	    exit 0' \
	    > run.log 2>&1; \
	  st=$$?; \
	  acode=$$(cat notallowed.code 2>/dev/null); lcode=$$(cat lenreq.code 2>/dev/null); \
	  tcode=$$(cat toobig.code 2>/dev/null); gcode=$$(cat get.code 2>/dev/null); \
	  if [ "$$acode" = 405 ] && [ "$$lcode" = 411 ] && [ "$$tcode" = 413 ] && [ "$$gcode" = 200 ]; then \
	    echo "  RESULT: PASS - the VERIFIED validators answered 405 (DELETE), 411 (no-length POST) and 413 (oversized POST), while a normal GET still got 200"; \
	    rm -rf $(RUN_DIR_ERR_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/probe did not terminate: killed after $(TIMEOUT)s (405=$$acode 411=$$lcode 413=$$tcode get=$$gcode)"; \
	    else echo "  RESULT: FAIL - 405=$$acode (want 405) 411=$$lcode (want 411) 413=$$tcode (want 413) get=$$gcode (want 200)"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_ERR_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── chunked upload  ->  verified decode (200) + malformed-chunk rejection (400) ─
# A POST with Transfer-Encoding: chunked is decoded by the VERIFIED
# http_decode_chunks_var; a well-formed body is echoed back (200) and a body with
# a non-hex chunk size is rejected (400).  Both probes half-close so the server
# can slurp the chunked body to EOF.
test-chunked: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " Chunked upload:  well-formed -> 200 (decoded), bad chunk size -> 400"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v python3 >/dev/null 2>&1 || { echo "  SKIP: 'python3' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_CHK); mkdir -p $(RUN_DIR_CHK)
	@cp raw_probe.py $(RUN_DIR_CHK)/raw_probe.py
	@echo "  probing a well-formed chunked upload (200, 11-byte decode) and a malformed one (400) ..."
	@cd $(RUN_DIR_CHK) && \
	  HTTP_PARSE_STATUS_FILE=parse.status \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_CHK) & srv=$$!; sleep 0.5; \
	    ccode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_CHK) chunked 2>err.log); echo $$ccode > chunked.code; \
	    for i in $$(seq 1 40); do [ -s parse.status ] && break; sleep 0.05; done; \
	    cp parse.status chunked.status 2>/dev/null; \
	    bcode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_CHK) badchunk 2>>err.log); echo $$bcode > badchunk.code; \
	    exit 0' \
	    > run.log 2>&1; \
	  st=$$?; \
	  ccode=$$(cat chunked.code 2>/dev/null); bcode=$$(cat badchunk.code 2>/dev/null); \
	  cstat=$$(cat chunked.status 2>/dev/null); \
	  if [ "$$ccode" = 200 ] && [ "$$bcode" = 400 ] && [ "$$cstat" = "chunked 11" ]; then \
	    echo "  RESULT: PASS - the VERIFIED chunk decoder accepted a well-formed chunked upload (200, decoded 11 bytes) and rejected a malformed chunk size with 400"; \
	    rm -rf $(RUN_DIR_CHK_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/probe did not terminate: killed after $(TIMEOUT)s (chunked=$$ccode badchunk=$$bcode status='$$cstat')"; \
	    else echo "  RESULT: FAIL - chunked=$$ccode (want 200) badchunk=$$bcode (want 400) status='$$cstat' (want 'chunked 11')"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_CHK_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── read timeout  ->  verified 408 on a stalled client ────────────────────────
# A client that opens a connection and sends only a PARTIAL request head (never
# the terminating CRLF-CRLF) and leaves its write side open must be dropped with
# a verified 408 Request Timeout once the server's SO_RCVTIMEO fires, rather than
# holding the single-threaded accept loop open (slow-loris defense).  The server
# runs with HTTP_READ_TIMEOUT=1 here so the test is quick.
test-timeout: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " Read timeout:  stalled partial request -> 408, normal GET -> 200"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v python3 >/dev/null 2>&1 || { echo "  SKIP: 'python3' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_TMO); mkdir -p $(RUN_DIR_TMO)
	@cp raw_probe.py $(RUN_DIR_TMO)/raw_probe.py
	@echo "  probing a stalled partial-head client (408) and a normal GET (200) ..."
	@cd $(RUN_DIR_TMO) && \
	  HTTP_PARSE_STATUS_FILE=parse.status HTTP_READ_TIMEOUT=1 \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_TMO) & srv=$$!; sleep 0.5; \
	    tcode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_TMO) timeout 2>err.log); echo $$tcode > timeout.code; \
	    for i in $$(seq 1 40); do [ -s parse.status ] && break; sleep 0.05; done; \
	    cp parse.status timeout.status 2>/dev/null; \
	    gcode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_TMO) clean 2>>err.log); echo $$gcode > clean.code; \
	    exit 0' \
	    > run.log 2>&1; \
	  st=$$?; \
	  tcode=$$(cat timeout.code 2>/dev/null); gcode=$$(cat clean.code 2>/dev/null); \
	  tstat=$$(cat timeout.status 2>/dev/null); \
	  if [ "$$tcode" = 408 ] && [ "$$gcode" = 200 ] && [ "$$tstat" = "timeout 408" ]; then \
	    echo "  RESULT: PASS - the server's read timeout answered 408 to a stalled partial-head client, while a normal request still got 200"; \
	    rm -rf $(RUN_DIR_TMO_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/probe did not terminate: killed after $(TIMEOUT)s (timeout=$$tcode clean=$$gcode status='$$tstat')"; \
	    else echo "  RESULT: FAIL - timeout=$$tcode (want 408) clean=$$gcode (want 200) status='$$tstat' (want 'timeout 408')"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_TMO_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── keep-alive  ->  persistent connection + verified Connection: close ─────────
# Two GET requests over a SINGLE TCP connection must BOTH get 200 (the server
# kept the connection alive between them), and a request carrying the verified
# `Connection: close` directive must get 200 and then have its connection closed.
test-keepalive: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " Keep-alive:  2 GETs on one connection -> 200 200, Connection: close -> 200 closed"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v python3 >/dev/null 2>&1 || { echo "  SKIP: 'python3' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_KA); mkdir -p $(RUN_DIR_KA)
	@cp raw_probe.py $(RUN_DIR_KA)/raw_probe.py
	@echo "  probing two GETs on one persistent connection, then a Connection: close request ..."
	@cd $(RUN_DIR_KA) && \
	  HTTP_PARSE_STATUS_FILE=parse.status \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_KA) & srv=$$!; sleep 0.5; \
	    kacode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_KA) keepalive 2>err.log); echo "$$kacode" > ka.code; \
	    cccode=$$(python3 raw_probe.py 127.0.0.1 $(PORT_KA) connclose 2>>err.log); echo "$$cccode" > cc.code; \
	    exit 0' \
	    > run.log 2>&1; \
	  st=$$?; \
	  kacode=$$(cat ka.code 2>/dev/null); cccode=$$(cat cc.code 2>/dev/null); \
	  if [ "$$kacode" = "200 200" ] && [ "$$cccode" = "200 closed" ]; then \
	    echo "  RESULT: PASS - the server served two requests over one persistent connection (200 200) and honored the VERIFIED Connection: close directive (200, then closed)"; \
	    rm -rf $(RUN_DIR_KA_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/probe did not terminate: killed after $(TIMEOUT)s (keepalive='$$kacode' connclose='$$cccode')"; \
	    else echo "  RESULT: FAIL - keepalive='$$kacode' (want '200 200') connclose='$$cccode' (want '200 closed')"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_KA_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── TLS termination  ->  verified HTTP over HTTPS ─────────────────────────────
# The verified HTTP leaves run UNCHANGED over a TLS-encrypted transport: with a
# certificate configured, the server speaks HTTPS.  A self-signed cert is minted
# for the test; curl -k does a GET (200 + fixed body) and a POST (200 + echoed
# body) over TLS, and the verified parser status is asserted from parse.status.
test-tls: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " TLS:  verified HTTP served over HTTPS -> GET 200 + body, POST 200 + echo"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v curl >/dev/null 2>&1 || { echo "  SKIP: 'curl' not found on PATH"; exit 3; }
	@command -v openssl >/dev/null 2>&1 || { echo "  SKIP: 'openssl' not found on PATH"; exit 3; }
	@rm -rf $(RUN_DIR_TLS); mkdir -p $(RUN_DIR_TLS)
	@openssl req -x509 -newkey rsa:2048 -keyout $(RUN_DIR_TLS)/key.pem \
	  -out $(RUN_DIR_TLS)/cert.pem -days 1 -nodes -subj "/CN=127.0.0.1" >/dev/null 2>&1 \
	  || { echo "  RESULT: FAIL - could not generate a self-signed certificate"; exit 1; }
	@echo "  minted a self-signed cert; probing GET and POST over HTTPS with curl -k ..."
	@cd $(RUN_DIR_TLS) && \
	  HTTP_PARSE_STATUS_FILE=parse.status HTTP_TLS_CERT=cert.pem HTTP_TLS_KEY=key.pem \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(PORT_TLS) & srv=$$!; sleep 0.7; \
	    gcode=$$(curl -sk https://127.0.0.1:$(PORT_TLS)/ -o get.body -w "%{http_code}"); echo $$gcode > get.code; \
	    printf "hello tls" > post.in; \
	    pcode=$$(curl -sk -X POST --data-binary @post.in https://127.0.0.1:$(PORT_TLS)/submit -o post.body -w "%{http_code}"); echo $$pcode > post.code; \
	    cp parse.status parse.saved 2>/dev/null; \
	    exit 0' \
	    > run.log 2>&1; \
	  st=$$?; \
	  gcode=$$(cat get.code 2>/dev/null); pcode=$$(cat post.code 2>/dev/null); \
	  pstat=$$(cat parse.saved 2>/dev/null); \
	  postbody=$$(cat post.body 2>/dev/null); \
	  if [ "$$gcode" = 200 ] && [ "$$pcode" = 200 ] && [ "$$postbody" = "hello tls" ] && [ "$$pstat" = "post 9" ]; then \
	    echo "  RESULT: PASS - the VERIFIED HTTP server answered a GET (200) and echoed a POST (200, body 'hello tls') over a TLS-encrypted connection (parse.status='post 9')"; \
	    rm -rf $(RUN_DIR_TLS_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - server/curl did not terminate: killed after $(TIMEOUT)s (get=$$gcode post=$$pcode)"; \
	    else echo "  RESULT: FAIL - get=$$gcode (want 200) post=$$pcode (want 200) postbody='$$postbody' (want 'hello tls') status='$$pstat' (want 'post 9')"; fi; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(RUN_DIR_TLS_ABS) for inspection)"; \
	    exit 1; \
	  fi

clean:
	rm -rf $(RUN_DIR) $(RUN_DIR)_post $(RUN_DIR_POST) $(RUN_DIR_SMUG) $(RUN_DIR_METH) $(RUN_DIR_LIM) $(RUN_DIR_ERR) $(RUN_DIR_CHK) $(RUN_DIR_TMO) $(RUN_DIR_KA) $(RUN_DIR_TLS)

help:
	@echo "HTTP interop test (vs curl):"
	@echo "  make test   - start http_server (verified response) and fetch it with curl;"
	@echo "                PASS iff curl gets HTTP 200 and a byte-identical body."
	@echo "  make clean  - remove the interop run directory"
	@echo "  Overrides:  PORT=<n> (default $(PORT))  TIMEOUT=<seconds> (default $(TIMEOUT))."
