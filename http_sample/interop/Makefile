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

.PHONY: all test build-progs clean help

all: test

# Build the extracted verified bundle (via the parent) then our server program.
build-progs:
	@$(MAKE) --no-print-directory -C $(PARENT) extract-loops
	@echo "Compiling the HTTP server over the VERIFIED response driver..."
	$(CC) $(CFLAGS_INTEROP) -o $(EXTRACT_DIR)/http_server \
	  http_server.c \
	  $(EXTRACT_DIR)/HTTP_Verified.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "Server http_server (verified response) compiled to $(EXTRACT_DIR)/."

# ── curl <-> our verified-response server ─────────────────────────────────────
test: build-progs
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

clean:
	rm -rf $(RUN_DIR)

help:
	@echo "HTTP interop test (vs curl):"
	@echo "  make test   - start http_server (verified response) and fetch it with curl;"
	@echo "                PASS iff curl gets HTTP 200 and a byte-identical body."
	@echo "  make clean  - remove the interop run directory"
	@echo "  Overrides:  PORT=<n> (default $(PORT))  TIMEOUT=<seconds> (default $(TIMEOUT))."
