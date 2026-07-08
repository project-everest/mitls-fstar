# ═══════════════════════════════════════════════════════════════════
# YMODEM interoperability tests against the lrzsz reference (sb / rb)
# ═══════════════════════════════════════════════════════════════════
# Two black-box interop tests transfer a dummy text file (dummy.txt) between one
# of our *extracted* YMODEM programs and the matching lrzsz reference program,
# then check that the received copy is byte-for-byte identical to the original:
#
#   test-server : our extracted `ymodem_sb` (sender)   <->  lrzsz `rb` (receiver)
#   test-client : lrzsz `sb dummy.txt` (sender)        <->  our extracted `ymodem_rb` (receiver)
#
# YMODEM is bidirectional over a single link: the sender writes packets and reads
# ACK/NAK/'C', the receiver writes ACK/NAK/'C' and reads packets.  We wire the two
# programs together over stdin/stdout with a named pipe (`back`) for the reverse
# channel:
#
#     sender  < back  |  receiver  > back
#
# so the sender's stdout (packets) feeds the receiver's stdin, and the receiver's
# stdout (ACK/NAK/'C') feeds `back`, which is the sender's stdin.  The receiver
# runs in a fresh `recv/` directory and writes the file there under the name from
# the YMODEM header block; we then `cmp` it against the original.
#
# The extracted programs are built by the parent Makefile's `wrappers` target
# (into ../_extract).  lrzsz's `sb`/`rb` must be on PATH (Debian/Ubuntu package
# `lrzsz`); a test that cannot find them reports SKIP.
#
# NOTE: these are UNVERIFIED interop drivers exercised end-to-end; a timeout
# guards against a stalled handshake.

PARENT      := ..
EXTRACT_DIR := $(PARENT)/_extract
SB_OUR      := $(abspath $(EXTRACT_DIR)/ymodem_sb)
RB_OUR      := $(abspath $(EXTRACT_DIR)/ymodem_rb)

DUMMY   := dummy.txt
SRC     := $(abspath $(DUMMY))
SRV_DIR := _run_server
CLI_DIR := _run_client
TIMEOUT ?= 30

.PHONY: all test test-server test-client build-wrappers clean help

all: test

# Build (or refresh) the extracted C programs via the parent Makefile.
build-wrappers:
	@$(MAKE) --no-print-directory -C $(PARENT) wrappers

# ── Server test: our extracted sender  <->  lrzsz rb (receiver) ────────────
test-server: build-wrappers $(DUMMY)
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " SERVER interop test:  extracted ymodem_sb (sender)  ->  lrzsz rb (receiver)"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v rb >/dev/null 2>&1 || { echo "  SKIP: lrzsz 'rb' not found on PATH (install the 'lrzsz' package)"; exit 3; }
	@rm -rf $(SRV_DIR); mkdir -p $(SRV_DIR)/recv; mkfifo $(SRV_DIR)/back
	@echo "  sending $(DUMMY) ($$(wc -c < $(DUMMY)) bytes) with our sender; receiving with lrzsz rb ..."
	-@cd $(SRV_DIR)/recv && timeout $(TIMEOUT) bash -c '$(SB_OUR) $(SRC) < ../back | rb > ../back' > ../run.log 2>&1
	@if cmp -s $(SRC) $(SRV_DIR)/recv/$(DUMMY); then \
	   echo "  RESULT: PASS - rb received an identical copy of $(DUMMY)"; \
	 else \
	   echo "  RESULT: FAIL - received file is missing or differs from $(DUMMY)"; \
	   echo "  --- $(SRV_DIR)/recv ---"; ls -la $(SRV_DIR)/recv 2>/dev/null; \
	   if [ -f $(SRV_DIR)/recv/$(DUMMY) ]; then echo "  --- cmp ---"; cmp $(SRC) $(SRV_DIR)/recv/$(DUMMY) 2>&1 | head -3; fi; \
	   echo "  --- run.log (tail) ---"; tail -20 $(SRV_DIR)/run.log 2>/dev/null; \
	   exit 1; \
	 fi

# ── Client test: lrzsz sb (sender)  <->  our extracted receiver ────────────
test-client: build-wrappers $(DUMMY)
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " CLIENT interop test:  lrzsz sb (sender)  ->  extracted ymodem_rb (receiver)"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v sb >/dev/null 2>&1 || { echo "  SKIP: lrzsz 'sb' not found on PATH (install the 'lrzsz' package)"; exit 3; }
	@rm -rf $(CLI_DIR); mkdir -p $(CLI_DIR)/recv; mkfifo $(CLI_DIR)/back
	@echo "  sending $(DUMMY) ($$(wc -c < $(DUMMY)) bytes) with lrzsz sb; receiving with our receiver ..."
	-@cd $(CLI_DIR)/recv && timeout $(TIMEOUT) bash -c 'sb $(SRC) < ../back | $(RB_OUR) > ../back' > ../run.log 2>&1
	@if cmp -s $(SRC) $(CLI_DIR)/recv/$(DUMMY); then \
	   echo "  RESULT: PASS - our receiver reconstructed an identical copy of $(DUMMY)"; \
	 else \
	   echo "  RESULT: FAIL - received file is missing or differs from $(DUMMY)"; \
	   echo "  --- $(CLI_DIR)/recv ---"; ls -la $(CLI_DIR)/recv 2>/dev/null; \
	   if [ -f $(CLI_DIR)/recv/$(DUMMY) ]; then echo "  --- cmp ---"; cmp $(SRC) $(CLI_DIR)/recv/$(DUMMY) 2>&1 | head -3; fi; \
	   echo "  --- run.log (tail) ---"; tail -20 $(CLI_DIR)/run.log 2>/dev/null; \
	   exit 1; \
	 fi

# ── Run both, aggregate, and report ────────────────────────────────────────
test:
	@rc=0; \
	 $(MAKE) --no-print-directory test-server || rc=1; \
	 echo; \
	 $(MAKE) --no-print-directory test-client || rc=1; \
	 echo; \
	 if [ $$rc -eq 0 ]; then echo "OVERALL: all interop tests PASSED"; \
	 else echo "OVERALL: some interop tests FAILED (see above)"; fi; \
	 exit $$rc

clean:
	rm -rf $(SRV_DIR) $(CLI_DIR)

help:
	@echo "YMODEM interop tests:"
	@echo "  make test-server  - our ymodem_sb (sender) vs lrzsz rb (receiver)"
	@echo "  make test-client  - lrzsz sb (sender) vs our ymodem_rb (receiver)"
	@echo "  make test         - run both and report an aggregate result"
	@echo "  make clean        - remove interop run directories"
	@echo "  (override the stall guard with TIMEOUT=<seconds>; default $(TIMEOUT))"
