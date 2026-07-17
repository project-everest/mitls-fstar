#!/bin/bash
# quick single-module verify against warm _cache
cd /workspaces/agentic-tls/http_sample
FSTAR=/workspaces/agentic-tls/tools/everparse/opt/FStar/bin/fstar.exe
LOWPARSE=/workspaces/agentic-tls/tools/everparse/src/lowparse
export PATH=/workspaces/agentic-tls/tools/everparse/opt/z3:$PATH
timeout 400 $FSTAR --cache_checked_modules --cache_dir _cache \
  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse' \
  --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps \
  --include ../common --include $LOWPARSE --include $LOWPARSE/pulse --include spec --include impl \
  "$1" > /tmp/vf.log 2>&1
echo "EXIT $?"
grep -iE "error|verified module|discharged|admit" /tmp/vf.log | head -20
