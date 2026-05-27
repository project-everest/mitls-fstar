#!/bin/bash

set -e

echo "=== KaRaMeL Bundle Bug Reproduction ==="
echo ""

# Try to find F* and KaRaMeL
if [ -n "$FSTAR_HOME" ]; then
    FSTAR="$FSTAR_HOME/bin/fstar.exe"
    KRML="$FSTAR_HOME/bin/krml"
elif [ -f "/home/nswamy/workspace/agentic-tls/tools/FStar/bin/fstar.exe" ]; then
    FSTAR="/home/nswamy/workspace/agentic-tls/tools/FStar/bin/fstar.exe"
    KRML="/home/nswamy/workspace/agentic-tls/tools/FStar/bin/krml"
elif command -v fstar.exe >/dev/null 2>&1; then
    FSTAR="fstar.exe"
    KRML="krml"
else
    echo "Error: fstar.exe not found. Set FSTAR_HOME or add to PATH"
    exit 1
fi

echo "Using F*: $FSTAR"
echo ""

mkdir -p _cache _output _extract

echo "Step 1: Verifying F* modules..."
"$FSTAR" --cache_checked_modules --cache_dir _cache Simple.State.fst
"$FSTAR" --cache_checked_modules --cache_dir _cache Simple.Internal.fst  
"$FSTAR" --cache_checked_modules --cache_dir _cache Simple.API.fst
echo "✓ Verification passed"
echo ""

echo "Step 2: Extracting to .krml..."
"$FSTAR" --codegen krml --extract_module Simple.State --odir _output --cache_dir _cache Simple.State.fst
"$FSTAR" --codegen krml --extract_module Simple.Internal --odir _output --cache_dir _cache Simple.Internal.fst
"$FSTAR" --codegen krml --extract_module Simple.API --odir _output --cache_dir _cache Simple.API.fst
echo "✓ Extraction complete"
echo ""

echo "Step 3: Test bundle WITHOUT Simple.Internal (should work)..."
"$KRML" -tmpdir _extract -skip-compilation \
  -bundle 'Simple.API=Simple.State[rename=Simple]' \
  _output/Simple_API.krml _output/Simple_State.krml _output/Simple_Internal.krml
echo "✓ Bundle without Simple.Internal succeeded"
echo ""

rm -rf _extract/*

echo "Step 4: Test bundle WITH Simple.Internal (should crash)..."
echo "Running: krml -bundle 'Simple.API=Simple.State,Simple.Internal[rename=Simple]' ..."
echo ""
"$KRML" -tmpdir _extract -skip-compilation \
  -bundle 'Simple.API=Simple.State,Simple.Internal[rename=Simple]' \
  _output/Simple_API.krml _output/Simple_State.krml _output/Simple_Internal.krml

echo ""
echo "✓ Bundle with Simple.Internal succeeded (bug may be fixed!)"
