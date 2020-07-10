#!/bin/bash
set -e
set -x
POPL_TARGET=$FSTAR_HOME/examples/layeredeffects/everparse
[[ ! -d $POPL_TARGET ]]
mkdir -p $POPL_TARGET/tls
cp -t $POPL_TARGET $QD_HOME/tests/layeff/L*.fst $QD_HOME/tests/layeff/L*.fsti $QD_HOME/tests/layeff/*.h $QD_HOME/tests/layeff/*.c $QD_HOME/tests/layeff/Makefile.basic
cp -t $POPL_TARGET/tls Negotiation.Writers*Aux*.fst Negotiation.Writers*Aux*.fsti Negotiation.Writers.NoHoare.fst dist/all/Negotiation_Writers_NoHoare.h dist/all/Negotiation_Writers_NoHoare.c
