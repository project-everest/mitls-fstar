#!/bin/bash
set -e
mkdir -p $FSTAR_HOME/everparse/tls
cp -t $FSTAR_HOME/everparse $QD_HOME/tests/layeff/*.fst $QD_HOME/tests/layeff/*.fsti
cp -t $FSTAR_HOME/everparse/tls Negotiation.Writers*Aux*.fst Negotiation.Writers*Aux*.fsti Negotiation.Writers.NoHoare.fst
