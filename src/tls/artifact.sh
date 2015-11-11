 #!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

wd=`pwd`

mkdir -p artifact
# Cedric 15-10-12 mkdir -p artifact/injectivity_proof

make clean pp

echo
echo '---copying mitls---'
echo
  cp -v TLSError.fst TLSConstants.fst Nonce.fst \
RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst \
HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti \
TLSInfo.fst Range.p.fst DataStream.fst StatefulPlain.fsti LHAEPlain.fst \
AEAD_GCM.fst StatefulLHAE.fst artifact; \
# Cedric 15-10-12   cp -v ../fstar_proof/* artifact/injectivity_proof;

echo
echo '---removing comments---'
echo
  pushd artifact; $wd/../../scripts/anonymize -m release -B *.fst *.fsti; popd
  
echo
echo '---testing---'
echo  
make -C artifact


echo
echo '---packaging---'
echo
tar cvzf miTLS-POPL2016.tgz artifact
