all: pki
	$(MAKE) -C src/tls all
	$(MAKE) -C apps/quicMinusNet all

test: pki
	$(MAKE) -C src/tls test
	$(MAKE) -C apps/quicMinusNet test

pki:
	$(MAKE) -C src/pki
