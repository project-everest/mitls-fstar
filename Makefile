# Just aliases so that there's a proper target in the root directory.

all: tls-all quic-app tls-app

.PHONY: tls-all
tls-all: pki
	$(MAKE) -C src/tls

.PHONY: quic-app
quic-app: tls-all
	$(MAKE) -C apps/quicMinusNet all

.PHONY: mitls-app
tls-app: tls-all
	$(MAKE) -C apps/cmitls all


test: tls-test quic-app-test tls-app-test

.PHONY: tls-test
tls-test: tls-all
	$(MAKE) -C src/tls/dist/test test

.PHONY: quic-app-test
quic-app-test: tls-all
	$(MAKE) -C apps/quicMinusNet test

.PHONY: tls-app-test
tls-app-test: tls-all
	$(MAKE) -C apps/cmitls test

.PHONY: pki
pki:
	$(MAKE) -C src/pki
