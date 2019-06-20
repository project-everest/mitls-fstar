LDFLAGS = \
  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a \
  -L../compact -lmitls -L$(HACL_HOME)/dist/compact -levercrypt \
  -L$(MITLS_HOME)/src/pki -lmipki

include Makefile.basic

test.exe:
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
