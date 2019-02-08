all: lowparse

lowparse:
	+$(MAKE) -f Makefile.LowParse

examples: lowparse
	+$(MAKE) -f Makefile.LowParseExamples

clean:
	+$(MAKE) -f Makefile.LowParseExamples clean
	+$(MAKE) -f Makefile.LowParse clean

.PHONY: lowparse examples clean
