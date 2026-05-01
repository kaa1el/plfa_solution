AGDA ?= agda

SRC := $(shell find src -name '*.agda' -not -path '*/demo/*')

.PHONY: all check clean

all: check

check:
	@total=$$(echo $(SRC) | wc -w | tr -d ' '); i=0; \
	for f in $(SRC); do \
		i=$$((i+1)); \
		printf '[%d/%d] %s\n' $$i $$total $$f; \
		$(AGDA) $$f || { echo "FAILED: $$f"; exit 1; }; \
	done; \
	echo "OK: checked $$total files"

clean:
	rm -rf _build
