.PHONY: test retest clean

INTERACTIVE ?= --interactive
threads ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)

test: build/exec/table-tests
	./build/exec/table-tests idris2 $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only $(only)

retest: build/exec/table-tests
	./build/exec/table-tests idris2 $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only-file failures --only $(only)

build/exec/table-tests: table-tests.ipkg TableTests.idr
	idris2 --build table-tests.ipkg

clean:
	$(RM) failures
	$(RM) -r build
	@find . -type f -name 'output' -exec rm -rf {} \;
