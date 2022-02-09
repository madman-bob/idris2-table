.PHONY: test retest clean

INTERACTIVE ?= --interactive
threads ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)

TEST_SCRIPTS := $(wildcard */run) $(wildcard */*/run)
DEPENDS := $(TEST_SCRIPTS:run=depends)

test: build/exec/table-tests $(DEPENDS)
	./build/exec/table-tests idris2 $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only $(only)

retest: build/exec/table-tests $(DEPENDS)
	./build/exec/table-tests idris2 $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only-file failures --only $(only)

build/exec/table-tests: table-tests.ipkg TableTests.idr
	idris2 --build table-tests.ipkg

%/depends: %/run
	mkdir "$@"
	ln -s "$(CURDIR)/../build/ttc" "$@/table-0"
	ln -s "$(CURDIR)/../B2T2/build/ttc" "$@/b2t2-0"

clean:
	$(RM) failures
	$(RM) -r build
	@find . -depth -name 'depends' -type d -exec rm -rf {} \;
	@find . -type f -name 'output' -exec rm -rf {} \;
