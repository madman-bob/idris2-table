.PHONY: all install table test retest clean

all: table

install: table
	idris2 --install table.ipkg

table: build/ttc/Data/Table.ttc

build/ttc/Data/Table.ttc: table.ipkg Data/Table/* Data/Table/*/*
	idris2 --build table.ipkg

test:
	make -C tests test

retest:
	make -C tests retest

clean:
	rm -rf build
