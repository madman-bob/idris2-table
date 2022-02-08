.PHONY: all table b2t2 test retest clean

all: table

install: table
	idris2 --install table.ipkg
	make -C B2T2 install

table: build/ttc/Data/Table.ttc

build/ttc/Data/Table.ttc: table.ipkg Data/Table/* Data/Table/*/*
	idris2 --build table.ipkg

b2t2:
	make -C B2T2 b2t2

test:
	make -C tests test

retest:
	make -C tests retest

clean:
	make -C B2T2 clean
	$(RM) -r build
