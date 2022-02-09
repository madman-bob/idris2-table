.PHONY: install b2t2 clean

install: b2t2
	idris2 --install b2t2.ipkg

b2t2: B2T2/build/ttc/B2T2.ttc

B2T2/build/ttc/B2T2.ttc: b2t2.ipkg B2T2.idr B2T2/* B2T2/*/* B2T2/*/*/* depends
	idris2 --build b2t2.ipkg

depends:
	mkdir "depends"
	ln -s "$(CURDIR)/../build/ttc" "$@/table-0"

clean:
	$(RM) -r build depends
