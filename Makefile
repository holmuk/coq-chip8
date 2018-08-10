
default: CoqMakefile
	$(MAKE) -f CoqMakefile

quick: CoqMakefile
	$(MAKE) -f CoqMakefile quick

install: CoqMakefile
	$(MAKE) -f CoqMakefile install

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:
	if [ -f CoqMakefile ]; then \
	  $(MAKE) -f CoqMakefile cleanall; fi
	rm -f CoqMakefile

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

examples: $(EXAMPLEVOFILES): %.vo: %.v
		$(SHOW)COQC $<
		$(COQC) $(COQFLAGS) $<

.PHONY: default quick clean lint distclean install
