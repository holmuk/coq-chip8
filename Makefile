#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU General Public License as published by  #
#  the Free Software Foundation, either version 2 of the License, or  #
#  (at your option) any later version.  This file is also distributed #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

# include Makefile.config

ARCH="chip8"
ARCHDIRS=$(ARCH)

DIRS=lib $(ARCHDIRS)

RECDIRS=lib $(ARCHDIRS)

COQINCLUDES=$(foreach d, $(RECDIRS), -R $(d) compcert.$(d))

COQC="coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="coqdep" $(COQINCLUDES)
COQDOC=coqdoc
COQEXEC="coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Archi.v Fappli_IEEE_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v BoolEqual.v

FILES=$(VLIB)

# Generated source files

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof

proof: $(FILES:.v=.vo)

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof extraction runtime FORCE

%.vo: %.v
	@echo "COQC $*.v"

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

depend: depend1

depend1: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f driver/Version.ml
	rm -f compcert.ini
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f .depend
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean

# Problems with coqchk (coq 8.6):
# Integers.Int.Z_mod_modulus_range takes forever to check
# compcert.backend.SelectDivproof.divs_mul_shift_2 takes forever to check

-include .depend

FORCE:
