# Makefile for the imbedding

TJROOT = /usr/local/bin
#VPATH = ../common

#export TJPATH = ../common

.PHONY: all 
all: binarysubst-examples.lp binarysans-examples.lp binary-unordered-examples.lp ps-elab.lp sp-elab.lp sans-canon-elab.lp subst-canon-elab.lp dd-examples.lp dd-canon-elab.lp oracle-examples.lp oracle-dd-elab.lp dd-oracle-elab.lp mating-examples.lp mating-canon-elab.lp cnf-examples.lp cnf-mating-elab.lp mating-explicit-examples.lp exp-examples.lp unordered-sans-elab.lp resolution-elab.lp
#all: basic lkf

.PHONY: basic
basic: lib.lp

.PHONY: lkf 
lkf: basic lkf-formulas.lp cforms.lp lkf-polarize.lp lkf-kernel.lp dd-examples.lp dlist-examples.lp binary-examples.lp binarysubst-examples.lp


%.lpo : %.mod %.sig
	$(TJROOT)/tjcc  $*

%.lp : %.lpo
	$(TJROOT)/tjlink  $*

-include depend
depend: *.mod *.sig
		$(TJROOT)/tjdepend *.mod  > depend-stage
		mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.lpo *.lp *.DT depend

.PHONY: tests
tests: cnf-examples.lp oracle-examples.lp 
	tjsim -b -s "test_all." cnf-examples.
	tjsim -b -s "test_all." oracle-examples.
