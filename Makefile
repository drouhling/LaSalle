MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(COQMAKE) clean

install: $(COQMAKEFILE)
	$(COQMAKE) install

%: Makefile.coq
	$(COQMAKE) $@
