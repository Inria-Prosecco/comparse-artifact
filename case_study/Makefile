CTLS_HOME     ?= .
FSTAR_HOME    ?= $(dir $(shell which fstar.exe))/..
COMPARSE_HOME ?= $(CTLS_HOME)/../comparse

SOURCE_DIR = src

INCLUDE_DIRS = $(SOURCE_DIR) $(COMPARSE_HOME)/src
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
FSTAR = $(FSTAR_EXE) $(MAYBE_ADMIT)

FSTAR_EXTRACT = --extract '-* +CTLS +TLS13 +MLS'
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '+241@247+285' --cache_dir cache --odir obj --cmi

.PHONY: all clean

all: copy_lib

clean:
	rm -rf hints obj cache ml/lib/src ml/tests/src

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIR))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIR)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

# Verification

hints:
	mkdir $@

cache:
	mkdir $@

obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | hints cache obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction
.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract_lib copy_lib

extract_lib: $(ALL_ML_FILES)

copy_lib: extract_lib
	mkdir -p ml/lib/src
	cp $(ALL_ML_FILES) ml/lib/src

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include obj

