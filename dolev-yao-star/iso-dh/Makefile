DY_HOME = $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))/..
include ../Makefile

APP_BASE_FST_FILES=ISODH.Messages.fst ISODH.Sessions.fst
APP_BASE_CMX_FILES=ocaml-symbolic/ISODH_Messages.cmx ocaml-symbolic/ISODH_Sessions.cmx

APP_FST_FILES=ISODH.Protocol.fst ISODH.Debug.fst
APP_CMX_FILES=ocaml-symbolic/ISODH_Protocol.cmx ocaml-symbolic/ISODH_Debug.cmx

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(APP_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(APP_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)
test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml-symbolic/test.exe

ocaml-symbolic/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
