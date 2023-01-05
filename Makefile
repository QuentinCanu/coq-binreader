# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS := --display=short

# --------------------------------------------------------------------
.PHONY: default all install uninstall fmt fmt-promote clean

# --------------------------------------------------------------------
default: all
	@true

all:
	dune build $(DUNEOPTS) 

install:
	dune install $(DUNEOPTS)

uninstall:
	dune uninstall $(DUNEOPTS)

fmt:
	dune build @fmt

fmt-promote:
	dune build @fmt --auto-promote

clean:
	dune clean $(DUNEOPTS)
