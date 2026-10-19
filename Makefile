AGDA ?= agda
STDLIB ?= .deps/agda-stdlib-2.3
AGDAFLAGS = --no-default-libraries --library-file=.deps/libraries

.PHONY: all deps toolchain check build test clean

all: test

deps:
	sh tools/stdlib.sh

toolchain:
	@test "$$($(AGDA) --version | head -n 1)" = "Agda version 2.8.0" || { echo 'Agda 2.8.0 is required'; exit 1; }
	@test -f $(STDLIB)/standard-library.agda-lib || { echo 'run make deps or set STDLIB'; exit 1; }
	@head -n 1 $(STDLIB)/standard-library.agda-lib | grep -qx 'name: standard-library-2.3'
	@mkdir -p .deps
	@printf '%s\n' '$(STDLIB)/standard-library.agda-lib' > .deps/libraries

check: toolchain
	@set -e; for source in $$(find src test -type f -name '*.agda' | sort); do \
		$(AGDA) $(AGDAFLAGS) --safe "$$source"; \
	done
	$(AGDA) $(AGDAFLAGS) app/Main.agda

build: toolchain
	$(AGDA) $(AGDAFLAGS) --compile --compile-dir=build app/Main.agda
	cp build/Main build/rumus

test: check build
	python3 test/regression.py build/rumus

clean:
	rm -rf build _build
