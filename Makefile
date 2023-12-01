TESTS := $(shell find test -name '*.lean')

.PHONY: all build test lint examples

all: build test

build:
	lake build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	lake env lean test/$*

examples:
	lake build SurfaceMeshTests
	# ./build/bin/SurfaceMeshTests
	lake build HarmonicOscillator
	# ./build/bin/HarmonicOscillator

lint: build
	./build/bin/runLinter
