TESTS := $(shell find test -name '*.lean')

.PHONY: all build test lint examples

all: build test

build:
	lake build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	lake env lean --load-dynlib=./.lake/build/lib/libSciLean-Tactic-LSimp-Main-1.so  test/$*

examples:
	lake build SurfaceMeshTests
	./.lake/build/bin/SurfaceMeshTests
	lake build HarmonicOscillator
	./.lake/build/bin/HarmonicOscillator
	lake build WaveEquation
	./.lake/build/bin/WaveEquation

lint: build
	./build/bin/runLinter
