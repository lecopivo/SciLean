TESTS := $(shell find Test -name '*.lean')

.PHONY: all build test lint examples

all: build

build:
	lake build

examples:
	lake build HelloWorld
	./.lake/build/bin/HelloWorld
	lake build SurfaceMeshTests
	./.lake/build/bin/SurfaceMeshTests
	lake build HarmonicOscillator
	./.lake/build/bin/HarmonicOscillator
	lake build WaveEquation
	./.lake/build/bin/WaveEquation
	lake build BFGS
	./.lake/build/bin/BFGS
	lake build LBFGS
	./.lake/build/bin/LBFGS
	lake build BlasTest
	./.lake/build/bin/BlasTest
	lake build FloatTest
	./.lake/build/bin/FloatTest

lint: build
	./build/bin/runLinter
