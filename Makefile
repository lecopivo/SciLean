.PHONY: examples

examples:
	lake build SurfaceMeshTests
	./build/bin/SurfaceMeshTests
	lake build HarmonicOscillator
	./build/bin/HarmonicOscillator
