.PHONY: examples

examples:
	lake build SurfaceMeshTests
	./build/bin/SurfaceMeshTests
