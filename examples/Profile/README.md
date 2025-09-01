# SciLean Performance Profiling Examples

This repository contains examples designed to test and improve the performance of SciLean.

## Structure of Each Test

Each test should include at least three implementations:

- **Reference C Implementation**: Provides a performance baseline representing the best possible speed.
- **Optimized Lean Implementation**: A Lean-based implementation focused solely on achieving the best performance.
- **Idiomatic SciLean Implementation**: A user-friendly SciLean implementation that reflects how typical users would write code.

## Building and Running Tests

For examples, to build and execute `KMeans` test, use the following commands:

```bash
lake build ProfileKMeans && ./.lake/build/bin/ProfileKMeans
```

This prints out:
```
k-means profile test
k := 1000, n := 10000, d := 16

reference c impl       time := 40.716340ms 	loss := 7202.578688
best lean impl         time := 44.375879ms 	loss := 7202.578688
scilean no BLAS        time := 79.685435ms 	loss := 7202.578688
target scilean impl    time := 1280.020544ms 	loss := 7202.578688
```

## Profiling Tests

You can profile any of these examples using `perf`. For example:

```bash
sudo perf record --call-graph dwarf ./.lake/build/bin/ProfileKMeans
```

This generates a `perf.data` file, which can be analyzed using `hotspot`:

```bash
hotspot perf.data
```

> **Note:** If `hotspot` cannot open the `perf.data` file, try running it with `sudo`.

