#!/usr/bin/env python3
"""
Benchmark comparison: SciLean Metal vs PyTorch vs MLX

Run with: .venv/bin/python benchmarks/compare_frameworks.py
"""

import time
import subprocess
import json
from dataclasses import dataclass
from typing import Optional

import torch
import mlx.core as mx

@dataclass
class BenchmarkResult:
    framework: str
    operation: str
    time_ms: float
    device: str

def benchmark(name: str, warmup: int, iterations: int, fn):
    """Run a benchmark with warmup and timing."""
    # Warmup
    for _ in range(warmup):
        fn()

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        fn()
    elapsed = time.perf_counter() - start

    return elapsed / iterations * 1000  # ms

# ============== KMeans Loss ==============

def kmeans_loss_pytorch_cpu(points, centroids):
    """Compute KMeans loss: sum of squared distances to nearest centroid."""
    # points: (n, d), centroids: (k, d)
    # Compute pairwise distances
    dists = torch.cdist(points, centroids, p=2) ** 2  # (n, k)
    min_dists = dists.min(dim=1).values
    return min_dists.sum()

def kmeans_loss_pytorch_mps(points, centroids):
    """KMeans on MPS (Apple Silicon GPU via PyTorch)."""
    points_mps = points.to('mps')
    centroids_mps = centroids.to('mps')
    dists = torch.cdist(points_mps, centroids_mps, p=2) ** 2
    min_dists = dists.min(dim=1).values
    result = min_dists.sum()
    torch.mps.synchronize()
    return result

def kmeans_loss_mlx(points, centroids):
    """KMeans loss using MLX."""
    # points: (n, d), centroids: (k, d)
    # Broadcast: points[:, None, :] - centroids[None, :, :] -> (n, k, d)
    diff = mx.expand_dims(points, axis=1) - mx.expand_dims(centroids, axis=0)
    dists = mx.sum(diff ** 2, axis=2)  # (n, k)
    min_dists = mx.min(dists, axis=1)
    result = mx.sum(min_dists)
    mx.eval(result)  # Force computation
    return result

# ============== GEMM ==============

def gemm_pytorch_cpu(A, B):
    return torch.mm(A, B)

def gemm_pytorch_mps(A, B):
    A_mps = A.to('mps')
    B_mps = B.to('mps')
    result = torch.mm(A_mps, B_mps)
    torch.mps.synchronize()
    return result

def gemm_mlx(A, B):
    result = mx.matmul(A, B)
    mx.eval(result)
    return result

# ============== Main ==============

def run_benchmarks():
    results = []

    # KMeans parameters
    n, d, k = 10000, 64, 32

    print("=" * 60)
    print("Framework Comparison Benchmark")
    print("=" * 60)

    # Generate random data
    print(f"\nKMeans: n={n}, d={d}, k={k}")
    print("-" * 40)

    # PyTorch CPU
    points_torch = torch.rand(n, d)
    centroids_torch = torch.rand(k, d)

    time_ms = benchmark("PyTorch CPU KMeans", 2, 10,
                        lambda: kmeans_loss_pytorch_cpu(points_torch, centroids_torch))
    print(f"PyTorch CPU:  {time_ms:.3f} ms")
    results.append(BenchmarkResult("PyTorch", "KMeans", time_ms, "CPU"))

    # PyTorch MPS
    if torch.backends.mps.is_available():
        time_ms = benchmark("PyTorch MPS KMeans", 2, 10,
                            lambda: kmeans_loss_pytorch_mps(points_torch, centroids_torch))
        print(f"PyTorch MPS:  {time_ms:.3f} ms")
        results.append(BenchmarkResult("PyTorch", "KMeans", time_ms, "MPS"))

    # MLX
    points_mlx = mx.random.uniform(shape=(n, d))
    centroids_mlx = mx.random.uniform(shape=(k, d))
    mx.eval(points_mlx, centroids_mlx)

    time_ms = benchmark("MLX KMeans", 2, 10,
                        lambda: kmeans_loss_mlx(points_mlx, centroids_mlx))
    print(f"MLX:          {time_ms:.3f} ms")
    results.append(BenchmarkResult("MLX", "KMeans", time_ms, "GPU"))

    # GEMM parameters
    m, kk, nn = 512, 512, 512

    print(f"\nGEMM: {m}x{kk} @ {kk}x{nn}")
    print("-" * 40)

    # PyTorch CPU
    A_torch = torch.rand(m, kk)
    B_torch = torch.rand(kk, nn)

    time_ms = benchmark("PyTorch CPU GEMM", 1, 10,
                        lambda: gemm_pytorch_cpu(A_torch, B_torch))
    print(f"PyTorch CPU:  {time_ms:.3f} ms")
    results.append(BenchmarkResult("PyTorch", "GEMM", time_ms, "CPU"))

    # PyTorch MPS
    if torch.backends.mps.is_available():
        time_ms = benchmark("PyTorch MPS GEMM", 1, 10,
                            lambda: gemm_pytorch_mps(A_torch, B_torch))
        print(f"PyTorch MPS:  {time_ms:.3f} ms")
        results.append(BenchmarkResult("PyTorch", "GEMM", time_ms, "MPS"))

    # MLX
    A_mlx = mx.random.uniform(shape=(m, kk))
    B_mlx = mx.random.uniform(shape=(kk, nn))
    mx.eval(A_mlx, B_mlx)

    time_ms = benchmark("MLX GEMM", 1, 10,
                        lambda: gemm_mlx(A_mlx, B_mlx))
    print(f"MLX:          {time_ms:.3f} ms")
    results.append(BenchmarkResult("MLX", "GEMM", time_ms, "GPU"))

    # Run SciLean benchmark
    print("\nSciLean Metal (from executable):")
    print("-" * 40)
    try:
        result = subprocess.run(
            ['.lake/build/bin/MetalBenchmark'],
            capture_output=True, text=True, timeout=60
        )
        # Parse SciLean output
        for line in result.stdout.split('\n'):
            if 'CPU KMeans:' in line or 'GPU KMeans:' in line:
                print(line)
            if 'CPU GEMM:' in line or 'GPU GEMM:' in line:
                print(line)
    except Exception as e:
        print(f"Could not run SciLean benchmark: {e}")

    print("\n" + "=" * 60)
    print("Summary")
    print("=" * 60)

    # Group by operation
    for op in ["KMeans", "GEMM"]:
        print(f"\n{op}:")
        op_results = [r for r in results if r.operation == op]
        for r in sorted(op_results, key=lambda x: x.time_ms):
            print(f"  {r.framework:12} ({r.device:4}): {r.time_ms:8.3f} ms")

    return results

if __name__ == "__main__":
    run_benchmarks()
