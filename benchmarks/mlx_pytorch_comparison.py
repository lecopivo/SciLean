#!/usr/bin/env python3
"""
SciLean Metal vs MLX vs PyTorch Benchmark Suite

Compares GPU tensor operations across:
- SciLean Metal (via compiled test program)
- MLX (Apple's ML framework)
- PyTorch MPS (Metal Performance Shaders backend)

Run: uv run benchmarks/mlx_pytorch_comparison.py
"""

import subprocess
import time
import sys
from dataclasses import dataclass
from typing import Optional
import json

# Check if MLX is available
try:
    import mlx.core as mx
    HAS_MLX = True
except ImportError:
    HAS_MLX = False
    print("Warning: MLX not installed. Install with: uv add mlx")

# Check if PyTorch is available
try:
    import torch
    HAS_TORCH = torch.backends.mps.is_available()
    if not HAS_TORCH:
        print("Warning: PyTorch MPS not available")
except ImportError:
    HAS_TORCH = False
    print("Warning: PyTorch not installed. Install with: uv add torch")

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
    print("Warning: NumPy not installed. Install with: uv add numpy")

@dataclass
class BenchResult:
    name: str
    backend: str
    size: str
    time_ms: float
    gflops: Optional[float] = None

    def __str__(self):
        gflops_str = f"{self.gflops:.1f} GFLOP/s" if self.gflops else "N/A"
        return f"{self.backend:12} | {self.size:12} | {self.time_ms:10.3f} ms | {gflops_str}"

def benchmark_gemm_mlx(m: int, k: int, n: int, iterations: int = 10) -> BenchResult:
    """Benchmark matrix multiplication with MLX"""
    if not HAS_MLX:
        return BenchResult("GEMM", "MLX", f"{m}x{k}x{n}", float('inf'), 0)

    A = mx.random.uniform(shape=(m, k))
    B = mx.random.uniform(shape=(k, n))

    # Warmup
    for _ in range(3):
        C = A @ B
        mx.eval(C)

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        C = A @ B
        mx.eval(C)
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    flops = 2 * m * k * n  # multiply-accumulate = 2 ops
    gflops = (flops / (time_ms / 1000)) / 1e9

    return BenchResult("GEMM", "MLX", f"{m}x{k}x{n}", time_ms, gflops)

def benchmark_gemm_torch(m: int, k: int, n: int, iterations: int = 10) -> BenchResult:
    """Benchmark matrix multiplication with PyTorch MPS"""
    if not HAS_TORCH:
        return BenchResult("GEMM", "PyTorch MPS", f"{m}x{k}x{n}", float('inf'), 0)

    device = torch.device("mps")
    A = torch.randn(m, k, device=device, dtype=torch.float32)
    B = torch.randn(k, n, device=device, dtype=torch.float32)

    # Warmup
    for _ in range(3):
        C = torch.mm(A, B)
        torch.mps.synchronize()

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        C = torch.mm(A, B)
        torch.mps.synchronize()
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    flops = 2 * m * k * n
    gflops = (flops / (time_ms / 1000)) / 1e9

    return BenchResult("GEMM", "PyTorch MPS", f"{m}x{k}x{n}", time_ms, gflops)

def benchmark_softmax_mlx(n: int, iterations: int = 10) -> BenchResult:
    """Benchmark softmax with MLX"""
    if not HAS_MLX:
        return BenchResult("Softmax", "MLX", f"{n}", float('inf'), 0)

    x = mx.random.uniform(shape=(n,))

    # Warmup
    for _ in range(3):
        y = mx.softmax(x)
        mx.eval(y)

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        y = mx.softmax(x)
        mx.eval(y)
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    return BenchResult("Softmax", "MLX", f"{n}", time_ms)

def benchmark_softmax_torch(n: int, iterations: int = 10) -> BenchResult:
    """Benchmark softmax with PyTorch MPS"""
    if not HAS_TORCH:
        return BenchResult("Softmax", "PyTorch MPS", f"{n}", float('inf'), 0)

    device = torch.device("mps")
    x = torch.randn(n, device=device, dtype=torch.float32)

    # Warmup
    for _ in range(3):
        y = torch.softmax(x, dim=0)
        torch.mps.synchronize()

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        y = torch.softmax(x, dim=0)
        torch.mps.synchronize()
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    return BenchResult("Softmax", "PyTorch MPS", f"{n}", time_ms)

def benchmark_attention_mlx(seq_len: int, head_dim: int, iterations: int = 10) -> BenchResult:
    """Benchmark attention with MLX"""
    if not HAS_MLX:
        return BenchResult("Attention", "MLX", f"{seq_len}x{head_dim}", float('inf'), 0)

    Q = mx.random.uniform(shape=(seq_len, head_dim))
    K = mx.random.uniform(shape=(seq_len, head_dim))
    V = mx.random.uniform(shape=(seq_len, head_dim))
    scale = 1.0 / (head_dim ** 0.5)

    def attention(Q, K, V):
        scores = (Q @ K.T) * scale
        weights = mx.softmax(scores, axis=-1)
        return weights @ V

    # Warmup
    for _ in range(3):
        out = attention(Q, K, V)
        mx.eval(out)

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        out = attention(Q, K, V)
        mx.eval(out)
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    # Attention FLOPS: 2 * seq^2 * d (QK^T) + seq^2 (softmax) + 2 * seq^2 * d (scores @ V)
    flops = 4 * seq_len * seq_len * head_dim + seq_len * seq_len
    gflops = (flops / (time_ms / 1000)) / 1e9

    return BenchResult("Attention", "MLX", f"{seq_len}x{head_dim}", time_ms, gflops)

def benchmark_attention_torch(seq_len: int, head_dim: int, iterations: int = 10) -> BenchResult:
    """Benchmark attention with PyTorch MPS"""
    if not HAS_TORCH:
        return BenchResult("Attention", "PyTorch MPS", f"{seq_len}x{head_dim}", float('inf'), 0)

    device = torch.device("mps")
    Q = torch.randn(seq_len, head_dim, device=device, dtype=torch.float32)
    K = torch.randn(seq_len, head_dim, device=device, dtype=torch.float32)
    V = torch.randn(seq_len, head_dim, device=device, dtype=torch.float32)
    scale = 1.0 / (head_dim ** 0.5)

    def attention(Q, K, V):
        scores = torch.mm(Q, K.T) * scale
        weights = torch.softmax(scores, dim=-1)
        return torch.mm(weights, V)

    # Warmup
    for _ in range(3):
        out = attention(Q, K, V)
        torch.mps.synchronize()

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        out = attention(Q, K, V)
        torch.mps.synchronize()
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    flops = 4 * seq_len * seq_len * head_dim + seq_len * seq_len
    gflops = (flops / (time_ms / 1000)) / 1e9

    return BenchResult("Attention", "PyTorch MPS", f"{seq_len}x{head_dim}", time_ms, gflops)

def benchmark_reduce_mlx(n: int, iterations: int = 10) -> BenchResult:
    """Benchmark sum reduction with MLX"""
    if not HAS_MLX:
        return BenchResult("ReduceSum", "MLX", f"{n}", float('inf'), 0)

    x = mx.random.uniform(shape=(n,))

    # Warmup
    for _ in range(3):
        y = mx.sum(x)
        mx.eval(y)

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        y = mx.sum(x)
        mx.eval(y)
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    return BenchResult("ReduceSum", "MLX", f"{n}", time_ms)

def benchmark_reduce_torch(n: int, iterations: int = 10) -> BenchResult:
    """Benchmark sum reduction with PyTorch MPS"""
    if not HAS_TORCH:
        return BenchResult("ReduceSum", "PyTorch MPS", f"{n}", float('inf'), 0)

    device = torch.device("mps")
    x = torch.randn(n, device=device, dtype=torch.float32)

    # Warmup
    for _ in range(3):
        y = torch.sum(x)
        torch.mps.synchronize()

    # Timed runs
    start = time.perf_counter()
    for _ in range(iterations):
        y = torch.sum(x)
        torch.mps.synchronize()
    elapsed = time.perf_counter() - start

    time_ms = (elapsed / iterations) * 1000
    return BenchResult("ReduceSum", "PyTorch MPS", f"{n}", time_ms)

def print_header():
    print("=" * 70)
    print("     SciLean Metal vs MLX vs PyTorch Benchmark Suite")
    print("=" * 70)
    print()
    print(f"MLX available:     {HAS_MLX}")
    print(f"PyTorch MPS:       {HAS_TORCH}")
    print()

def print_section(title: str):
    print()
    print("-" * 70)
    print(f"  {title}")
    print("-" * 70)
    print(f"{'Backend':12} | {'Size':12} | {'Time':>10}    | GFLOP/s")
    print("-" * 70)

def run_benchmarks():
    print_header()

    # GEMM benchmarks
    gemm_sizes = [(512, 512, 512), (1024, 1024, 1024), (2048, 2048, 2048)]

    print_section("GEMM (C = A @ B)")
    for m, k, n in gemm_sizes:
        results = []
        if HAS_MLX:
            results.append(benchmark_gemm_mlx(m, k, n))
        if HAS_TORCH:
            results.append(benchmark_gemm_torch(m, k, n))
        for r in results:
            print(r)
        if results:
            print()

    # Softmax benchmarks
    softmax_sizes = [10000, 100000, 1000000]

    print_section("Softmax")
    for n in softmax_sizes:
        results = []
        if HAS_MLX:
            results.append(benchmark_softmax_mlx(n))
        if HAS_TORCH:
            results.append(benchmark_softmax_torch(n))
        for r in results:
            print(r)
        if results:
            print()

    # Attention benchmarks
    attention_sizes = [(128, 64), (256, 64), (512, 64)]

    print_section("Attention (single-head)")
    for seq_len, head_dim in attention_sizes:
        results = []
        if HAS_MLX:
            results.append(benchmark_attention_mlx(seq_len, head_dim))
        if HAS_TORCH:
            results.append(benchmark_attention_torch(seq_len, head_dim))
        for r in results:
            print(r)
        if results:
            print()

    # Reduction benchmarks
    reduce_sizes = [100000, 1000000, 10000000]

    print_section("ReduceSum")
    for n in reduce_sizes:
        results = []
        if HAS_MLX:
            results.append(benchmark_reduce_mlx(n))
        if HAS_TORCH:
            results.append(benchmark_reduce_torch(n))
        for r in results:
            print(r)
        if results:
            print()

    print()

    # Run SciLean benchmark if executable exists
    print("-" * 70)
    print("  SciLean Metal (from Lean executable)")
    print("-" * 70)

    scilean_exe = ".lake/build/bin/Float32Benchmark"
    try:
        import os
        if os.path.exists(scilean_exe):
            result = subprocess.run(
                [scilean_exe],
                capture_output=True, text=True, timeout=120
            )
            print(result.stdout)
            if result.returncode != 0:
                print(f"Error: {result.stderr}")
        else:
            print(f"Executable not found: {scilean_exe}")
            print("Build with: lake build Float32Benchmark")
    except Exception as e:
        print(f"Could not run SciLean benchmark: {e}")

    print()
    print("=" * 70)
    print("  Benchmark Complete")
    print("=" * 70)
    print()
    print("To compare directly:")
    print("  MLX/PyTorch: This script")
    print("  SciLean Metal: lake build Float32Benchmark && .lake/build/bin/Float32Benchmark")

if __name__ == "__main__":
    run_benchmarks()
