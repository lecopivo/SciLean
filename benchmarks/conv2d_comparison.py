#!/usr/bin/env python3
"""
Conv2D Benchmark: SciLean Metal vs MLX vs PyTorch MPS

Run: uv run benchmarks/conv2d_comparison.py
"""

import time
import subprocess
import os

try:
    import mlx.core as mx
    import mlx.nn as nn
    HAS_MLX = True
except ImportError:
    HAS_MLX = False
    print("Warning: MLX not installed")

try:
    import torch
    import torch.nn.functional as F
    HAS_TORCH = torch.backends.mps.is_available()
except ImportError:
    HAS_TORCH = False
    print("Warning: PyTorch not installed")

def benchmark_conv2d_mlx(batch, in_c, out_c, h, w, kernel_size=3, iterations=100):
    """Benchmark Conv2D with MLX"""
    if not HAS_MLX:
        return float('inf')

    # Create input and conv layer
    x = mx.random.uniform(shape=(batch, h, w, in_c))  # MLX uses NHWC
    conv = nn.Conv2d(in_c, out_c, kernel_size=kernel_size, padding=kernel_size//2)

    # Warmup
    for _ in range(3):
        y = conv(x)
        mx.eval(y)

    # Timed
    start = time.perf_counter()
    for _ in range(iterations):
        y = conv(x)
        mx.eval(y)
    elapsed = time.perf_counter() - start

    return (elapsed / iterations) * 1000  # ms

def benchmark_conv2d_torch(batch, in_c, out_c, h, w, kernel_size=3, iterations=100):
    """Benchmark Conv2D with PyTorch MPS"""
    if not HAS_TORCH:
        return float('inf')

    device = torch.device("mps")
    x = torch.randn(batch, in_c, h, w, device=device, dtype=torch.float32)
    weight = torch.randn(out_c, in_c, kernel_size, kernel_size, device=device, dtype=torch.float32)
    bias = torch.randn(out_c, device=device, dtype=torch.float32)

    # Warmup
    for _ in range(3):
        y = F.conv2d(x, weight, bias, padding=kernel_size//2)
        torch.mps.synchronize()

    # Timed
    start = time.perf_counter()
    for _ in range(iterations):
        y = F.conv2d(x, weight, bias, padding=kernel_size//2)
        torch.mps.synchronize()
    elapsed = time.perf_counter() - start

    return (elapsed / iterations) * 1000  # ms

def benchmark_maxpool_mlx(batch, channels, h, w, pool_size=2, iterations=100):
    """Benchmark MaxPool2D with MLX"""
    if not HAS_MLX:
        return float('inf')

    x = mx.random.uniform(shape=(batch, h, w, channels))  # NHWC
    pool = nn.MaxPool2d(kernel_size=pool_size, stride=pool_size)

    # Warmup
    for _ in range(3):
        y = pool(x)
        mx.eval(y)

    # Timed
    start = time.perf_counter()
    for _ in range(iterations):
        y = pool(x)
        mx.eval(y)
    elapsed = time.perf_counter() - start

    return (elapsed / iterations) * 1000

def benchmark_maxpool_torch(batch, channels, h, w, pool_size=2, iterations=100):
    """Benchmark MaxPool2D with PyTorch MPS"""
    if not HAS_TORCH:
        return float('inf')

    device = torch.device("mps")
    x = torch.randn(batch, channels, h, w, device=device, dtype=torch.float32)

    # Warmup
    for _ in range(3):
        y = F.max_pool2d(x, kernel_size=pool_size, stride=pool_size)
        torch.mps.synchronize()

    # Timed
    start = time.perf_counter()
    for _ in range(iterations):
        y = F.max_pool2d(x, kernel_size=pool_size, stride=pool_size)
        torch.mps.synchronize()
    elapsed = time.perf_counter() - start

    return (elapsed / iterations) * 1000

def compute_conv_gflops(batch, in_c, out_c, h, w, kernel_size, time_ms):
    """Compute GFLOP/s for Conv2D"""
    out_h = h  # same padding
    out_w = w
    flops = 2 * batch * out_h * out_w * out_c * in_c * kernel_size * kernel_size
    if time_ms > 0.001:
        return (flops / (time_ms / 1000)) / 1e9
    return 0

def main():
    print("=" * 70)
    print("     Conv2D Benchmark: SciLean Metal vs MLX vs PyTorch MPS")
    print("=" * 70)
    print()
    print(f"MLX available:     {HAS_MLX}")
    print(f"PyTorch MPS:       {HAS_TORCH}")
    print()

    # Conv2D benchmarks
    configs = [
        (1, 1, 32, 28, 28, 3),    # MNIST first conv
        (1, 32, 64, 28, 28, 3),   # MNIST second conv
        (1, 64, 128, 14, 14, 3),  # After pooling
        (1, 3, 64, 224, 224, 3),  # ResNet first conv
        (1, 64, 128, 56, 56, 3),  # ResNet deeper
        (1, 128, 256, 28, 28, 3), # ResNet deeper
    ]

    print("-" * 70)
    print("  Conv2D 3x3 (same padding)")
    print("-" * 70)
    print(f"{'Config':<25} | {'MLX':>10} | {'PyTorch':>10} | {'MLX GFLOP/s':>12} | {'Torch GFLOP/s':>12}")
    print("-" * 70)

    for batch, in_c, out_c, h, w, k in configs:
        mlx_ms = benchmark_conv2d_mlx(batch, in_c, out_c, h, w, k)
        torch_ms = benchmark_conv2d_torch(batch, in_c, out_c, h, w, k)

        mlx_gflops = compute_conv_gflops(batch, in_c, out_c, h, w, k, mlx_ms)
        torch_gflops = compute_conv_gflops(batch, in_c, out_c, h, w, k, torch_ms)

        config_str = f"{h}x{w} x{in_c}→{out_c}"
        print(f"{config_str:<25} | {mlx_ms:>8.3f}ms | {torch_ms:>8.3f}ms | {mlx_gflops:>10.1f} | {torch_gflops:>10.1f}")

    print()

    # MaxPool benchmarks
    pool_configs = [
        (1, 32, 28, 28),
        (1, 64, 14, 14),
        (1, 128, 7, 7),
    ]

    print("-" * 70)
    print("  MaxPool2D 2x2, stride 2")
    print("-" * 70)
    print(f"{'Config':<25} | {'MLX':>10} | {'PyTorch':>10}")
    print("-" * 70)

    for batch, c, h, w in pool_configs:
        mlx_ms = benchmark_maxpool_mlx(batch, c, h, w)
        torch_ms = benchmark_maxpool_torch(batch, c, h, w)

        config_str = f"{h}x{w} x{c}"
        print(f"{config_str:<25} | {mlx_ms:>8.3f}ms | {torch_ms:>8.3f}ms")

    print()
    print("=" * 70)
    print("  SciLean Metal Results (from Lean executable)")
    print("=" * 70)

    # Run SciLean benchmark
    scilean_exe = ".lake/build/bin/Conv2DTest"
    if os.path.exists(scilean_exe):
        result = subprocess.run([scilean_exe], capture_output=True, text=True, timeout=60)
        # Extract benchmark section
        in_bench = False
        for line in result.stdout.split('\n'):
            if 'BENCHMARK' in line:
                in_bench = True
            if in_bench:
                print(line)
            if 'Test complete' in line:
                break
        print()
        print("Note: 'Fast' uses optimized 3x3 kernel with unrolled loops")
    else:
        print(f"Executable not found: {scilean_exe}")
        print("Build with: lake build Conv2DTest")

    print()
    print("=" * 70)
    print("  Comparison Summary")
    print("=" * 70)
    print()
    print("Note: SciLean uses NCHW format, MLX uses NHWC format")
    print("Lower time is better. Higher GFLOP/s is better.")

if __name__ == "__main__":
    main()
