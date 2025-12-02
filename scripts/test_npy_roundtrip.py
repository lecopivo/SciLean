#!/usr/bin/env python3
"""
Test .npy roundtrip: Create arrays in Python, save, load in Lean, verify.
"""
import numpy as np
import os

os.makedirs("data/npy_test", exist_ok=True)

# Test 1: Simple 1D array
arr1d = np.array([1.0, 2.0, 3.0, 4.0, 5.0], dtype=np.float64)
np.save("data/npy_test/test_1d.npy", arr1d)
print(f"test_1d.npy: {arr1d}")
print(f"  dtype: {arr1d.dtype}, shape: {arr1d.shape}")
print(f"  sum: {arr1d.sum()}, mean: {arr1d.mean()}")

# Test 2: 2D matrix (3x4)
arr2d = np.arange(12.0, dtype=np.float64).reshape(3, 4)
np.save("data/npy_test/test_2d.npy", arr2d)
print(f"\ntest_2d.npy:\n{arr2d}")
print(f"  dtype: {arr2d.dtype}, shape: {arr2d.shape}")
print(f"  sum: {arr2d.sum()}")

# Test 3: Matrix-vector multiply test
# A @ x should give specific result
A = np.array([[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]], dtype=np.float64)  # 3x2
x = np.array([1.0, 2.0], dtype=np.float64)  # 2
y = A @ x  # Should be [5.0, 11.0, 17.0]
np.save("data/npy_test/test_A.npy", A)
np.save("data/npy_test/test_x.npy", x)
np.save("data/npy_test/test_y.npy", y)
print(f"\nMatrix-vector test:")
print(f"  A (3x2):\n{A}")
print(f"  x (2):\n{x}")
print(f"  y = A @ x (3):\n{y}")

# Test 4: Softmax test
logits = np.array([1.0, 2.0, 3.0, 4.0], dtype=np.float64)
# Stable softmax
exp_logits = np.exp(logits - logits.max())
softmax_out = exp_logits / exp_logits.sum()
np.save("data/npy_test/test_logits.npy", logits)
np.save("data/npy_test/test_softmax.npy", softmax_out)
print(f"\nSoftmax test:")
print(f"  logits: {logits}")
print(f"  softmax: {softmax_out}")
print(f"  sum (should be 1.0): {softmax_out.sum()}")

print("\n=== All test files created ===")
