#!/bin/bash
# Setup script for testing SciLean CUDA on cloud GPU (Vast.ai, RunPod, Lambda, etc.)
#
# Usage:
#   # On cloud GPU with SSH access:
#   git clone https://github.com/YOUR_USER/SciLean.git
#   cd SciLean
#   bash CUDA/setup_cloud_gpu.sh
#
# Prerequisites:
#   - CUDA toolkit (usually pre-installed on GPU instances)
#   - git, curl, gcc/g++

set -e

echo "=== SciLean CUDA Setup ==="

# 1. Check CUDA
echo "[1/5] Checking CUDA..."
if ! command -v nvcc &> /dev/null; then
    echo "ERROR: nvcc not found. Install CUDA toolkit."
    exit 1
fi
nvcc --version
nvidia-smi

# 2. Install elan (Lean version manager)
echo "[2/5] Installing elan..."
if ! command -v elan &> /dev/null; then
    curl https://elan.lean-lang.org/install.sh -sSf | sh -s -- -y
    export PATH="$HOME/.elan/bin:$PATH"
fi
elan --version

# 3. Setup Lean toolchain
echo "[3/5] Setting up Lean toolchain..."
cd "$(dirname "$0")/.."  # Go to SciLean root
elan override set leanprover/lean4:v4.26.0-rc2

# 4. Build CUDA FFI library
echo "[4/5] Building CUDA FFI library..."
cd CUDA

# Get Lean include directory
LEAN_INCLUDE=$(lean --print-prefix)/include

# Compile CUDA backend
nvcc -shared -fPIC -O3 \
    -I"$LEAN_INCLUDE" \
    -o libscileancuda.so \
    cuda_backend.cu \
    -lcublas -lcuda

# Copy to library path
mkdir -p ../.lake/build/lib
cp libscileancuda.so ../.lake/build/lib/

echo "Built: libscileancuda.so"

# 5. Build test executable
echo "[5/5] Building CUDA test..."
cd ..

# Create minimal test file
cat > examples/CUDATest.lean << 'EOF'
import SciLean.FFI.CUDA

open SciLean

def main : IO Unit := do
  IO.println "=== SciLean CUDA Test ==="

  -- Check availability
  let available := CUDA.isAvailable ()
  IO.println s!"CUDA available: {available}"

  if available then
    let name := CUDA.deviceName ()
    IO.println s!"Device: {name}"

    -- Test GEMM
    IO.println "\nTesting GEMM 1024×1024..."

    -- Create test matrices (identity-ish for verification)
    let n : USize := 1024
    let size := n * n * 4  -- Float32 = 4 bytes

    -- A = ones, B = ones → C should have all elements = 1024
    let A := ByteArray.mk (Array.mkArray size.toNat 0x3F) -- ~1.0 in float
    let B := ByteArray.mk (Array.mkArray size.toNat 0x3F)

    -- Warm up
    let _ := CUDA.gemmTiled n n n A B
    let _ := CUDA.gemmCuBLAS n n n A B

    -- Benchmark tiled
    let startTiled ← IO.monoMsNow
    for _ in [0:10] do
      let _ := CUDA.gemmTiled n n n A B
    let endTiled ← IO.monoMsNow
    let tiledMs := (endTiled - startTiled).toFloat / 10.0

    -- Benchmark cuBLAS
    let startCublas ← IO.monoMsNow
    for _ in [0:10] do
      let _ := CUDA.gemmCuBLAS n n n A B
    let endCublas ← IO.monoMsNow
    let cublasMs := (endCublas - startCublas).toFloat / 10.0

    -- Calculate GFLOP/s (2 * M * N * K operations for GEMM)
    let gflops := 2.0 * 1024.0 * 1024.0 * 1024.0 / 1e9
    let tiledGflops := gflops / (tiledMs / 1000.0)
    let cublasGflops := gflops / (cublasMs / 1000.0)

    IO.println s!"  Tiled:  {tiledMs}ms ({tiledGflops} GFLOP/s)"
    IO.println s!"  cuBLAS: {cublasMs}ms ({cublasGflops} GFLOP/s)"

  IO.println "\nDone!"
EOF

# Add CUDA lib target to lakefile (if not present)
if ! grep -q "libscileancuda" lakefile.lean; then
    echo "
-- CUDA backend (Linux only)
target libscileancuda pkg : FilePath := do
  if System.Platform.isWindows || System.Platform.isOSX then
    -- Return dummy on non-Linux
    let name := nameToStaticLib \"scileancuda_dummy\"
    return pkg.sharedLibDir / name
  else
    -- On Linux, expect pre-built library
    return pkg.dir / \"CUDA\" / \"libscileancuda.so\"

lean_lib SciLean.FFI.CUDA where
  roots := #[\`SciLean.FFI.CUDA]
  precompileModules := false
  moreLinkObjs := #[libscileancuda]

lean_exe CUDATest where
  root := \`examples.CUDATest
  moreLinkArgs := #[\"-L\", \"CUDA\", \"-lscileancuda\", \"-lcublas\", \"-lcuda\"]
" >> lakefile.lean
fi

# Build
lake build CUDATest

echo ""
echo "=== Setup complete! ==="
echo "Run: ./.lake/build/bin/CUDATest"
