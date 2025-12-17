#!/usr/bin/env python3
"""MLX MNIST benchmark - equivalent to GpuMNIST.lean"""

import mlx.core as mx
import mlx.nn as nn
import mlx.optimizers as optim
import numpy as np
import time
import struct

def load_mnist_images(path, num_samples):
    """Load MNIST images (same format as Lean version)"""
    with open(path, 'rb') as f:
        magic, n, rows, cols = struct.unpack('>IIII', f.read(16))
        data = np.frombuffer(f.read(num_samples * 784), dtype=np.uint8)
        data = data.reshape(num_samples, 784).astype(np.float32) / 255.0
    return mx.array(data)

def load_mnist_labels(path, num_samples):
    """Load MNIST labels as one-hot"""
    with open(path, 'rb') as f:
        magic, n = struct.unpack('>II', f.read(8))
        labels = np.frombuffer(f.read(num_samples), dtype=np.uint8)
    # One-hot encode
    one_hot = np.zeros((num_samples, 10), dtype=np.float32)
    one_hot[np.arange(num_samples), labels] = 1.0
    return mx.array(one_hot)

class SimpleMLP(nn.Module):
    """2-layer MLP matching GpuMNIST.lean architecture"""
    def __init__(self):
        super().__init__()
        self.w1 = mx.random.normal((784, 128)) * np.sqrt(2.0 / 784)
        self.b1 = mx.zeros((128,))
        self.w2 = mx.random.normal((128, 10)) * np.sqrt(2.0 / 128)
        self.b2 = mx.zeros((10,))

    def __call__(self, x):
        # Hidden layer with GELU
        h = mx.matmul(x, self.w1) + self.b1
        h = nn.gelu(h)
        # Output layer with softmax
        o = mx.matmul(h, self.w2) + self.b2
        return mx.softmax(o, axis=-1)

def cross_entropy_loss(pred, target):
    """Cross-entropy loss"""
    return -mx.mean(mx.sum(target * mx.log(pred + 1e-7), axis=1))

def accuracy(pred, target):
    """Compute accuracy"""
    pred_labels = mx.argmax(pred, axis=1)
    true_labels = mx.argmax(target, axis=1)
    return mx.mean(pred_labels == true_labels).item()

def main():
    print("MLX MNIST Benchmark")
    print("=" * 40)

    # Configuration (matching GpuMNIST.lean)
    num_train = 1000  # Using batch of 1000 (same as Lean)
    epochs = 50
    lr = 0.0005 * num_train  # Effective lr (MLX averages gradients)

    # Load data
    print("Loading data...")
    images = load_mnist_images("data/train-images-idx3-ubyte", num_train)
    labels = load_mnist_labels("data/train-labels-idx1-ubyte", num_train)

    # Initialize model
    model = SimpleMLP()

    # Manual SGD (to match Lean implementation)
    def loss_fn(model, x, y):
        pred = model(x)
        return cross_entropy_loss(pred, y)

    loss_and_grad = mx.value_and_grad(loss_fn)

    # Initial accuracy
    init_pred = model(images)
    mx.eval(init_pred)
    init_acc = accuracy(init_pred, labels)
    print(f"Initial accuracy: {init_acc * 100:.1f}%\n")

    print("Training...")
    for epoch in range(epochs):
        start = time.perf_counter()

        # Forward and backward
        loss, grads = loss_and_grad(model, images, labels)

        # Manual SGD update
        model.w1 = model.w1 - lr * grads["w1"]
        model.b1 = model.b1 - lr * grads["b1"]
        model.w2 = model.w2 - lr * grads["w2"]
        model.b2 = model.b2 - lr * grads["b2"]

        # Compute accuracy
        pred = model(images)
        mx.eval(pred)  # Force evaluation
        acc = accuracy(pred, labels)

        elapsed = (time.perf_counter() - start) * 1000
        print(f"Epoch {epoch + 1}: accuracy = {acc * 100:.1f}%, time = {elapsed:.1f}ms")

    # Final accuracy
    final_pred = model(images)
    mx.eval(final_pred)
    final_acc = accuracy(final_pred, labels)
    print(f"\nFinal accuracy: {final_acc * 100:.1f}%")

if __name__ == "__main__":
    main()
