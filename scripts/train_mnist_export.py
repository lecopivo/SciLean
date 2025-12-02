#!/usr/bin/env python3
"""
Train a small MNIST classifier and export weights/test cases for Lean verification.

Architecture: 784 → 128 (ReLU) → 10 (softmax)
"""
import numpy as np
import torch
import torch.nn as nn
import torch.optim as optim
from torchvision import datasets, transforms
import os

# Reproducibility
torch.manual_seed(42)
np.random.seed(42)

# Create output directory
os.makedirs("data/mnist_weights", exist_ok=True)

# Simple 2-layer MLP
class SimpleMLP(nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(784, 128)
        self.fc2 = nn.Linear(128, 10)

    def forward(self, x):
        x = x.view(-1, 784)
        x = torch.relu(self.fc1(x))
        x = self.fc2(x)
        return x

    def forward_with_intermediates(self, x):
        """Return intermediate values for debugging"""
        x = x.view(-1, 784)
        h = self.fc1(x)
        h_relu = torch.relu(h)
        logits = self.fc2(h_relu)
        return h, h_relu, logits

# Load MNIST
transform = transforms.Compose([
    transforms.ToTensor(),
    transforms.Normalize((0.1307,), (0.3081,))
])

print("Loading MNIST dataset...")
train_dataset = datasets.MNIST('data', train=True, download=True, transform=transform)
test_dataset = datasets.MNIST('data', train=False, transform=transform)

train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=64, shuffle=True)
test_loader = torch.utils.data.DataLoader(test_dataset, batch_size=1000, shuffle=False)

# Train model
model = SimpleMLP()
criterion = nn.CrossEntropyLoss()
optimizer = optim.Adam(model.parameters(), lr=0.001)

print("Training model...")
epochs = 3
for epoch in range(epochs):
    model.train()
    total_loss = 0
    correct = 0
    total = 0

    for batch_idx, (data, target) in enumerate(train_loader):
        optimizer.zero_grad()
        output = model(data)
        loss = criterion(output, target)
        loss.backward()
        optimizer.step()

        total_loss += loss.item()
        pred = output.argmax(dim=1)
        correct += pred.eq(target).sum().item()
        total += target.size(0)

    train_acc = 100. * correct / total
    print(f"Epoch {epoch+1}/{epochs}: Loss={total_loss/len(train_loader):.4f}, Train Acc={train_acc:.2f}%")

# Evaluate
model.eval()
correct = 0
total = 0
with torch.no_grad():
    for data, target in test_loader:
        output = model(data)
        pred = output.argmax(dim=1)
        correct += pred.eq(target).sum().item()
        total += target.size(0)

test_acc = 100. * correct / total
print(f"\nTest Accuracy: {test_acc:.2f}%")

# Export weights as .npy
print("\nExporting weights...")
w1 = model.fc1.weight.detach().numpy()  # Shape: [128, 784]
b1 = model.fc1.bias.detach().numpy()    # Shape: [128]
w2 = model.fc2.weight.detach().numpy()  # Shape: [10, 128]
b2 = model.fc2.bias.detach().numpy()    # Shape: [10]

np.save("data/mnist_weights/w1.npy", w1.astype(np.float64))
np.save("data/mnist_weights/b1.npy", b1.astype(np.float64))
np.save("data/mnist_weights/w2.npy", w2.astype(np.float64))
np.save("data/mnist_weights/b2.npy", b2.astype(np.float64))

print(f"  w1: {w1.shape} → data/mnist_weights/w1.npy")
print(f"  b1: {b1.shape} → data/mnist_weights/b1.npy")
print(f"  w2: {w2.shape} → data/mnist_weights/w2.npy")
print(f"  b2: {b2.shape} → data/mnist_weights/b2.npy")

# Export test cases for verification
print("\nExporting test cases...")
test_iter = iter(test_loader)
test_data, test_labels = next(test_iter)

# Take first 10 samples for verification
num_test = 10
test_images = test_data[:num_test].numpy().reshape(num_test, 784)
test_targets = test_labels[:num_test].numpy()

# Compute expected outputs
model.eval()
with torch.no_grad():
    test_batch = test_data[:num_test]
    h, h_relu, logits = model.forward_with_intermediates(test_batch)
    probs = torch.softmax(logits, dim=1)
    preds = logits.argmax(dim=1)

np.save("data/mnist_weights/test_images.npy", test_images.astype(np.float64))
np.save("data/mnist_weights/test_labels.npy", test_targets.astype(np.int64))
np.save("data/mnist_weights/test_hidden.npy", h.numpy().astype(np.float64))
np.save("data/mnist_weights/test_hidden_relu.npy", h_relu.numpy().astype(np.float64))
np.save("data/mnist_weights/test_logits.npy", logits.numpy().astype(np.float64))
np.save("data/mnist_weights/test_probs.npy", probs.numpy().astype(np.float64))
np.save("data/mnist_weights/test_preds.npy", preds.numpy().astype(np.int64))

print(f"  test_images: {test_images.shape}")
print(f"  test_labels: {test_targets.shape}")
print(f"  test_hidden: {h.shape}")
print(f"  test_hidden_relu: {h_relu.shape}")
print(f"  test_logits: {logits.shape}")
print(f"  test_probs: {probs.shape}")
print(f"  test_preds: {preds.shape}")

# Print first few predictions for manual verification
print("\nFirst 10 test predictions:")
for i in range(num_test):
    print(f"  Image {i}: label={test_targets[i]}, pred={preds[i].item()}, "
          f"correct={'✓' if test_targets[i] == preds[i].item() else '✗'}")

# Save metadata
metadata = {
    'architecture': '784 -> 128 (ReLU) -> 10',
    'test_accuracy': test_acc,
    'num_test_samples': num_test,
    'normalization': {'mean': 0.1307, 'std': 0.3081}
}
import json
with open("data/mnist_weights/metadata.json", "w") as f:
    json.dump(metadata, f, indent=2)

print("\n=== Export complete ===")
print(f"Test accuracy: {test_acc:.2f}%")
print("Files saved to data/mnist_weights/")
