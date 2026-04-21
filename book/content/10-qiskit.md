# Quantum programming with Qiskit

```{note}
**Chapter roles (Spring 2026)**
Author: Nataniel Farzan · Reviewer: Ethan Tapia
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **Qiskit** for designing and running quantum circuits (simulation or hardware where available).

## Goals

- Give just enough quantum computing background to read a short circuit.
- Show a runnable Qiskit example with measurement and interpretation of results.
- Explore a further aspect depending on your interest.
- Link to IBM Qiskit documentation, textbooks, and simulators.

## Draft

### Introduction

### A Simple Quantum Circuit

The following code snippet represents a Bell state (two entangled qubits):

```python
qc = QuantumCircuit(2)  # Instantiate a quantum circuit with 2 qubits
qc.h(0)                 # Apply a Hadamard gate
qc.cx(0, 1)             # Apply a Controlled-X gate
```

### References & Resources

- [Qiskit Quickstart](https://quantum.cloud.ibm.com/docs/en/guides/quick-start)
- [Qiskit Circuit Library](https://quantum.cloud.ibm.com/docs/en/api/qiskit/circuit_library)
- [Qiskit Code Assistant (VS Code Extension)](https://github.com/Qiskit/qiskit-code-assistant-vscode)
