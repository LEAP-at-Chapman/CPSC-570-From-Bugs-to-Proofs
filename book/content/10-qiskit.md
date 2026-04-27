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

Qiskit is a Python library developed by IBM for interacting with quantum computers.

### Background

#### Classical Computing

The fundamental unit of information in classical computing systems is the bit (binary digit), which can represent either 0 or 1. Depending on the underlying physical medium, bits can be represented in a variety of ways: electrical charge, magnetization, light intensity, etc. Bits are used to store data and perform logical operations that modify the state of the system. Logic gates perform operations on one or more binary inputs to produce a single output. Common logic gates include AND, OR, and NOT gates. These operations can be modeled using boolean algebra to design complex logic circuits that perform desired functions.

Gordon Moore, the co-founder and former CEO of Intel, famously predicted that the number of transistors in integrated circuits would double roughly every two years (a prediction that would later be known as Moore's law). This rule of thumb has held for several decades, but we are approaching the physical limits to how small transistors can be. Therefore, a new architectural approach is needed to move beyond Moore’s Law and build upon many-core architectures.

#### Quantum Theory

Our physical world is governed by the fundamental laws of physics. While classical physics can be used to describe pheneomena at macroscopic and microscopic scales, quantum physics models submicroscopic and subatomic properties. A foundational understanding in quantum theory is required to explain electromagnetism, the strong force, the weak force, and gravity.

#### Quantum Computing

##### Qubits

The basic unit of information in quantum computing systems is the qubit (quantum bit). Unlike a classical bit, which exists in exactly one of two possible states, a qubit can be in an arbitrary superposition of all computable states simultaneously. Quantum computers are fundamentally different from classical computers because they can act on every state in the superposition at once. While it is possible to represent qubits classically, as the size of the system grows, quantum computers become extremely difficult to simulate with a classical computer. Qubits can be represented by a linear combination of two basis vectors: $| 0 \rangle ={\bigl [}{\begin{smallmatrix}1\\0\end{smallmatrix}}{\bigr ]}$ and $| 1 \rangle ={\bigl [}{\begin{smallmatrix}0\\1\end{smallmatrix}}{\bigr ]}$. Therefore, the state of a qubit is a vector in a two-dimensional vector space, which is known as the state space.

> The conventional notation used to represent qubits is known as **bra-ket notation** or **Dirac notation**. A **ket** (column vector) is of the form $| v \rangle$ and represents a quantum states, while a **bra** (row vector) is of the form $\langle f |$ and corresponds to the complex conjugate transpose of a ket. While it is convention to use bra-ket notation to describe quantum states as elements of a complex Hilbert space, the underlying representation is always two-dimensional row and column vectors. $| \psi \rangle$ is often used to denote an arbitrary quantum state.

The two orthonormal basis states, $| 0 \rangle$ and $| 1 \rangle$, form the computation basis that span the two-dimensional linear vector space of the qubit. Therefore, all possible qubit states can be described by a linear combination of these two states: $| \psi \rangle = \alpha | 0 \rangle + \beta | 1 \rangle$.

##### Quantum Gates

Quantum gates perform logical operations on qubits.

### Qiskit

#### A Simple Quantum Circuit

The following code snippet represents a Bell state (two entangled qubits):

```python
qc = QuantumCircuit(2)  # Instantiate a quantum circuit with 2 qubits
qc.h(0)                 # Apply a Hadamard gate
qc.cx(0, 1)             # Apply a Controlled-X gate
```

### References & Resources

#### Qiskit

- [Quickstart](https://quantum.cloud.ibm.com/docs/en/guides/quick-start)
- [Circuit Library](https://quantum.cloud.ibm.com/docs/en/api/qiskit/circuit_library)
- [GitHub repository](https://github.com/Qiskit/qiskit)
- [VS Code Extension](https://github.com/Qiskit/qiskit-code-assistant-vscode)

#### Quantum Theory

- [Quantum mechanics](https://en.wikipedia.org/wiki/Quantum_mechanics)

#### Quantum Computing

- [Qubit](https://en.wikipedia.org/wiki/Qubit)
- [Quantum.country](https://quantum.country/qcvc)
- [Bra-ket notation](https://en.wikipedia.org/wiki/Bra%E2%80%93ket_notation)

#### Classical Computing

- [Bit](https://en.wikipedia.org/wiki/Bit)
- [Logic gate](https://en.wikipedia.org/wiki/Logic_gate)
- [Moore's law](https://en.wikipedia.org/wiki/Moore%27s_law)
