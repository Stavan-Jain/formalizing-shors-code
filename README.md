# Shor’s Code in Lean

This project formalizes foundational concepts in quantum error correction using the Lean 4 proof assistant, building toward a complete formalization of **Shor’s 9-qubit error-correcting code**.

Along the way, it develops **definitions and lemmas** for reasoning about qubits, quantum states, and unitary operations.

## Overview

The repository is structured into modules that gradually build up to the formalization of quantum error correction.  
Each module is written in Lean 4 and relies on `mathlib`.

## Project Structure

| Path | Description |
|------|--------------|
| `ShorsCode/Foundations/Basic.lean` | Core definitions for qubits, quantum states, and supporting lemmas. |
| `ShorsCode/Foundations/Gates.lean` | Concrete implementations of single-qubit gates (Pauli matrices, Hadamard, etc.). |
| `ShorsCode/Foundations/Tensor.lean` | Tensor product utilities and proofs for composite systems (in progress). |
| `lakefile.toml` | Lake configuration specifying dependencies and namespaces. |

## Getting Started

### Prerequisites
- [Lean 4](https://lean-lang.org/) (≥ 4.8)
- `lake` build tool (bundled with Lean)


## Contributing

Contributions are welcome.  
If you add new modules or definitions, please:

1. Expose them through `lakefile.toml` or the umbrella module (`ShorsCode.lean`).
2. Update this README’s **Project Structure** section.
3. Follow Lean’s [style guide](https://leanprover-community.github.io/style-guide.html) and document key definitions.


## Long-Term Goal

This repository aims to:
- Provide a verified foundation for quantum error correction in Lean.  
- Bridge quantum computing and formal methods, enabling mechanized reasoning about quantum circuits.  
- Serve as a pedagogical resource for learning quantum theory through formal proof.

