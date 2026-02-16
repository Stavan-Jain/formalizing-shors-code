# Quantum Error Correction in Lean

This project formalizes foundational concepts in quantum error correction using the Lean 4 proof assistant, with the goal of a complete formalization of Stabilizer Codes.

Along the way, it develops **definitions and lemmas** for reasoning about qubits, quantum states, and unitary operations, providing a verified foundation for quantum computing in Lean.

## Overview

Modules are written in Lean 4 and rely on [mathlib](https://github.com/leanprover-community/mathlib4) for linear algebra and other foundations. Import everything via `QEC`, or use `QEC.Foundations`, `QEC.RepetitionCode`, or `QEC.Stabilizer` for a subset.

### Features

- **Foundational Quantum Computing**: Core definitions for qubits, quantum states, vectors, and norms
- **Quantum Gates**: Formalized implementations of single-qubit gates (Pauli matrices, Hadamard, phase gates, etc.)
- **Tensor Products**: Utilities and proofs for composite quantum systems
- **Repetition Code**: Complete formalization of the 3-qubit bit-flip error correction code (encode/decode, logical X, recovery)
- **Stabilizer Formalism**: Single-qubit and n-qubit Pauli groups, commutation (including tactics), matrix representations, stabilizer groups, CSS structure, centralizer, and logical operators
- **Binary Symplectic Representation**: Check matrices, symplectic inner product, symplectic span, and equivalence with independent generators
- **Concrete Codes**: 3-qubit repetition code (Z-stabilizer), n-qubit repetition code, Steane 7-qubit code, and Shor 9-qubit code
- **Verified Properties**: Mechanized proofs of correctness for encoding, decoding, recovery, and stabilizer/subgroup properties

## Project Structure

Import the whole development via `QEC` (or `QEC.Foundations`, `QEC.RepetitionCode`, `QEC.Stabilizer`). The code is organized as:

- **`QEC/Foundations/`** — Qubits, quantum states, gates (including CNOT), and tensor products.
- **`QEC/RepetitionCode/`** — 3-qubit bit-flip code: encode/decode, logical X, and recovery with proofs.
- **`QEC/Stabilizer/`** — Pauli groups (single- and n-qubit), binary symplectic representation (check matrices, symplectic span), stabilizer core (groups, CSS, centralizer, logical operators), and concrete codes: repetition (3- and n-qubit), Steane 7, Shor 9.

## Getting Started

### Prerequisites

- [Lean 4](https://lean-lang.org/) (this repo uses `leanprover/lean4:v4.24.0-rc1`; see `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (bundled with Lean) and mathlib (pulled automatically by Lake)

### Building

```bash
git clone <repository-url>
cd QuantumErrorCorrectionLean
lake build
```

### Working with the Code

- Open files in your Lean 4 editor (VS Code with the Lean extension, or Emacs with lean4-mode)
- Use `#check` and `#eval` commands in Lean to explore definitions
- Run `lake build` after making changes to verify your code compiles

## Contributing

Contributions are welcome! If you add new modules or definitions, please:

1. **Expose modules** through `lakefile.toml` or the umbrella module (`QEC.lean`)
2. **Update this README** if you add or rename top-level modules
3. **Follow Lean's [style guide](https://leanprover-community.github.io/style-guide.html)** and document key definitions with docstrings
4. **Add proofs** for important properties and lemmas
5. **Ensure code compiles** with `lake build`

### Code Style

- Use the `Quantum` namespace for quantum-specific definitions
- Document definitions with `/-- ... -/` docstrings (Lean doc comments)
- Use `@[simp]` attributes for lemmas that should be used by the simplifier
- Follow mathlib conventions for naming and structure

## Long-Term Goals

This repository aims to:

- Provide a verified foundation for quantum error correction in Lean
- Bridge quantum computing and formal methods, enabling mechanized reasoning about quantum circuits
- Serve as a pedagogical resource for learning quantum theory through formal proof
- Deepen the formalizations of **Shor's 9-qubit** and **Steane 7-qubit** codes (structure and proofs)
- Extend to further codes (e.g. surface codes) and verified syndrome decoding
- Develop verified quantum algorithms and protocols

## Acknowledgments

Built using [Lean 4](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4).
