# Quantum Error Correction in Lean

This project formalizes foundational concepts in quantum error correction using the Lean 4 proof assistant, with the goal of a complete formalization of Stabilizer Codes.

Along the way, it develops **definitions and lemmas** for reasoning about qubits, quantum states, and unitary operations, providing a verified foundation for quantum computing in Lean.

## Overview

The repository is structured into modules that gradually build up to the formalization of quantum error correction. Each module is written in Lean 4 and relies on `mathlib` for foundational mathematical structures.

### Features

- **Foundational Quantum Computing**: Core definitions for qubits, quantum states, vectors, and norms
- **Quantum Gates**: Formalized implementations of single-qubit gates (Pauli matrices, Hadamard, phase gates, etc.)
- **Tensor Products**: Utilities and proofs for composite quantum systems
- **Repetition Code**: Complete formalization of the 3-qubit bit-flip error correction code
- **Stabilizer Formalism**: Pauli group structures and phase associativity proofs
- **Verified Properties**: Mechanized proofs of correctness for encoding, decoding, and recovery operations

## Project Structure

### Foundations

| Path | Description |
|------|-------------|
| `ShorsCode/Foundations/basic.lean` | Core definitions for qubits, quantum states (`QuantumState`), vectors (`Vector`), norms, and basis states (`ket0`, `ket1`, `ket000`, `ket111`). |
| `ShorsCode/Foundations/gates.lean` | Concrete implementations of quantum gates including Pauli matrices (X, Y, Z), Hadamard, phase gates, and custom tactics (`matrix_expand`, `vec_expand`) for working with quantum operations. |
| `ShorsCode/Foundations/tensor.lean` | Tensor product utilities and proofs for composite quantum systems, enabling reasoning about multi-qubit states. |

### Repetition Code

| Path | Description |
|------|-------------|
| `ShorsCode/RepetitionCode/EncodeDecode.lean` | Semantic encode/decode maps between 1-qubit vectors/states and the 3-qubit repetition-code subspace, with proofs of norm preservation. |
| `ShorsCode/RepetitionCode/LogicalX.lean` | Implementation and verification of logical X operations on encoded qubits. |
| `ShorsCode/RepetitionCode/Recovery.lean` | Recovery operations using majority vote decoding, with proofs of correctness for error correction. |

### Stabilizer Formalism

| Path | Description |
|------|-------------|
| `ShorsCode/Stabilizer/PauliGroup.lean` | Formalization of the Pauli group, including phase associativity proofs and custom tactics (`pauli_phase_assoc_cases`) for exhaustive case analysis. |

## Getting Started

### Prerequisites

- [Lean 4](https://lean-lang.org/) (v4.24.0-rc1 or compatible)
- `lake` build tool (bundled with Lean)
- `mathlib` (automatically managed by Lake)

### Building the Project

1. **Clone the repository** (if you haven't already):
   ```bash
   git clone <repository-url>
   cd ShorsCode
   ```

2. **Build the project**:
   ```bash
   lake build
   ```

3. **Verify everything compiles**:
   ```bash
   lake build ShorsCode
   ```

### Working with the Code

- Open files in your Lean 4 editor (VS Code with the Lean extension, or Emacs with lean4-mode)
- Use `#check` and `#eval` commands in Lean to explore definitions
- Run `lake build` after making changes to verify your code compiles

## Dependencies

- **mathlib**: The Lean mathematical library, providing linear algebra, complex numbers, and other foundational structures
- Managed automatically via `lakefile.toml`

## Contributing

Contributions are welcome! If you add new modules or definitions, please:

1. **Expose modules** through `lakefile.toml` or the umbrella module (`ShorsCode.lean`)
2. **Update this README**'s **Project Structure** section
3. **Follow Lean's [style guide](https://leanprover-community.github.io/style-guide.html)** and document key definitions with docstrings
4. **Add proofs** for important properties and lemmas
5. **Ensure code compiles** with `lake build`

### Code Style

- Use the `Quantum` namespace for quantum-specific definitions
- Document definitions with `/-- ... -/` docstrings
- Use `@[simp]` attributes for lemmas that should be used by the simplifier
- Follow mathlib conventions for naming and structure

## Long-Term Goals

This repository aims to:

- Provide a verified foundation for quantum error correction in Lean
- Bridge quantum computing and formal methods, enabling mechanized reasoning about quantum circuits
- Serve as a pedagogical resource for learning quantum theory through formal proof
- Complete the formalization of **Shor's 9-qubit error-correcting code**
- Extend to other quantum error correction codes (Steane code, surface codes, etc.)
- Develop verified quantum algorithms and protocols

## Acknowledgments

Built using [Lean 4](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4).
