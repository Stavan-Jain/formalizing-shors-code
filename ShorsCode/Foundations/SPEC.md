# SPEC.md — Formalizing the Quantum 3-Bit Repetition Code in Lean

##  Project Overview

**Goal:**  
To formally define and verify the **quantum 3-bit repetition code** in Lean 4.  
The final theorem will state that this code can **correct a single bit-flip (Pauli-X) error** on any of its three physical qubits.

**End Theorem (informal):**
> For any qubit state `ψ`, and for any single-qubit bit-flip error `Xᵢ`,  
> applying encoding → error → decoding yields the original state:
>
> ```
> ∀ ψ : Qubit, ∀ i : Fin 3, decode (Xᵢ (encode ψ)) = ψ
> ```
---

## 🧩 Module Structure

| Module | Purpose |
|:-------|:--------|
| `Quantum.Basic` | Core definitions: complex vectors, norms, normalized quantum states, and unitaries. |
| `Quantum.Tensor` | Tensor product for states and gates; proofs of normalization and associativity. |
| `Quantum.Gates` | Common gates (X, H, CNOT); lemmas on unitarity and application to states. |
| `Quantum.Code.Repetition3` | Encoding and decoding for the 3-bit repetition code. |
| `Quantum.Code.Theorems` | Proofs that the code corrects all single bit-flip errors. |

---

## Current Progress

**Quantum.Basic**
- `Vector`, `norm` definitions 
- `QuantumState` definition (normalized complex vector)  
- Coercions between states and vectors  
- Basis qubits `|0⟩`, `|1⟩`, and `|+⟩`  


**Quantum.Gates**
- `Unitary` and `QuantumGate` definitions  
- Implemented Pauli gates: X, Y, Z
- Defined applyGate: applying a QuantumGate to a QuantumState 
- Proved that X |0⟩ = |1⟩ and X |1⟩ = |0⟩
- Defined gateProduct: composing two QuantumGates

---

## Roadmap to the 3-Bit Code

### 1. `Quantum.Tensor`
- [ ] Define `tensorVec : Vector (2^n) → Vector (2^m) → Vector (2^(n+m))`
- [ ] Prove `norm (tensorVec ψ φ) = norm ψ * norm φ`
- [ ] Define `tensorState (ψ : QuantumState n) (φ : QuantumState m) : QuantumState (n + m)`
- [ ] Define shorthand operator `⊗` for readability

### 2. `Quantum.Gates`
- [ ] Prove that QuantumGate is a group under multiplication
  - [ ] Prove that QuantumGates are invertible
  - [ ] Prove that that the identity matrix is the group identity
- [ ] Implement Hadamard (H)
- [ ] Implement CNOT
- [ ] Prove that unitary matrices preserve norms

### 3. `Quantum.Code.Repetition3`
- [ ] Define the encoding map:  
  `encode : Qubit → QuantumState 3`,  
  where `encode |0⟩ = |000⟩` and `encode |1⟩ = |111⟩`
- [ ] Define bit-flip error operators `X₀, X₁, X₂`
- [ ] Define decoding operation `decode : QuantumState 3 → Qubit`
- [ ] Show `decode (encode ψ) = ψ`

### 4. `Quantum.Code.Theorems`
- [ ] Prove `decode (Xᵢ (encode ψ)) = ψ` for all single-bit flips
- [ ] Combine lemmas into `repetition3_corrects_single_bit_flip`

---

## 🔬 Future Extensions

- [ ] Extend to **phase-flip code** (Z errors)  
- [ ] Compose both into **Shor’s 9-qubit code**  

---

## 🧱 File Layout Suggestion

