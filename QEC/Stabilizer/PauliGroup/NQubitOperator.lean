import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import QEC.Foundations.Foundations
import QEC.Stabilizer.PauliGroupSingle

namespace Quantum
open Matrix
open scoped BigOperators

/-!
# N-Qubit Pauli Operators

This file defines `NQubitPauliOperator n := Fin n → PauliOperator` along with basic
constructors and the matrix/gate representations.
-/

/-- An n-qubit Pauli operator.

This assigns a single-qubit Pauli operator to each of the n qubits.
The matrix representation is the tensor product (Kronecker product) of the individual
Pauli matrices.
-/
def NQubitPauliOperator (n : ℕ) : Type := Fin n → PauliOperator

variable {n : ℕ}

namespace NQubitPauliOperator

/-- Extensionality for NQubitPauliOperator. -/
@[ext] theorem ext {op₁ op₂ : NQubitPauliOperator n} (h : ∀ i, op₁ i = op₂ i) : op₁ = op₂ :=
  funext h

/-- The identity n-qubit Pauli operator (I ⊗ I ⊗ ... ⊗ I). -/
def identity (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.I

/-- The X n-qubit Pauli operator (X ⊗ X ⊗ ... ⊗ X). -/
def X (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.X

/-- The Y n-qubit Pauli operator (Y ⊗ Y ⊗ ... ⊗ Y). -/
def Y (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.Y

/-- The Z n-qubit Pauli operator (Z ⊗ Z ⊗ ... ⊗ Z). -/
def Z (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.Z

/-- Extract the Pauli operator at a specific qubit position. -/
def get (op : NQubitPauliOperator n) (i : Fin n) : PauliOperator := op i

/-- Set the Pauli operator at a specific qubit position. -/
def set (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
  NQubitPauliOperator n :=
  fun j => if j = i then p else op j

/-- Convert an n-qubit Pauli operator to its matrix representation.

For n qubits, this computes the tensor product (Kronecker product) of the
individual single-qubit Pauli matrices: M_0 ⊗ M_1 ⊗ ... ⊗ M_{n-1}

The matrix entry at (b₁, b₂) where b₁, b₂ : Fin n → QubitBasis is the product
over all qubit positions of the corresponding entries in the individual Pauli matrices:
  ∏_{i : Fin n} (op i).toMatrix (b₁ i) (b₂ i)

This corresponds to the tensor product of the individual Pauli matrices.
-/
noncomputable def toMatrix (op : NQubitPauliOperator n) :
  Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  fun b₁ b₂ => (Finset.univ : Finset (Fin n)).prod (fun i => (op i).toMatrix (b₁ i) (b₂ i))

/-- Construct an n-qubit Pauli operator from a list of Pauli operators.

The list should have length n, and the i-th element specifies the operator on qubit i.
-/
def ofList (ops : List PauliOperator) (h : ops.length = n) :
  NQubitPauliOperator n :=
  fun i => ops.get ⟨i.val, h ▸ i.isLt⟩

/-- Convert an n-qubit Pauli operator to a list. -/
def toList (op : NQubitPauliOperator n) : List PauliOperator :=
  List.ofFn op

/-- The identity operator's matrix representation is the identity matrix.

This follows from:
- Each qubit has the identity operator I
- `PauliOperator.I.toMatrix = 1` (the 2×2 identity matrix)
- The tensor product of identity matrices is the identity matrix
-/
lemma identity_toMatrix (n : ℕ) :
  (identity n).toMatrix = (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
  ext b₁ b₂
  simp [toMatrix, identity, Matrix.one_apply]
  by_cases h : b₁ = b₂
  · subst h
    simp
  · have h_ne : ∃ i, b₁ i ≠ b₂ i := by
      contrapose! h
      ext i
      simp [h]
    obtain ⟨i, hi⟩ := h_ne
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
      exact h
    · simp [hi]

/-- The matrix of an n-qubit Pauli operator is unitary.

Each single-qubit Pauli matrix is unitary; the n-qubit matrix is their tensor product.
-/
lemma toMatrix_mem_unitaryGroup (op : NQubitPauliOperator n) :
  op.toMatrix ∈ Matrix.unitaryGroup (NQubitBasis n) ℂ := by
  convert Quantum.PauliGroupElement.toMatrix_mem_unitaryGroup _;
  swap;
  · exact ⟨ 0, Quantum.PauliOperator.X ⟩
  constructor <;> intro h <;> simp [ Matrix.mem_unitaryGroup_iff];
  ext i j ; simp +decide [ Matrix.mul_apply, Quantum.NQubitPauliOperator.toMatrix ];
  have h_simp : ∀ (i j : NQubitBasis n), (∑ x : NQubitBasis n,
  (∏ k : Fin n, (op k).toMatrix (i k) (x k)) *
  (∏ k : Fin n, starRingEnd ℂ ((op k).toMatrix (j k) (x k)))) = (∏ k : Fin n,
  (∑ x : QubitBasis, (op k).toMatrix (i k) x * starRingEnd ℂ ((op k).toMatrix (j k) x))) := by
    simp +decide only [← Finset.prod_mul_distrib];
    exact fun i j ↦
      Eq.symm
        (Fintype.prod_sum fun i_2 j_2 ↦
          (op i_2).toMatrix (i i_2) j_2 * (starRingEnd ℂ) ((op i_2).toMatrix (j i_2) j_2));
  have h_unitary : ∀ (k : Fin n) (i j : QubitBasis),
  (∑ x : QubitBasis, (op k).toMatrix i x * starRingEnd ℂ
  ((op k).toMatrix j x)) = if i = j then 1 else 0 := by
    intro k i j; rcases h : op k with ( _ | _ | _ | _ ) <;> simp
    <;> fin_cases i <;> fin_cases j <;>
    simp [ Matrix.one_apply, Quantum.Xmat, Quantum.Ymat, Quantum.Zmat ];
  simp_all +decide [ Matrix.one_apply ];
  by_cases hi : i = j <;> simp +decide [ hi ];
  exact Finset.prod_eq_zero ( Finset.mem_univ ( Classical.choose
  ( Function.ne_iff.mp hi ) ) ) ( if_neg ( Classical.choose_spec
  ( Function.ne_iff.mp hi ) ) )

/-- Convert an n-qubit Pauli operator to its underlying gate.

This is the primary representation connecting the Stabilizer layer to Foundations.
The matrix representation is recovered as `(op.toGate).val = op.toMatrix`.
-/
noncomputable def toGate (op : NQubitPauliOperator n) : QuantumGate (NQubitBasis n) :=
  ⟨op.toMatrix, toMatrix_mem_unitaryGroup op⟩

/-- Connection between `toGate` and `toMatrix` for n-qubit operators. -/
@[simp] lemma toGate_val (op : NQubitPauliOperator n) : (op.toGate).val = op.toMatrix := rfl

end NQubitPauliOperator

end Quantum
