import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Quantum

variable {α : Type*} [Fintype α] [DecidableEq α]

/-!
### Vectors and quantum states
-/

-- ℓ² space indexed by α
abbrev Vector (α : Type*) [Fintype α] := EuclideanSpace ℂ α

-- Normalized quantum states
abbrev QuantumState (α : Type*) [Fintype α] [DecidableEq α] :=
  { v : Vector α // ‖v‖ = (1 : ℝ) }

-- Coercion to underlying vector
instance : CoeTC (QuantumState α) (Vector α) := ⟨Subtype.val⟩

@[simp] lemma coe_val_QState (ψ : QuantumState α) :
  ((ψ : Vector α) = ψ.val) := rfl


/-!
### Basis vectors
-/

-- Computational basis vector
noncomputable def basisVec (i0 : α) : Vector α :=
  Pi.single i0 (1 : ℂ)

-- Norm of a basis vector
lemma norm_basisVec (i0 : α) : ‖basisVec (α := α) i0‖ = (1 : ℝ) := by
  have hsum : (∑ i : α, ‖(basisVec (α := α) i0) i‖ ^ 2 : ℝ) = 1 := by
    have hstep : (∑ x : α, ‖(Pi.single i0 (1 : ℂ) : Vector α) x‖ ^ 2 : ℝ) = ∑ x
    : α, (if x = i0 then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      by_cases h : x = i0
      · subst h
        simp
      · simp [Pi.single, h]
    simp [basisVec] at *
    rw [hstep]
  simpa [basisVec, EuclideanSpace.norm_eq, hsum]

/-!
### One qubit
-/

abbrev QubitBasis : Type := Fin 2
abbrev QubitVec : Type := Vector QubitBasis
abbrev QubitState : Type := QuantumState QubitBasis

noncomputable def ket0 : QubitState :=
  ⟨basisVec (α := QubitBasis) 0,
    by simpa using norm_basisVec (α := QubitBasis) 0⟩

noncomputable def ket1 : QubitState :=
  ⟨basisVec (α := QubitBasis) 1,
    by simpa using norm_basisVec (α := QubitBasis) 1⟩

@[simp] lemma ket0_val : (ket0 : QubitVec) = basisVec (α := QubitBasis) 0 := rfl
@[simp] lemma ket1_val : (ket1 : QubitVec) = basisVec (α := QubitBasis) 1 := rfl

/-!
### Two qubits
-/

abbrev TwoQubitBasis : Type := QubitBasis × QubitBasis
abbrev TwoQubitVec : Type := Vector TwoQubitBasis
abbrev TwoQubitState : Type := QuantumState TwoQubitBasis

noncomputable def ket00 : TwoQubitState :=
  ⟨basisVec (α := TwoQubitBasis) (0, 0),
    by simpa using norm_basisVec (α := TwoQubitBasis) (0, 0)⟩

noncomputable def ket01 : TwoQubitState :=
  ⟨basisVec (α := TwoQubitBasis) (0, 1),
    by simpa using norm_basisVec (α := TwoQubitBasis) (0, 1)⟩

noncomputable def ket10 : TwoQubitState :=
  ⟨basisVec (α := TwoQubitBasis) (1, 0),
    by simpa using norm_basisVec (α := TwoQubitBasis) (1, 0)⟩

noncomputable def ket11 : TwoQubitState :=
  ⟨basisVec (α := TwoQubitBasis) (1, 1),
    by simpa using norm_basisVec (α := TwoQubitBasis) (1, 1)⟩


/-!
### Three qubits
-/

abbrev ThreeQubitBasis : Type := QubitBasis × QubitBasis × QubitBasis
abbrev ThreeQubitVec : Type := Vector ThreeQubitBasis
abbrev ThreeQubitState : Type := QuantumState ThreeQubitBasis

noncomputable def ket000 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (0, 0, 0),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (0, 0, 0)⟩

noncomputable def ket001 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (0, 0, 1),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (0, 0, 1)⟩

noncomputable def ket010 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (0, 1, 0),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (0, 1, 0)⟩

noncomputable def ket011 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (0, 1, 1),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (0, 1, 1)⟩

noncomputable def ket100 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (1, 0, 0),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (1, 0, 0)⟩

noncomputable def ket101 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (1, 0, 1),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (1, 0, 1)⟩

noncomputable def ket110 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (1, 1, 0),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (1, 1, 0)⟩

noncomputable def ket111 : ThreeQubitState :=
  ⟨basisVec (α := ThreeQubitBasis) (1, 1, 1),
    by simpa using norm_basisVec (α := ThreeQubitBasis) (1, 1, 1)⟩

@[simp] lemma ket000_val : (ket000 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (0, 0, 0) := rfl
@[simp] lemma ket001_val : (ket001 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (0, 0, 1) := rfl
@[simp] lemma ket010_val : (ket010 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (0, 1, 0) := rfl
@[simp] lemma ket011_val : (ket011 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (0, 1, 1) := rfl
@[simp] lemma ket100_val : (ket100 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (1, 0, 0) := rfl
@[simp] lemma ket101_val : (ket101 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (1, 0, 1) := rfl
@[simp] lemma ket110_val : (ket110 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (1, 1, 0) := rfl
@[simp] lemma ket111_val : (ket111 : ThreeQubitVec) = basisVec (α :=
ThreeQubitBasis) (1, 1, 1) := rfl

end Quantum
