import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Quantum
open Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev Vector (α : Type*) [Fintype α] [DecidableEq α]:= α → ℂ

noncomputable def norm (v : Vector α) :=
  Real.sqrt (∑ i, ‖v i‖^2)

@[simp] lemma norm_def {v : Vector α} : norm v =
Real.sqrt (∑ i, ‖v i‖^2) := rfl

abbrev QuantumState (α : Type*) [Fintype α] [DecidableEq α]:=
  { v : Vector α // norm v = 1 }

-- Coerce a quantum state to its underlying vector
instance :
  CoeTC (QuantumState α) (Vector α) := ⟨Subtype.val⟩

@[simp] lemma coe_val_QState
  (ψ : QuantumState α) :
  ((ψ : Vector α) = ψ.val) := rfl

abbrev QubitBasis : Type := Fin 2

abbrev Qubit := QuantumState QubitBasis

def ket0 : Qubit := ⟨![1, 0], by simp⟩

def ket1 : Qubit := ⟨![0, 1], by simp⟩

abbrev TwoQubitBasis : Type := QubitBasis × QubitBasis
abbrev TwoQubit : Type := QuantumState TwoQubitBasis

-- The "constructor" for basis vectors
noncomputable def basisVec (i0 : α) : Vector α :=
  fun i => if i = i0 then (1 : ℂ) else 0

lemma norm_basisVec (i0 : α) :
  norm (basisVec i0) = 1 := by
  classical
  -- we'll prove this later by expanding the sum
  admit

noncomputable def ket00 : TwoQubit :=
  ⟨ basisVec ((0, 0) : TwoQubitBasis),
    by simpa using norm_basisVec ((0, 0) : TwoQubitBasis) ⟩

noncomputable def ket01 : TwoQubit :=
  ⟨ basisVec ((0, 1) : TwoQubitBasis),
    by simpa using norm_basisVec ((0, 1) : TwoQubitBasis) ⟩

noncomputable def ket10 : TwoQubit :=
  ⟨ basisVec ((1, 0) : TwoQubitBasis),
    by simpa using norm_basisVec ((1, 0) : TwoQubitBasis) ⟩

noncomputable def ket11 : TwoQubit :=
  ⟨ basisVec ((1, 1) : TwoQubitBasis),
    by simpa using norm_basisVec ((1, 1) : TwoQubitBasis) ⟩

lemma ketPlusNorm1 : norm (![1 / (Real.sqrt 2) , 1 / (Real.sqrt 2)]) = 1 := by
  have h : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by grind
  simp
  exact h

noncomputable def ketPlus : Qubit := ⟨(![1 / (Real.sqrt 2) , 1 / (Real.sqrt 2)]), ketPlusNorm1⟩

end Quantum
