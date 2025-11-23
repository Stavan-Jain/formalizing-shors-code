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
abbrev QubitState : Type := QuantumState QubitBasis
abbrev QubitVec := QubitBasis → ℂ

def ket0 : Qubit := ⟨![1, 0], by simp⟩

def ket1 : Qubit := ⟨![0, 1], by simp⟩

abbrev TwoQubitBasis : Type := QubitBasis × QubitBasis
abbrev TwoQubitState : Type := QuantumState TwoQubitBasis

-- The "constructor" for basis vectors
noncomputable def basisVec (i0 : α) : Vector α :=
  fun i => if i = i0 then (1 : ℂ) else 0

@[simp] lemma basisVec_apply {α : Type*} [DecidableEq α] [Fintype α] (a x : α) :
  basisVec a x = (if x = a then 1 else 0) :=
by simp[basisVec]

@[simp] lemma dot_basisVec_left
  {α} [Fintype α] [DecidableEq α] (v : α → ℂ) (i : α) :
  (v ⬝ᵥ basisVec i) = v i := by
  classical
  simp [dotProduct, basisVec]


open scoped BigOperators

lemma norm_basisVec {α : Type*} [Fintype α] [DecidableEq α] (i0 : α) :
  norm (basisVec i0 : α → ℂ) = 1 := by
  classical
  -- First show the sum of squared entries is 1.
  have hsum :
      (∑ x : α, ‖(basisVec i0 : α → ℂ) x‖ ^ 2 : ℝ) = 1 := by
    -- Replace each summand by a simple real-valued `if`.
    have hstep :
        (∑ x : α, ‖(basisVec i0 : α → ℂ) x‖ ^ 2 : ℝ)
          = ∑ x : α, (if x = i0 then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x = i0
      · subst h
        simp [basisVec]          -- ‖1‖^2 = 1
      · simp [basisVec, h]       -- ‖0‖^2 = 0
    -- Now the sum of this indicator is just 1.
    simp [basisVec] at hstep
    exact hstep                -- `simp` evaluates the sum-of-ite to 1
  -- Now use the definition of `norm`.
  simp [norm]
  exact hsum

noncomputable def ket00 : TwoQubitState :=
  ⟨ basisVec ((0, 0) : TwoQubitBasis),
    by simpa using norm_basisVec ((0, 0) : TwoQubitBasis) ⟩

noncomputable def ket01 : TwoQubitState :=
  ⟨ basisVec ((0, 1) : TwoQubitBasis),
    by simpa using norm_basisVec ((0, 1) : TwoQubitBasis) ⟩

noncomputable def ket10 : TwoQubitState :=
  ⟨ basisVec ((1, 0) : TwoQubitBasis),
    by simpa using norm_basisVec ((1, 0) : TwoQubitBasis) ⟩

noncomputable def ket11 : TwoQubitState :=
  ⟨ basisVec ((1, 1) : TwoQubitBasis),
    by simpa using norm_basisVec ((1, 1) : TwoQubitBasis) ⟩

lemma ketPlusNorm1 : norm (![1 / (Real.sqrt 2) , 1 / (Real.sqrt 2)]) = 1 := by
  have h : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by grind
  simp
  exact h

noncomputable def ketPlus : Qubit := ⟨(![1 / (Real.sqrt 2) , 1 / (Real.sqrt 2)]), ketPlusNorm1⟩

end Quantum
