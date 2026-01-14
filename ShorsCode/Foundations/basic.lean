import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Quantum
open Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev Vector (α : Type*) [Fintype α] [DecidableEq α] := α → ℂ

noncomputable def norm (v : Vector α) :=
  Real.sqrt (∑ i, ‖v i‖^2)

@[simp] lemma norm_def {v : Vector α} : norm v = Real.sqrt (∑ i, ‖v i‖^2) := rfl

/-- The norm is always non-negative. -/
lemma norm_nonneg {v : Vector α} : 0 ≤ norm v := by
  simp only [norm]
  exact Real.sqrt_nonneg _

/-- The square of the norm equals the sum of squared magnitudes. -/
lemma norm_sq_def {v : Vector α} : (norm v)^2 = ∑ i, ‖v i‖^2 := by
  simp [norm]
  rw [Real.sq_sqrt]
  apply Finset.sum_nonneg
  intro i _
  apply sq_nonneg

/-- Two vectors have equal norms if and only if their norm squares are equal. -/
lemma norm_eq_iff_norm_sq_eq {v w : Vector α} :
  norm v = norm w ↔ (norm v)^2 = (norm w)^2 := by
  constructor
  · intro h; rw [h]
  · intro h
    have hvn : 0 ≤ norm v := norm_nonneg
    have hwn : 0 ≤ norm w := norm_nonneg
    rw [norm_sq_def, norm_sq_def] at h
    have hsqrt_eq : Real.sqrt (∑ i, ‖v i‖^2) = Real.sqrt (∑ i, ‖w i‖^2) := by
      rw [h]
    rw [← norm_def, ← norm_def] at hsqrt_eq
    exact hsqrt_eq

abbrev QuantumState (α : Type*) [Fintype α] [DecidableEq α] :=
  { v : Vector α // norm v = 1 }

-- Coerce a quantum state to its underlying vector
instance : CoeTC (QuantumState α) (Vector α) := ⟨Subtype.val⟩

abbrev QubitBasis : Type := Fin 2

abbrev Qubit := QuantumState QubitBasis
abbrev QubitVec := QubitBasis → ℂ

def ket0 : Qubit := ⟨![1, 0], by simp⟩

def ket1 : Qubit := ⟨![0, 1], by simp⟩

abbrev TwoQubitBasis : Type := QubitBasis × QubitBasis
abbrev TwoQubitState : Type := QuantumState TwoQubitBasis

abbrev ThreeQubitBasis := QubitBasis × QubitBasis × QubitBasis
abbrev ThreeQubitVec := ThreeQubitBasis → ℂ
abbrev ThreeQubitState := QuantumState ThreeQubitBasis

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
  have hsum : (∑ x : α, ‖(basisVec i0 : α → ℂ) x‖ ^ 2 : ℝ) = 1 := by
    have hstep : (∑ x : α, ‖(basisVec i0 : α → ℂ) x‖ ^ 2 : ℝ) =
                 ∑ x : α, (if x = i0 then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x = i0
      · subst h; simp [basisVec]
      · simp [basisVec, h]
    rw [hstep]
    simp [Finset.mem_univ]
  rw [norm, hsum, Real.sqrt_one]

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

lemma ketPlusNorm1 : norm (![1 / (Real.sqrt 2), 1 / (Real.sqrt 2)]) = 1 := by
  have h : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by norm_num
  simp
  exact h

noncomputable def ketPlus : Qubit := ⟨(![1 / (Real.sqrt 2), 1 / (Real.sqrt 2)]), ketPlusNorm1⟩

noncomputable def ket000 : ThreeQubitState :=
  ⟨basisVec (0, 0, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 0, 0)))⟩

noncomputable def ket001 : ThreeQubitState :=
  ⟨basisVec (0, 0, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 0, 1)))⟩

noncomputable def ket010 : ThreeQubitState :=
  ⟨basisVec (0, 1, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 1, 0)))⟩

noncomputable def ket011 : ThreeQubitState :=
  ⟨basisVec (0, 1, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 1, 1)))⟩

noncomputable def ket100 : ThreeQubitState :=
  ⟨basisVec (1, 0, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 0, 0)))⟩

noncomputable def ket101 : ThreeQubitState :=
  ⟨basisVec (1, 0, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 0, 1)))⟩

noncomputable def ket110 : ThreeQubitState :=
  ⟨basisVec (1, 1, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 1, 0)))⟩

noncomputable def ket111 : ThreeQubitState :=
  ⟨basisVec (1, 1, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 1, 1)))⟩

@[simp] lemma ket000_val : (ket000 : ThreeQubitVec) = basisVec (0, 0, 0) := rfl
@[simp] lemma ket001_val : (ket001 : ThreeQubitVec) = basisVec (0, 0, 1) := rfl
@[simp] lemma ket010_val : (ket010 : ThreeQubitVec) = basisVec (0, 1, 0) := rfl
@[simp] lemma ket011_val : (ket011 : ThreeQubitVec) = basisVec (0, 1, 1) := rfl
@[simp] lemma ket100_val : (ket100 : ThreeQubitVec) = basisVec (1, 0, 0) := rfl
@[simp] lemma ket101_val : (ket101 : ThreeQubitVec) = basisVec (1, 0, 1) := rfl
@[simp] lemma ket110_val : (ket110 : ThreeQubitVec) = basisVec (1, 1, 0) := rfl
@[simp] lemma ket111_val : (ket111 : ThreeQubitVec) = basisVec (1, 1, 1) := rfl

end Quantum
