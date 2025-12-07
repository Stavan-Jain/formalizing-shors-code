import Foundations.Basic
import Foundations.Gates

namespace Quantum

open Matrix
open Kronecker

@[simp]
theorem star_kron
  {α β : Type*}
  [DecidableEq α] [Fintype α]
  [DecidableEq β] [Fintype β]
  (a : Matrix α α ℂ) (b : Matrix β β ℂ) :
  star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  classical
  ext i j
  simp

/--
If `a` and `b` are unitary, then their Kronecker product is unitary.
-/
theorem kron_unitary
  {α β : Type*}
  [DecidableEq α] [Fintype α]
  [DecidableEq β] [Fintype β]
  (a : Matrix.unitaryGroup α ℂ)
  (b : Matrix.unitaryGroup β ℂ) :
  a.val ⊗ₖ b.val ∈ Matrix.unitaryGroup (α × β) ℂ := by
  classical
  simp [Matrix.mem_unitaryGroup_iff, star_kron, ← Matrix.mul_kronecker_mul]

noncomputable def tensorGate
  {α β : Type*}
  [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (G₁ : QuantumGate α) (G₂ : QuantumGate β) :
  QuantumGate (α × β) :=
by
  classical
  refine ⟨G₁.val ⊗ₖ G₂.val, ?_⟩
  simpa using (kron_unitary (a := G₁) (b := G₂))

scoped notation G₁:60 " ⊗ᵍ " G₂:60 => tensorGate G₁ G₂

open scoped BigOperators

/-- Tensor product of vectors (not yet normalized). -/
noncomputable def tensorVec
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (v : Vector α) (w : Vector β) : Vector (α × β) :=
  fun ij => v ij.1 * w ij.2

/-- The norm of a tensor product of normalized states is 1. -/
lemma norm_tensorVec_of_norm1
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  {v : Vector α} {w : Vector β}
  (hv : norm v = 1) (hw : norm w = 1) :
  norm (tensorVec v w) = 1 :=
by
  admit

/-- Tensor product of quantum states. -/
noncomputable def tensorState
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (ψ : QuantumState α) (φ : QuantumState β) :
  QuantumState (α × β) :=
by
  refine ⟨tensorVec ψ.val φ.val, ?_⟩
  -- use the norm lemma with hv := ψ.property, hw := φ.property
  exact norm_tensorVec_of_norm1 ψ.property φ.property

scoped notation ψ:60 " ⊗ₛ " φ:60 => tensorState ψ φ

end Quantum
