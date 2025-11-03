import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Quantum
open Matrix

abbrev Vector (n : ℕ):= Fin n → ℂ

noncomputable def norm {n : ℕ} (v : Vector n) := Real.sqrt (∑ i, ‖v i‖^2)

@[simp] lemma norm_def {n : ℕ} {v : Vector n} : norm v =
Real.sqrt (∑ i, ‖v i‖^2) := rfl

abbrev QuantumState (n : ℕ) := {v : Fin (2^n) → ℂ // norm v = 1}

-- Coerce a quantum state to its underlying vector
instance {n : ℕ} : CoeTC (QuantumState n) (Vector (2^n)) := ⟨Subtype.val⟩
@[simp] lemma coe_val_QState {n} (ψ : QuantumState n) : ((ψ : Vector (2^n)) = ψ.val) := rfl

abbrev Qubit := QuantumState 1

def ket0 : Qubit := ⟨![1, 0], by simp⟩

def ket1 : Qubit := ⟨![0, 1], by simp⟩

def ket00 : QuantumState 2 := ⟨![1, 0, 0, 0], by simp [Fin.sum_univ_four]⟩

def ket01 : QuantumState 2 := ⟨![0, 1, 0, 0], by simp [Fin.sum_univ_four]⟩

def ket10 : QuantumState 2 := ⟨![0, 0, 1, 0], by simp [Fin.sum_univ_four]⟩

def ket11 : QuantumState 2 := ⟨![0, 0, 0, 1], by simp [Fin.sum_univ_four]⟩

lemma ketPlusNorm1 : norm (![1 / (Real.sqrt 2) , 1 / (Real.sqrt 2)]) = 1 := by
  have h : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by grind
  simp
  exact h

noncomputable def ketPlus : Qubit := ⟨(![1 / (Real.sqrt 2) , 1 / (Real.sqrt 2)]), ketPlusNorm1⟩


end Quantum
