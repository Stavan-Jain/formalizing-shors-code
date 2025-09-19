import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix
import Mathlib.Tactic

open Matrix Complex
open scoped BigOperators ComplexConjugate

abbrev QubitVec := Fin 2 → ℂ

noncomputable def l2norm (v : QubitVec) : ℝ :=
  ‖v 0‖^2 + ‖v 1‖^2

@[simp] lemma l2norm_def {v : QubitVec} : l2norm v = ‖v 0‖^2 + ‖v 1‖^2 := rfl

@[ext]
structure Qubit where
  state : QubitVec
  normalized : l2norm state = 1

def ket0 : Qubit :=
  { state := ![1, 0],
    normalized := by simp }

def ket1 : Qubit :=
  { state := ![0, 1],
    normalized := by simp}

def Unitary (U : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (U * Uᴴ = 1) ∧ (Uᴴ * U = 1)

structure QuantumGate where
  U : Matrix (Fin 2) (Fin 2) ℂ
  unitary : Unitary U

lemma l2normQubitState (ψ : Qubit) : l2norm ψ.state = 1 := ψ.normalized

noncomputable abbrev applyMatrixVec
  : Matrix (Fin 2) (Fin 2) ℂ → QubitVec → QubitVec :=
  Matrix.mulVec

lemma l2norm_unitary
    {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : Unitary U) :
    ∀ v : QubitVec, l2norm (applyMatrixVec U v) = l2norm v := sorry

abbrev i := I

noncomputable def applyGate (G : QuantumGate) (ψ : Qubit) : Qubit :=
  { state := applyMatrixVec G.U ψ.state,
    normalized := by
      have := l2norm_unitary G.unitary ψ.state
      rw [← l2normQubitState ψ]
      exact this
  }

@[simp] def Hermitian {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop := Mᴴ = M

@[simp] def Involutary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop := M * M = 1

/-- If a matrix is Hermitian and involutary, then it is unitary. -/
lemma unitary_of_hermitian_involutary
  {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hH : Hermitian U) (hI : Involutary U) :
(U * Uᴴ = 1) ∧ (Uᴴ * U = 1) := by
  have hH' : Uᴴ = U := hH
  refine ⟨?left, ?right⟩
  · simpa [hH'] using hI
  · simpa [hH'] using hI

/- Defining the Identity Quantum Gate -/
lemma id_Hermitian : Hermitian (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simp

lemma id_Involutary : Involutary (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simp

/-- Identity matrix packaged as a `QuantumGate`. -/
def Igate : QuantumGate :=
  { U := 1
  , unitary := unitary_of_hermitian_involutary id_Hermitian id_Involutary
  }

/- Creating the Pauli X Quantum Gate -/
def Xmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
lemma Xmat_hermitian : Hermitian Xmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat]

lemma Xmat_involutary : Involutary Xmat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xmat, Matrix.mul_apply]

/-- Pauli X packaged as a `QuantumGate`. -/
def Xgate : QuantumGate :=
  { U := Xmat
  , unitary := unitary_of_hermitian_involutary Xmat_hermitian Xmat_involutary
  }

/- Creating the Pauli Y Quantum Gate -/
def Ymat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -i; i, 0]

lemma Ymat_hermitian : Hermitian Ymat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ymat]

lemma Ymat_involutary : Involutary Ymat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ymat, Matrix.mul_apply]

/-- Pauli Y packaged as a `QuantumGate`. -/
def Ygate : QuantumGate :=
  { U := Ymat
  , unitary := unitary_of_hermitian_involutary Ymat_hermitian Ymat_involutary
  }

/- Creating the Pauli Z Quantum Gate -/
def Zmat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
lemma Zmat_hermitian : Hermitian Zmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zmat]

lemma Zmat_involutary : Involutary Zmat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Zmat, Matrix.mul_apply]

/-- Pauli Z packaged as a `QuantumGate`. -/
def Zgate : QuantumGate :=
  { U := Zmat
  , unitary := unitary_of_hermitian_involutary Zmat_hermitian Zmat_involutary
  }

lemma X_on_ket0 : applyGate Xgate ket0 = ket1 := by
  ext x
  fin_cases x <;>
      simp [applyGate, Xgate, Xmat, ket0, ket1,
            applyMatrixVec]

lemma X_on_ket1 : applyGate Xgate ket1 = ket0 := by
  ext x
  fin_cases x <;>
      simp [applyGate, Xgate, Xmat, ket0, ket1,
            applyMatrixVec]

-- TODO: try to get simp to auto-apply everything
lemma XZ_neg_ZX : Xgate.U * Zgate.U = - (Zgate.U * Xgate.U) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xgate, Xmat, Zgate, Zmat]
