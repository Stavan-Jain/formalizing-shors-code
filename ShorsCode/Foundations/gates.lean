import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Foundations.Basic

namespace Quantum
open Matrix

def Unitary {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  (U * Uᴴ = 1) ∧ (Uᴴ * U = 1)

abbrev QuantumGate (n : ℕ):= {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ // Unitary U}

instance {n : ℕ} : CoeTC (QuantumGate n) (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := ⟨Subtype.val⟩
@[simp] lemma coe_val_Qgate {n} (ψ : QuantumState n) : ((ψ : Vector (2^n)) = ψ.val) := rfl

noncomputable abbrev applyMatrixVec {n : ℕ}
  : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → Vector (2 ^ n) → Vector (2 ^ n) :=
  Matrix.mulVec

lemma unitary_preserves_norm {n : ℕ} {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hU : Unitary U) :
∀ v : Vector (2 ^ n), norm (applyMatrixVec U v) = norm v := sorry

noncomputable def applyGate {n : ℕ} (G : QuantumGate n) (ψ : QuantumState n) : QuantumState n :=
  { val := applyMatrixVec G.val ψ.val,
    property := by
      have h := unitary_preserves_norm G.property ψ.val
      rw [h]
      exact ψ.property
  }

def Hermitian {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop := Mᴴ = M

@[simp] lemma Hermitian_def {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Hermitian M ↔ Mᴴ = M := Iff.rfl

def Involutary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop := M * M = 1

@[simp] lemma Involutary_def {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
Involutary M ↔ M * M = 1 := Iff.rfl

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

def Igate : QuantumGate 1:=
  { val := 1
  , property := unitary_of_hermitian_involutary id_Hermitian id_Involutary
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
def X : QuantumGate 1:=
  { val := Xmat
  , property := unitary_of_hermitian_involutary Xmat_hermitian Xmat_involutary}

abbrev i := Complex.I
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
def Y : QuantumGate 1:=
  { val := Ymat
  , property := unitary_of_hermitian_involutary Ymat_hermitian Ymat_involutary
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
def Z : QuantumGate 1 :=
  { val := Zmat
  , property := unitary_of_hermitian_involutary Zmat_hermitian Zmat_involutary
  }

lemma X_on_ket0 : applyGate X ket0 = ket1 := by
  ext x
  fin_cases x <;>
      simp [applyGate, X, Xmat, ket0, ket1,
            applyMatrixVec]
lemma X_on_ket1 : applyGate X ket1 = ket0 := by
  ext x
  fin_cases x <;>
      simp [applyGate, X, Xmat, ket0, ket1,
            applyMatrixVec]

lemma XZ_neg_ZX : X.val * Z.val = - (Z.val * X.val) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X, Xmat, Z, Zmat]

lemma X_involutary' (ψ : Qubit) :
    applyGate X (applyGate X ψ) = ψ := by
    ext x
    simp only [applyGate, applyMatrixVec, X]
    have := Xmat_involutary
    rw [Involutary_def] at this
    rw [mulVec_mulVec, this, one_mulVec]

#check Matrix.conjTranspose_mul

noncomputable def gateProduct {n : ℕ} (Q1 : QuantumGate n) (Q2 : QuantumGate n) : QuantumGate n :=
{
  val := Q1.val * Q2.val
  property := by
    constructor
    · rw [Matrix.conjTranspose_mul]
      have h1 := Q1.property.1
      have h2 := Q2.property.1
      unfold Unitary at *
      simp [mul_assoc]
      have h : Q1.val * (Q2.val * ((Q2.val)ᴴ * (Q1.val)ᴴ)) = Q1.val * (Q2.val *
      (Q2.val)ᴴ) * (Q1.val)ᴴ := by grind
      rw [h, h2, mul_one]
      exact h1
    · rw [Matrix.conjTranspose_mul]
      have h1 := Q1.property.2
      have h2 := Q2.property.2
      have h : Q2.valᴴ * (Q1.val)ᴴ * (Q1.val * ((Q2.val))) =
      Q2.valᴴ * ((Q1.val)ᴴ * Q1.val) * ((Q2.val)) := by grind
      rw [h, h1, mul_one]
      exact h2
}

#check Matrix.mul_inv_eq_iff_eq_mul_of_invertible
lemma unitary_eq_conjugate_transpose {n : ℕ} (Q : QuantumGate n) :
  Q.val = ((Q.val)ᴴ)⁻¹ := by
  have := Q.property.1
  calc
    -- need Q.val invertible
    Q.val = Q.val * (Q.valᴴ * ((Q.val)ᴴ)⁻¹) := sorry
    Q.val * (Q.valᴴ * ((Q.val)ᴴ)⁻¹) = (Q.val * Q.valᴴ) * ((Q.val)ᴴ)⁻¹ := by grind
  rw [this, one_mul]

noncomputable def gateInverse {n : ℕ} (Q : QuantumGate n)
: QuantumGate n :=
{
  val := (Q.val)⁻¹
  property := by
    unfold Unitary
    sorry
    -- constructor
}
