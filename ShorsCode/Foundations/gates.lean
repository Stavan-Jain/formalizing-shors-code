import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Foundations.basic

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

noncomputable instance instHMulGateState {n : ℕ}
  : HMul (QuantumGate n) (QuantumState n) (QuantumState n) :=
⟨applyGate⟩

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

lemma I_Hermitian {n : ℕ} : Hermitian (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) := by simp

lemma I_Involutary {n : ℕ} : Involutary (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) := by simp

def I {n : ℕ} : QuantumGate n :=
{
  val := 1
  property := unitary_of_hermitian_involutary I_Hermitian I_Involutary
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

/- Define 1/√2 and a lemma for use in the Hadamard gate -/
noncomputable def invsqrt2 : ℂ := 1 / (Real.sqrt 2)

lemma invsqrt2_sq : invsqrt2 * invsqrt2 = 1 / 2 := by
  unfold invsqrt2
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  field_simp [Real.sqrt, h2]
  norm_cast
  simp

/- Creating the H (Hadamard) Quantum Gate -/
noncomputable def Hmat : Matrix (Fin 2) (Fin 2) ℂ :=
  invsqrt2 • !![1, 1; 1, -1]
lemma Hmat_involutary : Involutary Hmat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hmat, Matrix.mul_apply, invsqrt2_sq,]; all_goals ring
lemma Hmat_hermitian : Hermitian Hmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hmat, invsqrt2];

/- H packaged as a `QuantumGate`. -/
noncomputable def H : QuantumGate 1 :=
{ val := Hmat
, property := unitary_of_hermitian_involutary Hmat_hermitian Hmat_involutary
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
instance {n : ℕ} (U : QuantumGate n) : Invertible U.val :=
{
  invOf := (U.val)ᴴ
  invOf_mul_self := by exact (U.property).2
  mul_invOf_self := by exact (U.property).1
}

instance {n : ℕ} (U : QuantumGate n) : Invertible (U.val)ᴴ :=
{
  invOf := (U.val)
  invOf_mul_self := by exact (U.property).1
  mul_invOf_self := by exact (U.property).2
}

noncomputable def gateInverse {n : ℕ} (Q : QuantumGate n)
: QuantumGate n :=
{
  val := (Q.val)ᴴ
  property := by
    unfold Unitary
    simp
    constructor
    · exact Q.property.2
    · exact Q.property.1
}

noncomputable instance {n : ℕ} : Inv (QuantumGate n) :=
⟨fun U => ⟨gateInverse U, (gateInverse U).property⟩⟩

noncomputable instance {n : ℕ} : Mul (QuantumGate n) :=
{
  mul := gateProduct
}

noncomputable instance {n : ℕ} : Group (QuantumGate n) :=
{
  mul_assoc := sorry
  one := I
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry
}

example {n : ℕ} (U: QuantumGate n) : U⁻¹ * U = I := by sorry

-- lemma X_inv {n : ℕ }: X⁻¹ = X := by

/- 2-qubit CNOT, with basis ordering |00>,|01>,|10>,|11>.
   Control = most-significant qubit (the first qubit), target = second. -/
def CNOTmat : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ 1, 0, 0, 0
    ; 0, 1, 0, 0
    ; 0, 0, 0, 1
    ; 0, 0, 1, 0 ]

lemma CNOT_hermitian : Hermitian CNOTmat := by
  -- real permutation matrix = symmetric = Hermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CNOTmat]

lemma CNOT_involutary : Involutary CNOTmat := by
  -- CNOT ⬝ CNOT = I₄
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOTmat, Matrix.mul_apply, Fin.sum_univ_four]

/-- CNOT packaged as a `QuantumGate 2`. -/
def CNOT : QuantumGate 2 :=
{ val := CNOTmat
, property := unitary_of_hermitian_involutary CNOT_hermitian CNOT_involutary }

/-- CNOT as a block matrix on `Fin 2 ⊕ Fin 2`. This might be useful later on -/
def CNOT_blocks : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks (Igate) 0 0 Xmat

example : CNOT * ket00 = ket00 := by sorry

end Quantum
