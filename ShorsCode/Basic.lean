import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix

abbrev QVec (n : ℕ):= Fin n → ℂ

noncomputable def normsq {n : ℕ} (v : Fin n → ℂ) : ℝ :=
∑ i, ‖v i‖^2

@[simp] lemma normsq_def {n : ℕ} {v : Fin n → ℂ} : normsq v = ∑ i, ‖v i‖^2 := rfl

@[ext]
structure QState (n : ℕ) where
  state : Fin (2^n) → ℂ
  normalized : normsq state = 1

abbrev Qubit := QState 1

-- Allows us to treat a qubit as a qubit.vec
instance : CoeTC  Qubit (QVec 2) := ⟨QState.state⟩
@[simp] lemma coe_Qubit (ψ : Qubit) : (ψ : QVec 2) = ψ.state := rfl

-- Allows us to treat a qubit as a qubit.vec
instance {n : ℕ} : CoeTC  (QState n) (QVec (2 ^ n)) := ⟨QState.state⟩
@[simp] lemma coe_QState {n : ℕ} (ψ : QState n) : (ψ : QVec (2 ^ n)) = ψ.state := rfl

def ket0 : Qubit :=
  { state := ![1, 0],
    normalized := by simp}

def ket1 : Qubit :=
  { state := ![0, 1],
    normalized := by simp}

def Unitary (U : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (U * Uᴴ = 1) ∧ (Uᴴ * U = 1)

structure QuantumGate where
  U : Matrix (Fin 2) (Fin 2) ℂ
  unitary : Unitary U

-- Allows us to treat a qubit as a qubit.vec
instance : CoeTC QuantumGate (Matrix (Fin 2) (Fin 2) ℂ) := ⟨QuantumGate.U⟩
@[simp] lemma coe_QuantumGate (Q : QuantumGate) : (Q : Matrix (Fin 2) (Fin 2) ℂ) = Q.U := rfl

lemma normsqQubitState (ψ : Qubit) : normsq ψ.state = 1 := ψ.normalized

noncomputable abbrev applyMatrixVec
  : Matrix (Fin 2) (Fin 2) ℂ → QVec 2 → QVec 2 :=
  Matrix.mulVec

lemma normsq_unitary
    {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : Unitary U) :
    ∀ v : QVec 2, normsq (applyMatrixVec U v) = normsq v := sorry

abbrev i := Complex.I

noncomputable def applyGate (G : QuantumGate) (ψ : Qubit) : Qubit :=
  { state := applyMatrixVec G.U ψ,
    normalized := by
      have := normsq_unitary G.unitary ψ
      rw [← normsqQubitState ψ]
      exact this
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
  , unitary := unitary_of_hermitian_involutary Xmat_hermitian Xmat_involutary}

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

-- Maybe add these as simp lemmas?
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

lemma XZ_neg_ZX : Xgate.U * Zgate.U = - (Zgate.U * Xgate.U) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xgate, Xmat, Zgate, Zmat]

-- TODO : Prove that X as a gate is involutary
lemma X_involutary' (ψ : Qubit) :
    applyGate Xgate (applyGate Xgate ψ) = ψ := by
    ext x
    simp only [applyGate, applyMatrixVec, Xgate]
    have := Xmat_involutary
    rw [Involutary_def] at this
    rw [mulVec_mulVec, this, one_mulVec]

-- TODO: Prove that Unitary * Unitary = Unitary
