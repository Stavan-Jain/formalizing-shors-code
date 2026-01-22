import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Foundations.Basic
import Foundations.Gates
import Foundations.Tensor

namespace Quantum
open Matrix
open scoped BigOperators

/-!
# The Pauli Group on a Single Qubit

This file defines the Pauli group on a single qubit. The Pauli group consists of
the four Pauli operators (I, X, Y, Z) multiplied by phases {1, -1, i, -i}, giving
16 elements total.

The Pauli group is fundamental to the stabilizer formalism for quantum error correction.
-/

/-- The four Pauli operators: Identity, X, Y, and Z. -/
inductive PauliOperator : Type
  | I : PauliOperator
  | X : PauliOperator
  | Y : PauliOperator
  | Z : PauliOperator
deriving DecidableEq

/-- An element of the single-qubit Pauli group.

The Pauli group consists of elements of the form `i^k * P` where:
- `k : Fin 4` represents the phase: k=0 → 1, k=1 → i, k=2 → -1, k=3 → -i
- `op : PauliOperator` is one of I, X, Y, Z

This gives 4 phases × 4 operators = 16 total elements.
-/
structure PauliGroupElement where
  phasePower : Fin 4  -- 0 → 1, 1 → i, 2 → -1, 3 → -i
  operator : PauliOperator
deriving DecidableEq

/-- Extensionality for PauliGroupElement. -/
@[ext] theorem PauliGroupElement.ext (p q : PauliGroupElement)
  (h_phase : p.phasePower = q.phasePower)
  (h_op : p.operator = q.operator) : p = q := by
  cases p; cases q; congr

namespace PauliOperator

/-- Convert a Pauli operator to its corresponding matrix representation.
TODO: Add a definition that takes PauliOperators to their corresponding QuantumGate -/
noncomputable def toMatrix : PauliOperator → Matrix QubitBasis QubitBasis ℂ
  | .I => 1
  | .X => Xmat
  | .Y => Ymat
  | .Z => Zmat

/-- The identity operator's matrix is the identity matrix. -/
@[simp] lemma toMatrix_I : PauliOperator.I.toMatrix = (1 : Matrix QubitBasis QubitBasis ℂ) := rfl
@[simp] lemma toMatrix_X : PauliOperator.X.toMatrix = Xmat := rfl
@[simp] lemma toMatrix_Y : PauliOperator.Y.toMatrix = Ymat := rfl
@[simp] lemma toMatrix_Z : PauliOperator.Z.toMatrix = Zmat := rfl

/-- Multiplication of Pauli operators, returning a Pauli group element.

The multiplication rules:
- I is the identity
- X * X = I, Y * Y = I, Z * Z = I
- X * Y = iZ, Y * X = -iZ
- Y * Z = iX, Z * Y = -iX
- Z * X = iY, X * Z = -iY
-/
noncomputable def mulOp : PauliOperator → PauliOperator → PauliGroupElement
  | .I, q => ⟨0, q⟩
  | p, .I => ⟨0, p⟩
  | .X, .X => ⟨0, .I⟩
  | .Y, .Y => ⟨0, .I⟩
  | .Z, .Z => ⟨0, .I⟩
  | .X, .Y => ⟨1, .Z⟩  -- X * Y = iZ
  | .Y, .X => ⟨3, .Z⟩  -- Y * X = -iZ
  | .Y, .Z => ⟨1, .X⟩  -- Y * Z = iX
  | .Z, .Y => ⟨3, .X⟩  -- Z * Y = -iX
  | .Z, .X => ⟨1, .Y⟩  -- Z * X = iY
  | .X, .Z => ⟨3, .Y⟩  -- X * Z = -iY

-- Simp lemmas for mulOp - these only fire on concrete constructors
-- after case analysis, avoiding performance issues with variables
@[simp] lemma mulOp_I_I : PauliOperator.I.mulOp PauliOperator.I = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_I_X : PauliOperator.I.mulOp PauliOperator.X = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_I_Y : PauliOperator.I.mulOp PauliOperator.Y = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_I_Z : PauliOperator.I.mulOp PauliOperator.Z = ⟨0, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_X_I : PauliOperator.X.mulOp PauliOperator.I = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_X_X : PauliOperator.X.mulOp PauliOperator.X = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_X_Y : PauliOperator.X.mulOp PauliOperator.Y = ⟨1, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_X_Z : PauliOperator.X.mulOp PauliOperator.Z = ⟨3, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Y_I : PauliOperator.Y.mulOp PauliOperator.I = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Y_X : PauliOperator.Y.mulOp PauliOperator.X = ⟨3, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_Y_Y : PauliOperator.Y.mulOp PauliOperator.Y = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_Y_Z : PauliOperator.Y.mulOp PauliOperator.Z = ⟨1, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_Z_I : PauliOperator.Z.mulOp PauliOperator.I = ⟨0, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_Z_X : PauliOperator.Z.mulOp PauliOperator.X = ⟨1, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Z_Y : PauliOperator.Z.mulOp PauliOperator.Y = ⟨3, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_Z_Z : PauliOperator.Z.mulOp PauliOperator.Z = ⟨0, PauliOperator.I⟩ := rfl

end PauliOperator

namespace PauliGroupElement

/-- Convert a phase power (0-3) to the corresponding complex phase. -/
def phasePowerToComplex (k : Fin 4) : ℂ :=
  Complex.I ^ (k : ℕ)

@[simp] lemma phasePowerToComplex_0 : phasePowerToComplex 0 = 1 := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_1 : phasePowerToComplex 1 = Complex.I := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_2 : phasePowerToComplex 2 = -1 := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_3 : phasePowerToComplex 3 = -Complex.I := by
  simp  [phasePowerToComplex]

/-- Phase powers add modulo 4: i^(a+b) = i^((a+b) mod 4). -/
lemma phasePowerToComplex_add (a b : Fin 4) :
  phasePowerToComplex a * phasePowerToComplex b = phasePowerToComplex (a + b) := by
  -- Since i^4 = 1, we have i^(a+b) = i^((a+b) mod 4)
  -- Prove by case analysis on all 16 combinations
  fin_cases a <;> fin_cases b <;> simp [phasePowerToComplex]

/-- Matrix multiplication of Pauli operators matches their group multiplication.

This is a fundamental property connecting the abstract group structure with
the matrix representation. For Pauli operators P and Q, if P.mulOp Q = ⟨p, R⟩,
then P.toMatrix * Q.toMatrix = phasePowerToComplex p • R.toMatrix.

This means that multiplying the matrix representations of two Pauli operators
gives the same result as:
1. Multiplying them abstractly using `mulOp` (which may introduce a phase)
2. Converting the result to a matrix and scaling by that phase
-/
lemma PauliOperator.toMatrix_mul (P Q : PauliOperator) :
  P.toMatrix * Q.toMatrix =
  phasePowerToComplex (P.mulOp Q).phasePower • (P.mulOp Q).operator.toMatrix := by
  cases P <;> cases Q <;> simp
  · exact Xmat_mul_Ymat
  · simp only [Xmat_mul_Zmat, neg_smul]
  · simp only [Ymat_mul_Xmat, neg_smul]
  · simp only [Ymat_mul_Zmat]
  · simp only [Zmat_mul_Xmat]
  · simp only [Zmat_mul_Ymat, neg_smul]

/-- Convert a Pauli group element to its matrix representation. -/
noncomputable def toMatrix (p : PauliGroupElement) : Matrix QubitBasis QubitBasis ℂ :=
  phasePowerToComplex p.phasePower • p.operator.toMatrix

/-- The identity element of the Pauli group: I with phase 1. -/
def one : PauliGroupElement := ⟨0, PauliOperator.I⟩

/-- The Pauli operator X with phase 1. -/
def X : PauliGroupElement := ⟨0, PauliOperator.X⟩

/-- The Pauli operator Y with phase 1. -/
def Y : PauliGroupElement := ⟨0, PauliOperator.Y⟩

/-- The Pauli operator Z with phase 1. -/
def Z : PauliGroupElement := ⟨0, PauliOperator.Z⟩

/-- Multiplication in the Pauli group.

If we have `i^k * P` and `i^m * Q`, their product is `i^(k+m+p) * R` where
`P * Q = i^p * R` follows the Pauli operator multiplication rules.
-/
noncomputable def mul (p q : PauliGroupElement) : PauliGroupElement :=
  ⟨p.phasePower + q.phasePower + (p.operator.mulOp q.operator).phasePower,
   (p.operator.mulOp q.operator).operator⟩

/-- The inverse of a Pauli group element.

For `i^k * P`, the inverse is `i^(4-k mod 4) * P` since P * P = I for Pauli operators.
-/
noncomputable def inv (p : PauliGroupElement) : PauliGroupElement :=
  ⟨-p.phasePower, p.operator⟩

/-- Multiplication in the Pauli group. -/
noncomputable instance : Mul PauliGroupElement := ⟨mul⟩

@[simp] lemma mul_eq (p q : PauliGroupElement) : p * q = mul p q := rfl

/-- Inverse in the Pauli group. -/
noncomputable instance : Inv PauliGroupElement := ⟨inv⟩

@[simp] lemma inv_eq (p : PauliGroupElement) : p⁻¹ = inv p := rfl

/-- One element of the Pauli group. -/
instance : One PauliGroupElement := ⟨one⟩

-- Simp lemmas for Pauli group element definitions
@[simp] lemma one_def : (1 : PauliGroupElement) = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma X_def : X = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma Y_def : Y = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma Z_def : Z = ⟨0, PauliOperator.Z⟩ := rfl

/-- The identity group element maps to the identity matrix. -/
@[simp] lemma toMatrix_one : (1 : PauliGroupElement).toMatrix = 1 := by
  simp [toMatrix, one_def, PauliOperator.toMatrix_I, phasePowerToComplex_0]

/-- Group multiplication corresponds to matrix multiplication.

This is the group element version of `PauliOperator.toMatrix_mul`, showing that
the matrix representation is a group homomorphism.
-/
lemma toMatrix_mul (p q : PauliGroupElement) :
  (p * q).toMatrix = p.toMatrix * q.toMatrix := by
  simp [toMatrix, mul, PauliOperator.toMatrix_mul]
  cases p.operator <;> cases q.operator <;>
  simp[← phasePowerToComplex_add, smul_smul, mul_comm, mul_assoc]

/-- Group inverse corresponds to matrix inverse.

Since Pauli matrices are unitary, their matrix inverse equals their group inverse.
-/
lemma toMatrix_inv (p : PauliGroupElement) :
  (p⁻¹).toMatrix = (p.toMatrix)⁻¹ := by
  -- TODO: This requires proving that Pauli group elements are unitary
  -- For now, we can prove it using the fact that p * p⁻¹ = 1 and toMatrix_mul
  sorry

/-- The identity element acts as identity on the right. -/
@[simp] lemma mul_one (p : PauliGroupElement) : p * 1 = p := by
  rcases p with ⟨k, op⟩
  cases op <;> simp[mul]

/-- The identity element acts as identity on the left. -/
@[simp] lemma one_mul (p : PauliGroupElement) : 1 * p = p := by
  rcases p with ⟨k, op⟩
  cases op <;> simp[mul]

/-- Right inverse property: p * p⁻¹ = 1. -/
@[simp] lemma mul_right_inv (p : PauliGroupElement) : p * p⁻¹ = 1 := by
  rcases p with ⟨k, op⟩
  cases op <;> simp[mul, inv]

/-- Left inverse property: p⁻¹ * p = 1. -/
@[simp] lemma mul_left_inv (p : PauliGroupElement) : p⁻¹ * p = 1 := by
  rcases p with ⟨k, op⟩
  cases op <;> simp[mul, inv]

/-- Associativity of Pauli operator multiplication (operator part only). -/
private lemma PauliOperator.mul_assoc_op (P Q R : PauliOperator) :
  ((P.mulOp Q).operator.mulOp R).operator = (P.mulOp (Q.mulOp R).operator).operator := by
  cases P <;> cases Q <;> cases R <;> simp


/-- Associativity of multiplication in the Pauli group. -/
theorem mul_assoc (p q r : PauliGroupElement) : (p * q) * r = p * (q * r) := by
  have h_op : ((p.operator.mulOp q.operator).operator.mulOp r.operator).operator =
              (p.operator.mulOp (q.operator.mulOp r.operator).operator).operator :=
    PauliOperator.mul_assoc_op p.operator q.operator r.operator

  -- Show that the phase calculations are equal using Fin 4 addition associativity
  have h_phase : ((p.phasePower + q.phasePower + (p.operator.mulOp q.operator).phasePower) +
                  r.phasePower +
                  ((p.operator.mulOp q.operator).operator.mulOp r.operator).phasePower) =
                 (p.phasePower +
                 (q.phasePower + r.phasePower + (q.operator.mulOp r.operator).phasePower) +
                  (p.operator.mulOp (q.operator.mulOp r.operator).operator).phasePower) := by
    -- Show phase contributions match by case analysis on operators
    simp[add_assoc, add_comm, add_left_comm]
    cases p.operator <;> cases q.operator <;> cases r.operator <;> simp

  apply PauliGroupElement.ext
  · exact h_phase
  · exact h_op

/-- The Pauli group forms a group under multiplication. -/
noncomputable instance : Group PauliGroupElement where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := mul_left_inv

end PauliGroupElement

end Quantum
