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

## Structure

A Pauli group element is represented as `i^k * P` where:
- `k : Fin 4` represents the phase: k=0 → 1, k=1 → i, k=2 → -1, k=3 → -i
- `P : PauliOperator` is one of I, X, Y, Z

This gives 4 phases × 4 operators = 16 total elements.

## Key Properties

- The Pauli group forms a group under multiplication
- Matrix representation is a group homomorphism
- All Pauli operators are unitary and Hermitian (except for phase factors)
- The group multiplication rules encode the commutation relations: X*Y = iZ, Y*X = -iZ, etc.
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
- `phasePower : Fin 4` represents the phase:
  - k=0 → phase = 1
  - k=1 → phase = i
  - k=2 → phase = -1
  - k=3 → phase = -i
- `operator : PauliOperator` is one of I, X, Y, Z

This gives 4 phases × 4 operators = 16 total elements.
-/
structure PauliGroupElement where
  phasePower : Fin 4
  operator : PauliOperator
deriving DecidableEq

/-- Extensionality for PauliGroupElement. -/
@[ext] theorem PauliGroupElement.ext (p q : PauliGroupElement)
  (h_phase : p.phasePower = q.phasePower)
  (h_op : p.operator = q.operator) : p = q := by
  cases p; cases q; congr

namespace PauliOperator

/-- Convert a Pauli operator to a quantum gate.

Maps I → I, X → X, Y → Y, Z → Z (the gates defined in Foundations.Gates).
This is the primary representation for operators.
-/
noncomputable def toGate : PauliOperator → OneQubitGate
  | .I => Quantum.I
  | .X => Quantum.X
  | .Y => Quantum.Y
  | .Z => Quantum.Z

/-- Convert a Pauli operator to its corresponding matrix representation.

This is derived from `toGate` by taking the underlying matrix.
-/
noncomputable def toMatrix : PauliOperator → Matrix QubitBasis QubitBasis ℂ
  | .I => 1
  | .X => Xmat
  | .Y => Ymat
  | .Z => Zmat

/-- Connection between `toGate` and `toMatrix` for operators.

The underlying matrix of a gate created from a Pauli operator equals the
operator's matrix representation.
-/
@[simp] lemma toGate_val (P : PauliOperator) : (P.toGate).val = P.toMatrix := by
  cases P <;> simp [toGate, toMatrix, Quantum.coe_I, Quantum.coe_X
  , Quantum.coe_Y, Quantum.coe_Z, Imat]

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
  fin_cases a <;> fin_cases b <;> simp [phasePowerToComplex]

/-- Phase powers add for three terms: i^(a+b+c) = i^a * i^b * i^c. -/
lemma phasePowerToComplex_add3 (a b c : Fin 4) :
  phasePowerToComplex a * phasePowerToComplex b * phasePowerToComplex c =
  phasePowerToComplex (a + b + c) := by
  rw [phasePowerToComplex_add, phasePowerToComplex_add, add_assoc]

/-- The conjugate of a phase power equals the negative phase power: star(i^k) = i^(-k). -/
lemma phasePowerToComplex_star (k : Fin 4) :
  star (phasePowerToComplex k) = phasePowerToComplex (-k) := by
  fin_cases k <;> simp [phasePowerToComplex]
  · rw [← Complex.I_sq]
    rfl
  · symm
    have h : (-3 : Fin 4) = 1 := by decide
    simp [h]

/-- Matrix multiplication of Pauli operators matches their group multiplication.

For Pauli operators P and Q, if P.mulOp Q = ⟨p, R⟩, then
P.toMatrix * Q.toMatrix = phasePowerToComplex p • R.toMatrix.
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

/-- Scalar multiplication by a unit complex number preserves unitarity. -/
lemma mem_unitaryGroup_smul {c : ℂ} {M : Matrix QubitBasis QubitBasis ℂ}
  (h_unit : c * star c = 1) (h_unitary : M ∈ Matrix.unitaryGroup QubitBasis ℂ) :
  c • M ∈ Matrix.unitaryGroup QubitBasis ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [star_eq_conjTranspose, conjTranspose_smul, smul_mul, Matrix.mul_smul]
  rw [← MulAction.mul_smul, h_unit, one_smul]
  exact Matrix.mem_unitaryGroup_iff.1 h_unitary

/-- Phase powers produce unit complex numbers. -/
lemma phasePowerToComplex_isUnit (k : Fin 4) :
  phasePowerToComplex k * star (phasePowerToComplex k) = 1 := by
  fin_cases k <;> simp [phasePowerToComplex]

/-- Convert a Pauli group element to a quantum gate.

This is the primary representation. For `⟨k, P⟩` representing `i^k * P`,
we scale the base gate `P.toGate` by `phasePowerToComplex k`.
-/
noncomputable def toGate (p : PauliGroupElement) : OneQubitGate :=
  ⟨phasePowerToComplex p.phasePower • (PauliOperator.toGate p.operator).val,
   mem_unitaryGroup_smul (phasePowerToComplex_isUnit p.phasePower)
     ((PauliOperator.toGate p.operator).property)⟩

/-- The identity element of the Pauli group: I with phase 1. -/
def one : PauliGroupElement := ⟨0, PauliOperator.I⟩

/-- The Pauli operator X with phase 1. -/
def X : PauliGroupElement := ⟨0, PauliOperator.X⟩

/-- The Pauli operator Y with phase 1. -/
def Y : PauliGroupElement := ⟨0, PauliOperator.Y⟩

/-- The Pauli operator Z with phase 1. -/
def Z : PauliGroupElement := ⟨0, PauliOperator.Z⟩

/-- Multiplication in the Pauli group.

For `i^k * P` and `i^m * Q`, the product is `i^(k+m+p) * R` where
`P * Q = i^p * R` follows the Pauli operator multiplication rules.
-/
noncomputable def mul (p q : PauliGroupElement) : PauliGroupElement :=
  ⟨p.phasePower + q.phasePower + (p.operator.mulOp q.operator).phasePower,
   (p.operator.mulOp q.operator).operator⟩

/-- The inverse of a Pauli group element.

For `i^k * P`, the inverse is `i^(-k) * P` since P * P = I for Pauli operators.
-/
noncomputable def inv (p : PauliGroupElement) : PauliGroupElement :=
  ⟨-p.phasePower, p.operator⟩

noncomputable instance : Mul PauliGroupElement := ⟨mul⟩
noncomputable instance : Inv PauliGroupElement := ⟨inv⟩
instance : One PauliGroupElement := ⟨one⟩

@[simp] lemma mul_eq (p q : PauliGroupElement) : p * q = mul p q := rfl
@[simp] lemma inv_eq (p : PauliGroupElement) : p⁻¹ = inv p := rfl
@[simp] lemma one_def : (1 : PauliGroupElement) = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma X_def : X = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma Y_def : Y = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma Z_def : Z = ⟨0, PauliOperator.Z⟩ := rfl

/-- Convert a Pauli group element to its matrix representation.

This is derived from `toGate` by taking the underlying matrix.
-/
@[simp] noncomputable def toMatrix (p : PauliGroupElement) : Matrix QubitBasis QubitBasis ℂ :=
  (toGate p).val

/-- Connection between `toGate` and `toMatrix`. -/
lemma toGate_val (p : PauliGroupElement) : (toGate p).val = toMatrix p := rfl

/-- The identity group element maps to the identity matrix. -/
@[simp] lemma toMatrix_one : toMatrix (1 : PauliGroupElement) = 1 := by
  simp [toMatrix, toGate,
  one_def, PauliOperator.toGate, phasePowerToComplex_0, Quantum.coe_I, Imat]

/-- All Pauli group element matrices are unitary. -/
lemma toMatrix_mem_unitaryGroup (p : PauliGroupElement) :
  toMatrix p ∈ Matrix.unitaryGroup QubitBasis ℂ :=
  (toGate p).property

/-- The identity Pauli group element maps to the identity gate. -/
@[simp] lemma toGate_one : toGate (1 : PauliGroupElement) = (1 : OneQubitGate) := by
  apply Subtype.ext
  rw [toGate_val, toMatrix_one]
  rfl

/-- Group multiplication corresponds to matrix multiplication.

The matrix representation is a group homomorphism: `toMatrix (p * q) = toMatrix p * toMatrix q`.
-/
lemma toMatrix_mul (p q : PauliGroupElement) :
  toMatrix (p * q) = toMatrix p * toMatrix q := by
  simp only [toMatrix, toGate]
  simp [smul_smul, mul]
  rw [PauliOperator.toMatrix_mul]
  simp [smul_smul, mul_comm (phasePowerToComplex q.phasePower)]
  rw [phasePowerToComplex_add3]


/-- `toGate` is a group homomorphism. -/
lemma toGate_mul (p q : PauliGroupElement) : toGate (p * q) = toGate p * toGate q := by
  ext
  rw [toGate_val]
  have h_mul_val : (toGate p * toGate q).val = (toGate p).val * (toGate q).val := rfl
  rw [h_mul_val, toGate_val, toGate_val]
  exact congrFun (congrFun (toMatrix_mul p q) _) _

/-- `toGate` preserves inverse. -/
lemma toGate_inv (p : PauliGroupElement) : toGate (p⁻¹) = (toGate p)⁻¹ := by
  apply Subtype.ext
  -- Show the underlying matrices are equal: toMatrix (p⁻¹) = star (toMatrix p)
  -- Goal: (toGate (p⁻¹)).val = ((toGate p)⁻¹).val
  rw [toGate_val]
  -- Goal: toMatrix (p⁻¹) = ((toGate p)⁻¹).val
  rw [gate_inv_val (toGate p)]
  -- Goal: toMatrix (p⁻¹) = star (toGate p).val
  rw [toGate_val]
  -- Goal: toMatrix (p⁻¹) = star (toMatrix p)
  -- Expand both sides
  simp only [toMatrix, toGate]
  -- Goal: phasePowerToComplex (-p.phasePower) • ↑(p.operator.toGate) =
  --       star (phasePowerToComplex p.phasePower • ↑(p.operator.toGate))
  -- Star distributes over scalar multiplication: star (c • M) = star c • star M
  rw [star_smul]
  -- Goal: phasePowerToComplex (-p.phasePower) • ↑(p.operator.toGate) =
  --       star (phasePowerToComplex p.phasePower) • star ↑(p.operator.toGate)

  rw [phasePowerToComplex_star]
  -- Goal: phasePowerToComplex (-p.phasePower) • ↑(p.inv.operator.toGate) =
  --       phasePowerToComplex (-p.phasePower) • star ↑(p.operator.toGate)
  -- First, simplify p.inv.operator = p.operator (since inv doesn't change the operator)
  simp [inv]
  -- Goal: phasePowerToComplex (-p.phasePower) • p.operator.toMatrix =
  --       phasePowerToComplex (-p.phasePower) • star (p.operator.toMatrix)
  -- Cancel the common scalar factor using congr
  congr 1
  -- Goal: p.operator.toMatrix = star (p.operator.toMatrix)
  -- This follows from Pauli operators being Hermitian: star (P.toMatrix) = P.toMatrix
  -- Prove by case analysis on the operator
  cases p.operator <;> simp [PauliOperator.toMatrix, star_eq_conjTranspose]
  · matrix_expand[Xmat]
  · matrix_expand[Ymat]
  · matrix_expand[Zmat]

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

  have h_phase : ((p.phasePower + q.phasePower + (p.operator.mulOp q.operator).phasePower) +
                  r.phasePower +
                  ((p.operator.mulOp q.operator).operator.mulOp r.operator).phasePower) =
                 (p.phasePower +
                 (q.phasePower + r.phasePower + (q.operator.mulOp r.operator).phasePower) +
                  (p.operator.mulOp (q.operator.mulOp r.operator).operator).phasePower) := by
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

/-- Group inverse corresponds to matrix inverse. -/
lemma toMatrix_inv (p : PauliGroupElement) :
  toMatrix (p⁻¹) = (toMatrix p)⁻¹ := by
  have h_gate : toGate (p⁻¹) = (toGate p)⁻¹ := toGate_inv p
  have h_val : (toGate (p⁻¹)).val = ((toGate p)⁻¹).val := by rw [h_gate]
  rw [toGate_val, gate_inv_val (toGate p), toGate_val] at h_val
  rw [h_val, ← toGate_val, ← gate_val_inv (toGate p), toGate_val]

/-!
# Commutation Properties

Two Pauli group elements commute if their operators commute (which happens when
the operators are equal or one is the identity). The phase factors don't affect
commutation since they're scalars.
-/

/-- Two single-qubit Pauli operators commute if and only if they are equal or one is I. -/
lemma PauliOperator.commutes_iff (P Q : PauliOperator) :
  P.mulOp Q = Q.mulOp P ↔ (P = Q ∨ P = PauliOperator.I ∨ Q = PauliOperator.I) := by
  cases P <;> cases Q <;> simp

/-- Two Pauli group elements commute if and only if their operators commute. -/
lemma commutes_iff (p q : PauliGroupElement) :
  p * q = q * p ↔ p.operator.mulOp q.operator = q.operator.mulOp p.operator := by
  sorry


/-- Symmetry of commutation: if p commutes with q, then q commutes with p. -/
lemma commutes_symm (p q : PauliGroupElement) :
  (p * q = q * p) ↔ (q * p = p * q) := by
  constructor
  · intro h; symm; exact h
  · intro h; symm; exact h

end PauliGroupElement

end Quantum
