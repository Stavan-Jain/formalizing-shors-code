import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Foundations.Basic
import Foundations.Gates
import Mathlib.LinearAlgebra.UnitaryGroup

namespace Quantum
open Matrix

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

namespace PauliOperator

/-- Convert a Pauli operator to its corresponding matrix representation. -/
noncomputable def toMatrix : PauliOperator → Matrix QubitBasis QubitBasis ℂ
  | .I => 1
  | .X => Xmat
  | .Y => Ymat
  | .Z => Zmat

/-- Multiplication of Pauli operators, returning a Pauli group element.

The multiplication rules:
- I is the identity
- X * X = I, Y * Y = I, Z * Z = I
- X * Y = iZ, Y * X = -iZ
- Y * Z = iX, Z * Y = -iX
- Z * X = iY, X * Z = -iY
-/
noncomputable def mulOp : PauliOperator → PauliOperator → (Fin 4 × PauliOperator)
  | .I, q => (0, q)
  | p, .I => (0, p)
  | .X, .X => (0, .I)
  | .Y, .Y => (0, .I)
  | .Z, .Z => (0, .I)
  | .X, .Y => (1, .Z)  -- X * Y = iZ
  | .Y, .X => (3, .Z)  -- Y * X = -iZ
  | .Y, .Z => (1, .X)  -- Y * Z = iX
  | .Z, .Y => (3, .X)  -- Z * Y = -iX
  | .Z, .X => (1, .Y)  -- Z * X = iY
  | .X, .Z => (3, .Y)  -- X * Z = -iY

end PauliOperator

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

namespace PauliGroupElement

/-- Convert a phase power (0-3) to the corresponding complex phase. -/
def phasePowerToComplex (k : Fin 4) : ℂ :=
  Complex.I ^ (k : ℕ)

@[simp] lemma phasePowerToComplex_0 : phasePowerToComplex 0 = 1 := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_1 : phasePowerToComplex 1 = Complex.I := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_2 : phasePowerToComplex 2 = -1 := by
  simp [phasePowerToComplex, Complex.I_sq]

@[simp] lemma phasePowerToComplex_3 : phasePowerToComplex 3 = -Complex.I := by
  simp only [phasePowerToComplex]
  calc Complex.I ^ 3
    _ = Complex.I ^ 2 * Complex.I := by ring
    _ = (-1) * Complex.I := by simp [Complex.I_sq]
    _ = -Complex.I := by ring

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
  let (phaseFromOp, resultOp) := p.operator.mulOp q.operator
  let totalPhaseVal := ((p.phasePower.val + q.phasePower.val + phaseFromOp.val) : ℕ) % 4
  ⟨⟨totalPhaseVal, Nat.mod_lt _ (by norm_num)⟩, resultOp⟩

/-- The inverse of a Pauli group element.

For `i^k * P`, the inverse is `i^(4-k mod 4) * P` since P * P = I for Pauli operators.
-/
noncomputable def inv (p : PauliGroupElement) : PauliGroupElement :=
  let k' := (4 - p.phasePower.val) % 4
  ⟨⟨k', Nat.mod_lt _ (by norm_num)⟩, p.operator⟩

/-- Multiplication in the Pauli group. -/
noncomputable instance : Mul PauliGroupElement := ⟨mul⟩

/-- Inverse in the Pauli group. -/
noncomputable instance : Inv PauliGroupElement := ⟨inv⟩

/-- One element of the Pauli group. -/
instance : One PauliGroupElement := ⟨one⟩

/-- Helper lemma: adding phases modulo 4. -/
private lemma phase_add_mod4 (k m : Fin 4) : ((k.val + m.val) : ℕ) % 4 < 4 :=
  Nat.mod_lt _ (by norm_num)

/-- Associativity of addition modulo 4: `((a + b) % 4 + c) % 4 = (a + (b + c) % 4) % 4`. -/
private lemma mod4_add_assoc (a b c : ℕ) :
  ((a + b) % 4 + c) % 4 = (a + (b + c) % 4) % 4 := by
  calc
    ((a + b) % 4 + c) % 4
      = ((a + b) + c) % 4 := by rw [Nat.mod_add_mod]
    _ = (a + b + c) % 4 := by rw [Nat.add_assoc]
    _ = (a + (b + c)) % 4 := by rw [← Nat.add_assoc]
    _ = ((a % 4) + ((b + c) % 4)) % 4 := by rw [Nat.add_mod]
    _ = (a + (b + c) % 4) % 4 := by rw [Nat.mod_add_mod]

/-- The identity element acts as identity on the right. -/
@[simp] lemma mul_one (p : PauliGroupElement) : p * 1 = p := by
  change mul p one = p
  unfold mul one
  cases h : p.operator <;> simp [PauliOperator.mulOp]
  all_goals
    congr 1
    · simp [Nat.mod_eq_of_lt p.phasePower.isLt]
    · rw [← h]

/-- The identity element acts as identity on the left. -/
@[simp] lemma one_mul (p : PauliGroupElement) : 1 * p = p := by
  change mul one p = p
  unfold mul one
  cases h : p.operator <;> simp [PauliOperator.mulOp]
  all_goals
    congr 1
    · simp [Nat.mod_eq_of_lt p.phasePower.isLt]
    · rw [← h]

/-- Right inverse property: p * p⁻¹ = 1. -/
@[simp] lemma mul_right_inv (p : PauliGroupElement) : p * p⁻¹ = 1 := by
  change mul p (inv p) = one
  unfold mul inv one
  cases h : p.operator with
  | I => {
    simp only [PauliOperator.mulOp]
    congr 1
    · simp only [Fin.ext_iff]
      by_cases hk : p.phasePower.val = 0
      · rw [hk]; simp
      · have h4k : 4 - p.phasePower.val < 4 := by omega
        rw [Nat.mod_eq_of_lt h4k]
        omega
  }
  | X | Y | Z => {
    simp only [PauliOperator.mulOp]
    congr 1
    · simp only [Fin.ext_iff]
      omega
  }

/-- Left inverse property: p⁻¹ * p = 1. -/
@[simp] lemma mul_left_inv (p : PauliGroupElement) : p⁻¹ * p = 1 := by
  change mul (inv p) p = one
  unfold mul inv one
  cases h : p.operator <;> simp only [PauliOperator.mulOp]
  all_goals
    congr 1
    · simp only [Fin.ext_iff]
      omega

/-- Associativity of Pauli operator multiplication (operator part only). -/
private lemma PauliOperator.mul_assoc_op (P Q R : PauliOperator) :
  ((P.mulOp Q).2.mulOp R).2 = (P.mulOp (Q.mulOp R).2).2 := by
  cases P <;> cases Q <;> cases R <;> simp only [PauliOperator.mulOp]


/-- Associativity of multiplication in the Pauli group. -/
theorem mul_assoc (p q r : PauliGroupElement) : (p * q) * r = p * (q * r) := by
  change mul (mul p q) r = mul p (mul q r)
  unfold mul

  have h_op : ((p.operator.mulOp q.operator).2.mulOp r.operator).2 =
              (p.operator.mulOp (q.operator.mulOp r.operator).2).2 :=
    PauliOperator.mul_assoc_op p.operator q.operator r.operator

  have h_phase_val :
    ((p.phasePower.val + q.phasePower.val + (p.operator.mulOp q.operator).1.val) % 4 +
     r.phasePower.val + ((p.operator.mulOp q.operator).2.mulOp r.operator).1.val) % 4 =
    (p.phasePower.val + ((q.phasePower.val + r.phasePower.val +
     (q.operator.mulOp r.operator).1.val) % 4) +
     (p.operator.mulOp (q.operator.mulOp r.operator).2).1.val) % 4 := by
    rcases p.phasePower with ⟨p_phase_val, p_phase_lt⟩
    rcases q.phasePower with ⟨q_phase_val, q_phase_lt⟩
    rcases r.phasePower with ⟨r_phase_val, r_phase_lt⟩
    cases p.operator <;> cases q.operator <;> cases r.operator <;>
    simp only [PauliOperator.mulOp] <;> omega

  have h_phase :
    (⟨((p.phasePower.val + q.phasePower.val + (p.operator.mulOp q.operator).1.val) % 4 +
       r.phasePower.val + ((p.operator.mulOp q.operator).2.mulOp r.operator).1.val) % 4,
      Nat.mod_lt _ (by norm_num)⟩ : Fin 4) =
    (⟨(p.phasePower.val + ((q.phasePower.val + r.phasePower.val +
       (q.operator.mulOp r.operator).1.val) % 4) +
       (p.operator.mulOp (q.operator.mulOp r.operator).2).1.val) % 4,
      Nat.mod_lt _ (by norm_num)⟩ : Fin 4) := by
    simp [Fin.ext_iff]
    exact h_phase_val

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
