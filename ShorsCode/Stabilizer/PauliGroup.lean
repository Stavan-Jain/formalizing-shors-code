import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Foundations.Basic
import Foundations.Gates
import Foundations.Tensor
import ShorsCode.Stabilizer.PauliGroupSingle

namespace Quantum
open Matrix
open scoped BigOperators

/-!
# The N-Qubit Pauli Group

This section extends the single-qubit Pauli group to n-qubit systems.
An n-qubit Pauli operator is a function from qubit positions to single-qubit Pauli operators.
-/

/-- An n-qubit Pauli operator.

This assigns a single-qubit Pauli operator to each of the n qubits.
The matrix representation is the tensor product (Kronecker product) of the individual
Pauli matrices.
-/
def NQubitPauliOperator (n : ℕ) : Type := Fin n → PauliOperator

variable {n : ℕ}

namespace NQubitPauliOperator

/-- Extensionality for NQubitPauliOperator. -/
@[ext] theorem ext {op₁ op₂ : NQubitPauliOperator n} (h : ∀ i, op₁ i = op₂ i) : op₁ = op₂ :=
  funext h

/-- The identity n-qubit Pauli operator (I ⊗ I ⊗ ... ⊗ I). -/
def identity (n : ℕ) : NQubitPauliOperator n :=
  fun _ => PauliOperator.I

/-- Extract the Pauli operator at a specific qubit position. -/
def get (op : NQubitPauliOperator n) (i : Fin n) : PauliOperator := op i

/-- Set the Pauli operator at a specific qubit position. -/
def set (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
  NQubitPauliOperator n :=
  fun j => if j = i then p else op j

/-- Convert an n-qubit Pauli operator to its matrix representation.

For n qubits, this computes the tensor product (Kronecker product) of the
individual single-qubit Pauli matrices: M_0 ⊗ M_1 ⊗ ... ⊗ M_{n-1}

The matrix entry at (b₁, b₂) where b₁, b₂ : Fin n → QubitBasis is the product
over all qubit positions of the corresponding entries in the individual Pauli matrices:
  ∏_{i : Fin n} (op i).toMatrix (b₁ i) (b₂ i)

This corresponds to the tensor product of the individual Pauli matrices.
-/
noncomputable def toMatrix (op : NQubitPauliOperator n) :
  Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  fun b₁ b₂ => (Finset.univ : Finset (Fin n)).prod (fun i => (op i).toMatrix (b₁ i) (b₂ i))

/-- Construct an n-qubit Pauli operator from a list of Pauli operators.

The list should have length n, and the i-th element specifies the operator on qubit i.
-/
def ofList (ops : List PauliOperator) (h : ops.length = n) :
  NQubitPauliOperator n :=
  fun i => ops.get ⟨i.val, h ▸ i.isLt⟩

/-- Convert an n-qubit Pauli operator to a list. -/
def toList (op : NQubitPauliOperator n) : List PauliOperator :=
  List.ofFn op

end NQubitPauliOperator

/-!
# The N-Qubit Pauli Group Element

An n-qubit Pauli group element consists of a global phase and an n-qubit Pauli operator.
This extends the single-qubit Pauli group to n-qubit systems.
-/

/-- An element of the n-qubit Pauli group.

The n-qubit Pauli group consists of elements of the form `i^k * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})` where:
- `k : Fin 4` represents the global phase: k=0 → 1, k=1 → i, k=2 → -1, k=3 → -i
- `operators : NQubitPauliOperator n` assigns a single-qubit Pauli operator to each qubit

For n qubits, this gives 4 phases × 4^n operators = 4^(n+1) total elements.
-/
structure NQubitPauliGroupElement (n : ℕ) where
  phasePower : Fin 4  -- 0 → 1, 1 → i, 2 → -1, 3 → -i
  operators : NQubitPauliOperator n

/-- Extensionality for NQubitPauliGroupElement. -/
@[ext] theorem NQubitPauliGroupElement.ext {n : ℕ} (p q : NQubitPauliGroupElement n)
  (h_phase : p.phasePower = q.phasePower)
  (h_ops : p.operators = q.operators) : p = q := by
  cases p; cases q; congr

namespace NQubitPauliGroupElement

/-- Convert an n-qubit Pauli group element to its matrix representation.

This multiplies the global phase by the tensor product of the individual Pauli matrices.
-/
noncomputable def toMatrix (p : NQubitPauliGroupElement n) :
  Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  PauliGroupElement.phasePowerToComplex p.phasePower • p.operators.toMatrix

/-- The identity element of the n-qubit Pauli group: I ⊗ I ⊗ ... ⊗ I with phase 1. -/
def one (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨0, NQubitPauliOperator.identity n⟩

/-- Extract the global phase power. -/
def phase (p : NQubitPauliGroupElement n) : Fin 4 := p.phasePower

/-- Extract the n-qubit Pauli operator. -/
def ops (p : NQubitPauliGroupElement n) : NQubitPauliOperator n := p.operators

/-- Get the Pauli operator at a specific qubit position. -/
def getOp (p : NQubitPauliGroupElement n) (i : Fin n) : PauliOperator :=
  p.operators i

/-- Multiplication of n-qubit Pauli operators (operator part only).

This multiplies operators qubit-by-qubit and returns:
- The total phase contribution from all qubit multiplications (mod 4)
- The resulting n-qubit operator (function mapping each qubit to its result operator)
-/
private noncomputable def mulOp (p q : NQubitPauliOperator n) : NQubitPauliGroupElement n :=
  -- Multiply qubit-by-qubit
  let results : Fin n → PauliGroupElement :=
    fun i => (p i).mulOp (q i)
  -- Sum all phase contributions using Fin 4 addition
  let totalPhase := (Finset.univ : Finset (Fin n)).sum (fun i => (results i).phasePower)
  -- Construct result operator
  let resultOp : NQubitPauliOperator n := fun i => (results i).operator
  ⟨totalPhase, resultOp⟩

-- Notation and helper functions for more readable proof states
/-- Notation for operator multiplication: `p *ₚ q` means `mulOp p q`. -/
infixl:70 " *ₚ " => mulOp

/-- Multiplication in the n-qubit Pauli group.

If we have `i^k * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})` and `i^m * (Q₀ ⊗ Q₁ ⊗ ... ⊗ Q_{n-1})`,
their product is computed qubit-by-qubit:
- For each qubit i: P_i * Q_i = i^{p_i} * R_i
- Total phase: k + m + (sum of p_i) mod 4
- Result operator: R₀ ⊗ R₁ ⊗ ... ⊗ R_{n-1}
-/
noncomputable def mul (p q : NQubitPauliGroupElement n) : NQubitPauliGroupElement n :=
  ⟨p.phasePower + q.phasePower + (mulOp p.operators q.operators).phasePower,
  (mulOp p.operators q.operators).operators⟩

/-- The inverse of an n-qubit Pauli group element.

For `i^k * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})`, the inverse is `i^(4-k mod 4) * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})`
since each P_i * P_i = I for Pauli operators, so the operators remain the same and only
the phase is inverted.
-/
noncomputable def inv (p : NQubitPauliGroupElement n) : NQubitPauliGroupElement n :=
  ⟨-p.phasePower, p.operators⟩

/-- Multiplication in the n-qubit Pauli group. -/
noncomputable instance : Mul (NQubitPauliGroupElement n) := ⟨mul⟩

@[simp] lemma mul_eq (p q : NQubitPauliGroupElement n) : p * q = mul p q := rfl

/-- Inverse in the n-qubit Pauli group. -/
noncomputable instance : Inv (NQubitPauliGroupElement n) := ⟨inv⟩

@[simp] lemma inv_eq (p : NQubitPauliGroupElement n) : p⁻¹ = inv p := rfl

/-- One element of the n-qubit Pauli group. -/
noncomputable instance : One (NQubitPauliGroupElement n) := ⟨one n⟩

-- Simp lemmas for n-qubit Pauli group element definitions
@[simp] lemma one_def : (1 : NQubitPauliGroupElement n) = ⟨0, NQubitPauliOperator.identity n⟩ := rfl

/-- Helper: multiplication with identity operator gives no phase contribution. -/
private lemma mulOp_identity_right_phase (op : NQubitPauliOperator n) :
  (mulOp op (NQubitPauliOperator.identity n)).phasePower = 0 := by
  unfold mulOp NQubitPauliOperator.identity
  -- For each qubit i, (op i).mulOp I gives phase 0
  have h : ∀ i, ((op i).mulOp PauliOperator.I).phasePower = 0 := by
    intro i
    cases op i <;> simp
  -- Sum of zeros is zero
  have hsum : (Finset.univ : Finset (Fin n)).sum (fun i => ((op i).mulOp
  PauliOperator.I).phasePower) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simp
  simp [hsum]

private lemma mulOp_identity_left_phase (op : NQubitPauliOperator n) :
  (mulOp (NQubitPauliOperator.identity n) op).phasePower = 0 := by
  unfold mulOp NQubitPauliOperator.identity
  have h : ∀ i, (PauliOperator.I.mulOp (op i)).phasePower = 0 := by
    intro i
    cases op i <;> simp
  have hsum : (Finset.univ : Finset (Fin n)).sum (fun i =>
  (PauliOperator.I.mulOp (op i)).phasePower) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simp
  simp [hsum]


/-- Helper: multiplication with identity operator gives same operator. -/
private lemma mulOp_identity_right_op (op : NQubitPauliOperator n) :
  (mulOp op ((one n).operators)).operators = op := by
  unfold mulOp one NQubitPauliOperator.identity
  ext i
  simp
  cases op i <;> simp

private lemma mulOp_identity_left_op (op : NQubitPauliOperator n) :
  (mulOp (NQubitPauliOperator.identity n) op).operators = op := by
  unfold mulOp NQubitPauliOperator.identity
  ext i
  simp
  cases op i <;> simp

/-- The identity element acts as identity on the right. -/
@[simp] lemma mul_one (p : NQubitPauliGroupElement n) : p * 1 = p := by
  -- Use helper lemmas
  have h_phase : (mulOp p.operators (NQubitPauliOperator.identity n)).phasePower = 0 :=
    mulOp_identity_right_phase p.operators
  have h_op : (mulOp p.operators (NQubitPauliOperator.identity n)).operators = p.operators :=
    mulOp_identity_right_op p.operators
  ext i
  · simp[mul, h_phase]
  · simp[mul, h_op]

/-- The identity element acts as identity on the left. -/
@[simp] lemma one_mul (p : NQubitPauliGroupElement n) : 1 * p = p := by
  have h_phase : (mulOp (NQubitPauliOperator.identity n) p.operators).phasePower = 0 :=
    mulOp_identity_left_phase p.operators
  have h_op : (mulOp (NQubitPauliOperator.identity n) p.operators).operators = p.operators :=
    mulOp_identity_left_op p.operators
  ext i
  · simp[mul, h_phase]
  · simp[mul, h_op]

/-- Helper: self-inverse property for operators. -/
private lemma mulOp_self_inv (op : NQubitPauliOperator n) :
  (mulOp op op).phasePower = 0 ∧ (mulOp op op).operators = NQubitPauliOperator.identity n := by
  constructor
  · unfold mulOp
    -- For each qubit, P_i * P_i = I with phase 0
    have h : ∀ i, ((op i).mulOp (op i)).phasePower = 0 := by
      intro i
      cases op i <;> simp
    have hsum : (Finset.univ : Finset (Fin n)).sum
      (fun i => ((op i).mulOp (op i)).phasePower) = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => h i)]
      simp
    simp [hsum]
  · unfold mulOp NQubitPauliOperator.identity
    ext i
    -- For each Pauli operator P, P * P = I with phase 0
    -- So (P * P).operator = I
    cases h : op i <;> simp [h]

/-- Right inverse property: p * p⁻¹ = 1. -/
@[simp] lemma mul_right_inv (p : NQubitPauliGroupElement n) : p * p⁻¹ = 1 := by
  simp [mul, inv,mulOp_self_inv]

/-- Left inverse property: p⁻¹ * p = 1. -/
@[simp] lemma mul_left_inv (p : NQubitPauliGroupElement n) : p⁻¹ * p = 1 := by
  simp [mul, inv,mulOp_self_inv]

/-- Helper: associativity of n-qubit operator multiplication (operator part only).

This follows from associativity of single-qubit Pauli operator multiplication,
applied qubit-by-qubit.
-/
private lemma mulOp_assoc_op (p q r : NQubitPauliOperator n) :
  (mulOp (mulOp p q).operators r).operators = (mulOp p (mulOp q r).operators).operators := by
  ext i
  -- Apply single-qubit associativity at each qubit position
  -- We prove this by case analysis on each operator, similar to the single-qubit proof
  -- Use case hypotheses to help simp reduce the nested match expressions
  cases h1 : (p i) <;> cases h2 : (q i) <;> cases h3 : (r i) <;> simp [mulOp,h1, h2, h3]

/-- Associativity of multiplication in the n-qubit Pauli group. -/
theorem mul_assoc (p q r : NQubitPauliGroupElement n) : (p * q) * r = p * (q * r) := by
  simp only [mul_eq, mul, mk.injEq]
  -- Operator associativity
  have h_op : ((p.operators *ₚ q.operators).operators *ₚ r.operators).operators =
              (p.operators *ₚ (q.operators *ₚ r.operators).operators).operators :=
    mulOp_assoc_op p.operators q.operators r.operators
  -- Phase associativity: use Fin 4 addition associativity and sum properties
  have h_phase : ((p.phasePower + q.phasePower + (p.operators *ₚ q.operators).phasePower) +
                  r.phasePower +
                  ((p.operators *ₚ q.operators).operators *ₚ r.operators).phasePower) =
                 (p.phasePower +
                 (q.phasePower + r.phasePower + (q.operators *ₚ r.operators).phasePower) +
                  (p.operators *ₚ (q.operators *ₚ r.operators).operators).phasePower) := by
    -- Unfold mulOp to work with sums
    simp[mulOp]
    -- Use associativity of Fin 4 addition
    simp only [add_assoc]
    congr 2
    simp [add_left_comm]
    -- Now we need to show: sum1 + (r.phasePower + sum2) = r.phasePower + (sum3 + sum4)
    -- Rearrange: sum1 + r.phasePower + sum2 = r.phasePower + sum3 + sum4
    -- Cancel r.phasePower: sum1 + sum2 = sum3 + sum4
    -- Combine sums: sum(A+B) = sum(C+D)
    -- Then use single-qubit associativity per qubit
    sorry -- TODO: Complete the proof by combining sums and using single-qubit associativity
  constructor
  · exact h_phase
  · exact h_op

/-- The n-qubit Pauli group forms a group under multiplication. -/
noncomputable instance : Group (NQubitPauliGroupElement n) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := mul_left_inv

end NQubitPauliGroupElement

end Quantum
