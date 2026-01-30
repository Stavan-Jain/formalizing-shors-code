import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import ShorsCode.Foundations.Foundations
import ShorsCode.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

namespace NQubitPauliGroupElement

/-!
# Commutation Properties

Two n-qubit Pauli group elements commute if they commute qubit-wise.
The phase factors don't affect commutation since they're scalars.
-/

/-!
## Helper Lemmas for Commutation Proofs
-/

/-- The operator at qubit i in the result of mulOp is the operator from the
    single-qubit multiplication. -/
private lemma mulOp_operators_at (p q : NQubitPauliOperator n) (i : Fin n) :
  (mulOp p q).operators i = ((p i).mulOp (q i)).operator := rfl

/-- The phase power in mulOp is the sum of phase powers from all qubit multiplications. -/
private lemma mulOp_phasePower (p q : NQubitPauliOperator n) :
  (mulOp p q).phasePower =
    (Finset.univ : Finset (Fin n)).sum (fun i => ((p i).mulOp (q i)).phasePower) := rfl

/-- If two functions are equal pointwise, their sums over Finset.univ are equal. -/
private lemma sum_eq_of_pointwise_eq {α : Type*} [AddCommMonoid α] {f g : Fin n → α}
  (h : ∀ i, f i = g i) :
  (Finset.univ : Finset (Fin n)).sum f = (Finset.univ : Finset (Fin n)).sum g :=
  Finset.sum_congr rfl (fun i _ => h i)

/-- If operators commute qubit-wise, then the phase contributions are equal at each qubit. -/
private lemma phasePower_eq_of_commutes_qubitwise {p q : NQubitPauliOperator n}
  (h : ∀ i : Fin n, (p i).mulOp (q i) = (q i).mulOp (p i)) :
  ∀ i : Fin n, ((p i).mulOp (q i)).phasePower = ((q i).mulOp (p i)).phasePower := by
  intro i
  rw [h i]

/-- If operators commute qubit-wise, then the total phase contributions are equal. -/
private lemma mulOp_phasePower_eq_of_commutes_qubitwise {p q : NQubitPauliOperator n}
  (h : ∀ i : Fin n, (p i).mulOp (q i) = (q i).mulOp (p i)) :
  (mulOp p q).phasePower = (mulOp q p).phasePower := by
  simp [mulOp_phasePower]
  apply sum_eq_of_pointwise_eq
  exact phasePower_eq_of_commutes_qubitwise h

/-- If operators commute qubit-wise, then the operators are equal at each qubit. -/
private lemma mulOp_operators_eq_of_commutes_qubitwise {p q : NQubitPauliOperator n}
  (h : ∀ i : Fin n, (p i).mulOp (q i) = (q i).mulOp (p i)) :
  ∀ i : Fin n, (mulOp p q).operators i = (mulOp q p).operators i := by
  intro i
  simp [mulOp_operators_at]
  rw [h i]

/-- The `operators` part of n-qubit Pauli group multiplication is commutative
(phase factors may differ). -/
lemma operators_mul_comm (p q : NQubitPauliGroupElement n) :
    (p * q).operators = (q * p).operators := by
  ext i
  simp [mul, mul_eq, mulOp_operators_at, PauliOperator.mulOp_operator_comm]

/-- Two n-qubit Pauli group elements commute if they commute at every qubit position. -/
lemma commutes_of_componentwise_commutes (p q : NQubitPauliGroupElement n) :
  (∀ i : Fin n,
  (p.operators i).mulOp (q.operators i) = (q.operators i).mulOp (p.operators i))
  → p * q = q * p := by
    intro h
    ext
    · simp [mul, mul_eq]
      rw [mulOp_phasePower_eq_of_commutes_qubitwise h]
      simp [add_comm]
    · simp [mul, mul_eq]
      rw [mulOp_operators_eq_of_commutes_qubitwise h]

/-- Every element commutes with itself. -/
lemma commutes_refl (p : NQubitPauliGroupElement n) : p * p = p * p := rfl

/-- Symmetry of commutation: if p commutes with q, then q commutes with p. -/
lemma commutes_symm (p q : NQubitPauliGroupElement n) :
  (p * q = q * p) ↔ (q * p = p * q) := by
  constructor
  · intro h; symm; exact h
  · intro h; symm; exact h

/-- The identity element commutes with all elements. -/
lemma commutes_one_left (p : NQubitPauliGroupElement n) : 1 * p = p * 1 := by
  rw [one_mul, mul_one]

/-- All elements commute with the identity. -/
lemma commutes_one_right (p : NQubitPauliGroupElement n) : p * 1 = 1 * p := by
  rw [mul_one, one_mul]

/-- If one element is the identity, they commute. -/
lemma commutes_if_one_identity_left (p : NQubitPauliGroupElement n) :
  (1 : NQubitPauliGroupElement n) * p = p * (1 : NQubitPauliGroupElement n) :=
  commutes_one_left p

/-- If one element is the identity, they commute. -/
lemma commutes_if_one_identity_right (p : NQubitPauliGroupElement n) :
  p * (1 : NQubitPauliGroupElement n) = (1 : NQubitPauliGroupElement n) * p :=
  commutes_one_right p

end NQubitPauliGroupElement

end Quantum
