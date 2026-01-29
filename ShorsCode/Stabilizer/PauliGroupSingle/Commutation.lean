import Mathlib.Tactic
import ShorsCode.Stabilizer.PauliGroupSingle.Core
import ShorsCode.Stabilizer.PauliGroupSingle.Operator
import ShorsCode.Stabilizer.PauliGroupSingle.Element

namespace Quantum

namespace PauliGroupElement

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
  constructor
  · intro h
    have h_op : (p * q).operator = (q * p).operator := by
      rw [h]
    simp [mul, mul_eq] at h_op
    have h_phase : (p * q).phasePower = (q * p).phasePower := by
      rw [h]
    simp [mul, mul_eq] at h_phase
    ext
    · simp [add_comm] at h_phase
      rw [h_phase]
    · exact h_op
  · intro h
    ext
    · simp [mul, mul_eq]
      have h_phase : (p.operator.mulOp q.operator).phasePower =
                     (q.operator.mulOp p.operator).phasePower := by
        rw [h]
      rw [h_phase, add_comm (p.phasePower) (q.phasePower)]
    · simp [mul, mul_eq]
      have h_op : (p.operator.mulOp q.operator).operator =
                  (q.operator.mulOp p.operator).operator := by
        rw [h]
      exact h_op

/-- Symmetry of commutation: if p commutes with q, then q commutes with p. -/
lemma commutes_symm (p q : PauliGroupElement) :
  (p * q = q * p) ↔ (q * p = p * q) := by
  constructor
  · intro h; symm; exact h
  · intro h; symm; exact h

end PauliGroupElement

end Quantum
