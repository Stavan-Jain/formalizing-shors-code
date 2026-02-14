import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.PauliGroupSingle
import QEC.Stabilizer.PauliGroupSingle.Commutation
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement
import QEC.Stabilizer.PauliGroup.Commutation

namespace Quantum

open scoped BigOperators

variable {n : ℕ}

/-!
# Symplectic inner product

The symplectic inner product ⟨v,w⟩_s = (X-part of v)·(Z-part of w) + (Z-part of v)·(X-part of w)
in ZMod 2. Two Pauli group elements commute iff their symplectic inner product is 0.
-/

namespace PauliOperator

/-- Single-qubit symplectic product: 0 iff P and Q commute. -/
def symplecticProductSingle (P Q : PauliOperator) : ZMod 2 :=
  P.toSymplecticSingle.1 * Q.toSymplecticSingle.2 + P.toSymplecticSingle.2 * Q.toSymplecticSingle.1

lemma symplecticProductSingle_eq_zero_iff_commute (P Q : PauliOperator) :
    symplecticProductSingle P Q = 0 ↔ P.mulOp Q = Q.mulOp P := by
  cases P <;> cases Q <;>
    simp [symplecticProductSingle]
  rfl

end PauliOperator

namespace NQubitPauliOperator

/-- Symplectic inner product of two n-qubit Pauli operators (sum over qubits, in ZMod 2).
  Zero iff the two operators commute (as n-qubit Pauli group elements). -/
def symplecticInner (op₁ op₂ : NQubitPauliOperator n) : ZMod 2 :=
  (Finset.univ : Finset (Fin n)).sum (fun i =>
    PauliOperator.symplecticProductSingle (op₁ i) (op₂ i))

/-- Two n-qubit Pauli group elements commute iff their symplectic inner product (on the
  operator parts) is 0. The equivalence with the existing `commutes_iff_even_anticommutes`
  is proved later. -/
theorem commutes_iff_symplectic_inner_zero (p q : NQubitPauliGroupElement n) :
    p * q = q * p ↔ symplecticInner p.operators q.operators = 0 := by
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes]
  sorry  -- symplecticInner = 0 ↔ Even (card of anticommuting qubits)

end NQubitPauliOperator

end Quantum
