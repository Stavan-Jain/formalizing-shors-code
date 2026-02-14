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

/-- The symplectic vector of the product operator is the pointwise sum (in ZMod 2)
  of the two symplectic vectors. -/
lemma toSymplectic_add (p q : NQubitPauliOperator n) (j : Fin (n + n)) :
    toSymplectic (NQubitPauliGroupElement.mulOp p q).operators j = toSymplectic
    p j + toSymplectic q j := by
  simp only [toSymplectic, NQubitPauliGroupElement.mulOp]
  split_ifs with hj
  · exact congr_arg Prod.fst
      (PauliOperator.toSymplecticSingle_add (p ⟨j.val, hj⟩) (q ⟨j.val, hj⟩))
  · exact congr_arg Prod.snd
      (PauliOperator.toSymplecticSingle_add (p ⟨j.val - n, by omega⟩) (q ⟨j.val - n, by omega⟩))

/-- Two n-qubit Pauli group elements commute iff their symplectic inner product (on the
  operator parts) is 0. The equivalence with the existing `commutes_iff_even_anticommutes`
  is proved later. -/
theorem commutes_iff_symplectic_inner_zero (p q : NQubitPauliGroupElement n) :
    p * q = q * p ↔ symplecticInner p.operators q.operators = 0 := by
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes]
  unfold NQubitPauliOperator.symplecticInner;
  have h_symplecticProductSingle : ∀ P Q : PauliOperator,
  PauliOperator.symplecticProductSingle P Q =
  if (P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2 then 1 else 0 := by
    rintro ( P | P | P | P ) ( Q | Q | Q | Q ) <;> simp +decide;
  rw [ Finset.sum_congr rfl fun i _ => h_symplecticProductSingle _ _ ] ;
  simp [ ZMod ] ;
  rw [ ← even_iff_two_dvd ];
  congr! 2;
  ext; simp [Quantum.NQubitPauliGroupElement.anticommutesAt]

/-- Two n-qubit Pauli group elements anticommute iff their symplectic inner product
  (on the operator parts) is 1. -/
theorem anticommutes_iff_symplectic_inner_one (p q : NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.Anticommute p q ↔ symplecticInner p.operators q.operators = 1 := by
  rw [NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes, Nat.odd_iff]
  unfold symplecticInner
  have h_symplecticProductSingle : ∀ P Q : PauliOperator,
    PauliOperator.symplecticProductSingle P Q =
      if (P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2 then 1 else 0 := by
    rintro ( P | P | P | P ) ( Q | Q | Q | Q ) <;> simp +decide
  rw [Finset.sum_congr rfl fun i _ => h_symplecticProductSingle _ _]
  classical
  have hsum_eq : (Finset.univ : Finset (Fin n)).sum (fun i =>
      if NQubitPauliGroupElement.anticommutesAt p.operators q.operators i then 1 else 0) =
    (Finset.univ : Finset (Fin n)).sum (fun i =>
      if ((p.operators i).mulOp (q.operators i)).phasePower =
        ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 1 else 0) :=
    Finset.sum_congr rfl fun i _ => by congr 1
  have heq : (Finset.filter (NQubitPauliGroupElement.anticommutesAt p.operators q.operators)
      Finset.univ).card = (Finset.univ : Finset (Fin n)).sum (fun i =>
      if NQubitPauliGroupElement.anticommutesAt p.operators q.operators i then 1 else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hcast : ((Finset.univ : Finset (Fin n)).sum (fun i =>
      if ((p.operators i).mulOp (q.operators i)).phasePower =
        ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 1 else 0) : ZMod 2) =
    (Finset.filter (NQubitPauliGroupElement.anticommutesAt p.operators q.operators)
      Finset.univ).card := by norm_cast; rw [← hsum_eq, heq]
  rw [hcast]
  rw [ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]


end NQubitPauliOperator

end Quantum
