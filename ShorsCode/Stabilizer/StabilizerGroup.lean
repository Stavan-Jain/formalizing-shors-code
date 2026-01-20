import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Foundations.Basic
import Foundations.Gates
import Foundations.Tensor
import ShorsCode.Stabilizer.PauliGroupSingle
import ShorsCode.Stabilizer.PauliGroup

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-!
# Stabilizer Groups

This file defines stabilizer groups, which are abelian subgroups of the n-qubit Pauli group
that do not contain -I. Stabilizer groups are fundamental to the stabilizer formalism for
quantum error correction.

A stabilizer group stabilizes a quantum state (or subspace) by consisting of all Pauli group
elements that fix that state with eigenvalue +1.
-/

/-- The negative identity element: -I ⊗ I ⊗ ... ⊗ I.

This is the n-qubit Pauli group element with phase -1 (phasePower = 2) and identity
operators on all qubits.
-/
def negIdentity (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨2, NQubitPauliOperator.identity n⟩

@[simp] lemma negIdentity_phasePower (n : ℕ) : (negIdentity n).phasePower = 2 := rfl

@[simp] lemma negIdentity_operators (n : ℕ) :
  (negIdentity n).operators = NQubitPauliOperator.identity n := rfl

/-!
# Stabilized States

A quantum state is stabilized by a Pauli group element if applying that element
to the state leaves it unchanged (i.e., the state is an eigenvector
with eigenvalue +1).
-/

/-- A vector is stabilized by a Pauli group element if applying the element's matrix
    representation to the vector returns the same vector.

    This means the vector is an eigenvector with eigenvalue +1.
-/
def IsStabilizedVec (g : NQubitPauliGroupElement n) (v : NQubitVec n) : Prop :=
  Matrix.mulVec (g.toMatrix) v = v

/-- A quantum state is stabilized by a Pauli group element if its underlying vector
    is stabilized by that element.

    This means applying the Pauli group element to the state returns the same state.
-/
def IsStabilizedBy (g : NQubitPauliGroupElement n) (ψ : NQubitState n) : Prop :=
  IsStabilizedVec g ψ.val

/-- A stabilizer group is an abelian subgroup of the n-qubit Pauli group that does not contain -I.

Properties:
- It is a subgroup of the n-qubit Pauli group
- It is abelian (all elements commute)
- It does not contain -I
- For an n-qubit system, a stabilizer group can have at most n independent generators
-/
structure StabilizerGroup (n : ℕ) where
  /-- The underlying subgroup of the n-qubit Pauli group. -/
  toSubgroup : Subgroup (NQubitPauliGroupElement n)
  /-- The subgroup is abelian: all elements commute. -/
  is_abelian : ∀ (g h : NQubitPauliGroupElement n) (_ : g ∈ toSubgroup) (_ : h ∈ toSubgroup),
    g * h = h * g
  /-- The stabilizer does not contain -I. -/
  no_neg_identity : negIdentity n ∉ toSubgroup

namespace StabilizerGroup

/-- Coerce a stabilizer group to its underlying subgroup. -/
instance : Coe (StabilizerGroup n) (Subgroup (NQubitPauliGroupElement n)) :=
  ⟨StabilizerGroup.toSubgroup⟩

/-- A quantum state is in the codespace of a stabilizer group if it is stabilized
    by every element in the group.

    The codespace of a stabilizer group consists of all states stabilized by that group.
-/
def IsInCodespace (ψ : NQubitState n) (S : StabilizerGroup n) : Prop :=
  ∀ g ∈ S.toSubgroup, IsStabilizedBy g ψ

/-- The identity element is in every stabilizer group. -/
lemma one_mem (S : StabilizerGroup n) : (1 : NQubitPauliGroupElement n) ∈ S.toSubgroup :=
  S.toSubgroup.one_mem

/-- If g and h are in a stabilizer group, then g * h is also in it. -/
lemma mul_mem (S : StabilizerGroup n) {g h : NQubitPauliGroupElement n}
  (hg : g ∈ S.toSubgroup) (hh : h ∈ S.toSubgroup) : g * h ∈ S.toSubgroup :=
  S.toSubgroup.mul_mem hg hh

/-- If g is in a stabilizer group, then g⁻¹ is also in it. -/
lemma inv_mem (S : StabilizerGroup n) {g : NQubitPauliGroupElement n}
  (hg : g ∈ S.toSubgroup) : g⁻¹ ∈ S.toSubgroup :=
  S.toSubgroup.inv_mem hg

/-- All elements of a stabilizer group commute. -/
lemma commutes (S : StabilizerGroup n) {g h : NQubitPauliGroupElement n}
  (hg : g ∈ S.toSubgroup) (hh : h ∈ S.toSubgroup) : g * h = h * g :=
  S.is_abelian g h hg hh

/-- The negative identity is not in any stabilizer group. -/
lemma neg_identity_not_mem (S : StabilizerGroup n) : negIdentity n ∉ S.toSubgroup :=
  S.no_neg_identity

/-!
# Basic Properties of Stabilized States
-/

/-- The identity element stabilizes all vectors. -/
lemma identity_stabilizes_vec (v : NQubitVec n) :
  IsStabilizedVec (1 : NQubitPauliGroupElement n) v := by
  simp [IsStabilizedVec, NQubitPauliGroupElement.toMatrix]
  -- The identity element has phasePower = 0 (which is 1) and identity operators
  -- So its matrix is 1 • (identity operator matrix) = identity matrix
  -- The identity operator's matrix representation should be the identity matrix
  -- TODO: Prove that NQubitPauliOperator.identity n has identity matrix representation
  -- For now, we use the fact that PauliOperator.I.toMatrix = 1, and tensor product
  -- of identities is identity
  admit

/-- The identity element stabilizes all quantum states. -/
lemma identity_stabilizes (ψ : NQubitState n) : IsStabilizedBy (1 : NQubitPauliGroupElement n) ψ :=
  identity_stabilizes_vec ψ.val

/-- If a state is in the codespace of a stabilizer group, then it is stabilized by the identity. -/
lemma IsInCodespace.identity_stabilizes (ψ : NQubitState n) (S : StabilizerGroup n)
  (h : IsInCodespace ψ S) : IsStabilizedBy (1 : NQubitPauliGroupElement n) ψ := by
  have h_one : (1 : NQubitPauliGroupElement n) ∈ S.toSubgroup := S.one_mem
  exact h (1 : NQubitPauliGroupElement n) h_one

end StabilizerGroup

end Quantum
