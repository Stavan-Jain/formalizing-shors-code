import Mathlib.GroupTheory.Subgroup.Centralizer
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.PauliGroup

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

/-!
# Centralizer of a stabilizer group

The centralizer of a stabilizer group S is the subgroup of the n-qubit Pauli group
consisting of all elements that commute with every element of S. These are exactly
the operators that preserve the codespace (map the codespace to itself). For Pauli
stabilizer groups (no -I), the centralizer coincides with the normalizer.
-/

/-- The centralizer of a stabilizer group: all Pauli elements that commute with
    every element of S. Equivalently, operators that preserve the codespace. -/
def centralizer (S : StabilizerGroup n) : Subgroup (NQubitPauliGroupElement n) :=
  Subgroup.centralizer (S.toSubgroup : Set (NQubitPauliGroupElement n))

/-- Membership in the centralizer is equivalent to commuting with every element
    of the stabilizer group. -/
lemma mem_centralizer_iff (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    g ∈ centralizer S ↔ ∀ h ∈ S.toSubgroup, h * g = g * h :=
  Subgroup.mem_centralizer_iff

/-- Every element of the stabilizer group lies in its centralizer (S is abelian). -/
theorem stabilizer_le_centralizer (S : StabilizerGroup n) :
    S.toSubgroup ≤ centralizer S := by
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  exact (S.is_abelian g h hg hh).symm

end StabilizerGroup
end Quantum
