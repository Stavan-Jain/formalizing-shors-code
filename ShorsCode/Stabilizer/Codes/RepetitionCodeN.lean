import Mathlib.Tactic
import ShorsCode.Stabilizer.Core.StabilizerGroup
import ShorsCode.Stabilizer.Core.SubgroupLemmas
import ShorsCode.Stabilizer.Core.CSSNoNegI
import ShorsCode.Stabilizer.PauliGroup.Commutation

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace RepetitionCodeN

/-!
# Parametric repetition code (Z-only CSS) on `n+2` qubits

This is a parametric version of `RepetitionCode3`, defined on **`n+2` qubits** to make the
adjacent-pair indexing clean.

Generators (Z-checks):
`Z_i Z_{i+1}` for `i : Fin (n+1)`, acting on qubits `i` and `i+1`.

We show the generated subgroup is a `StabilizerGroup (n+2)`:
- **abelian**: all generators are Z-type
- **no `-I`**: apply the reusable CSS lemma with `XGenerators = ∅`
-/

open NQubitPauliGroupElement

/-!
## Generators
-/

/-- The adjacent Z-check `Z_i Z_{i+1}` on `n+2` qubits, indexed by `i : Fin (n+1)`. -/
def ZPair (n : ℕ) (i : Fin (n + 1)) : NQubitPauliGroupElement (n + 2) :=
  ⟨0,
    ((NQubitPauliOperator.identity (n + 2)).set (Fin.castSucc i) PauliOperator.Z)
      |>.set (Fin.succ i) PauliOperator.Z⟩

def ZGenerators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  Set.range (ZPair n)

def XGenerators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  (∅ : Set (NQubitPauliGroupElement (n + 2)))

def generators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  ZGenerators n ∪ XGenerators n

def subgroup (n : ℕ) : Subgroup (NQubitPauliGroupElement (n + 2)) :=
  Subgroup.closure (generators n)

/-!
## Typing: Z-type generators
-/

lemma ZGenerators_are_ZType (n : ℕ) :
    ∀ g, g ∈ ZGenerators n → NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  intro g hg
  rcases hg with ⟨i, rfl⟩
  refine ⟨rfl, ?_⟩
  intro j
  -- The operator is `Z` at `i` and `i+1`, and `I` elsewhere.
  by_cases h1 : j = Fin.succ i
  · subst h1
    exact Or.inr (by simp [ZPair, NQubitPauliOperator.set])
  · by_cases h2 : j = Fin.castSucc i
    · subst h2
      -- Here we use `h1 : castSucc i ≠ succ i` to simplify the outer `set`.
      exact Or.inr (by simp [ZPair, NQubitPauliOperator.set, h1])
    · -- Otherwise the operator is `I`.
      simp [ZPair, NQubitPauliOperator.set, NQubitPauliOperator.identity, h1, h2,
        PauliOperator.IsZType]

/-!
## Abelian: commutation of the generated subgroup
-/

private lemma ZType_commutes {m : ℕ} {g h : NQubitPauliGroupElement m}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  classical
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  have hg' := hg.2 k
  have hh' := hh.2 k
  rcases hg' with hgI | hgZ <;> rcases hh' with hhI | hhZ
  · simp [PauliOperator.mulOp, hgI, hhI]
  · simp [PauliOperator.mulOp, hgI, hhZ]
  · simp [PauliOperator.mulOp, hgZ, hhI]
  · simp [PauliOperator.mulOp, hgZ, hhZ]

theorem generators_commute (n : ℕ) :
    ∀ g ∈ generators n, ∀ h ∈ generators n, g * h = h * g := by
  classical
  intro g hg h hh
  -- Since `XGenerators = ∅`, membership reduces to `ZGenerators`.
  simp [generators, XGenerators] at hg hh
  exact ZType_commutes (ZGenerators_are_ZType n g hg) (ZGenerators_are_ZType n h hh)

theorem subgroup_is_abelian (n : ℕ) :
    ∀ g ∈ subgroup n, ∀ h ∈ subgroup n, g * h = h * g := by
  simpa [subgroup] using
    (Subgroup.abelian_closure_of_pairwise_commute (G := NQubitPauliGroupElement (n + 2))
      (generators n) (generators_commute n))

/-!
## No `-I` in the generated subgroup (CSS lemma with empty X-generators)
-/

theorem negIdentity_not_mem (n : ℕ) :
    negIdentity (n + 2) ∉ subgroup n := by
  have hX :
      ∀ x, x ∈ XGenerators n → NQubitPauliGroupElement.IsXTypeElement x := by
    intro x hx
    simp [XGenerators] at hx
  have hZX :
      ∀ z ∈ ZGenerators n, ∀ x ∈ XGenerators n, z * x = x * z := by
    intro z hz x hx
    simp [XGenerators] at hx
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (n := n + 2) (ZGenerators n) (XGenerators n)
      (ZGenerators_are_ZType n) hX hZX)

/-!
## Bundled `StabilizerGroup (n+2)`
-/

noncomputable def stabilizerGroup (n : ℕ) : StabilizerGroup (n + 2) :=
{ toSubgroup := subgroup n
, is_abelian := by
    intro g h hg hh
    exact subgroup_is_abelian n g hg h hh
, no_neg_identity := by
    simpa using negIdentity_not_mem n }

end RepetitionCodeN
end StabilizerGroup

end Quantum

