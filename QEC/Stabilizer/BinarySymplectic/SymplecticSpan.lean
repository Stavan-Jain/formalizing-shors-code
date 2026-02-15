import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum

variable {n : ℕ}

/-!
# Symplectic span and closure

For phase-0 stabilizer generators given as a list `L`, the subgroup closure equals
(the operator parts corresponding to) the F₂-linear span of their symplectic vectors.
So "logical L ∉ subgroup" reduces to "symp(L.operators) ∉ sympSpan(generators)".
-/

namespace NQubitPauliGroupElement

open NQubitPauliOperator
open Submodule

/-- The F₂-submodule spanned by the symplectic vectors (rows) of the check matrix of `L`. -/
def sympSpan (L : List (NQubitPauliGroupElement n)) : Submodule (ZMod 2) (Fin (n + n) → ZMod 2) :=
  span (ZMod 2) (Set.range (checkMatrix L))

/-- The symplectic vector of the identity operator is the zero vector. -/
lemma toSymplectic_one_operators : toSymplectic (1 : NQubitPauliGroupElement n).operators = 0 := by
  ext j
  simp only [NQubitPauliGroupElement.one_operators_def, toSymplectic, Pi.zero_apply,
    NQubitPauliOperator.identity, PauliOperator.toSymplecticSingle_I]
  split_ifs <;> rfl

/-- The inverse has the same operator part, so the same symplectic vector. -/
lemma toSymplectic_inv_operators (g : NQubitPauliGroupElement n) :
    toSymplectic (g⁻¹).operators = toSymplectic g.operators := by
  simp only [NQubitPauliGroupElement.inv_eq, NQubitPauliGroupElement.inv]

/-- If `g` is in the list `L`, then its symplectic vector is a row of the check matrix. -/
lemma mem_listToSet_symp_in_range (L : List (NQubitPauliGroupElement n))
    (g : NQubitPauliGroupElement n) (hg : g ∈ listToSet L) :
    toSymplectic g.operators ∈ Set.range (checkMatrix L) := by
  rw [listToSet, Set.mem_setOf] at hg
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  use i
  have h_row : checkMatrix L i = toSymplectic (L.get i).operators := by ext j; rfl
  rw [h_row, congr_arg (fun e => toSymplectic e.operators) hi]

/-- For phase-0 generators, closure is contained in the symplectic span:
  if `g ∈ Subgroup.closure (listToSet L)` then `toSymplectic g.operators ∈ sympSpan L`. -/
theorem mem_closure_implies_symp_in_span (L : List (NQubitPauliGroupElement n))
    (_ : AllPhaseZero L) (g : NQubitPauliGroupElement n)
    (hg : g ∈ Subgroup.closure (listToSet L)) :
    toSymplectic g.operators ∈ sympSpan L := by
  refine Subgroup.closure_induction
    (p := fun (k : NQubitPauliGroupElement n) _ => toSymplectic k.operators ∈ sympSpan L)
    (fun k hk => subset_span (mem_listToSet_symp_in_range L k hk))
    (by change (1 : NQubitPauliGroupElement n).operators.toSymplectic ∈ sympSpan L
        rw [toSymplectic_one_operators]; exact zero_mem _)
    (fun x y _ _ hx hy => ?_)
    (fun x _ hx => ?_)
    hg
  · change (x * y).operators.toSymplectic ∈ sympSpan L
    have heq : (x * y).operators.toSymplectic =
        x.operators.toSymplectic + y.operators.toSymplectic := by
      ext j
      have h_mul_op : (NQubitPauliGroupElement.mul x y).operators =
          (NQubitPauliGroupElement.mulOp x.operators y.operators).operators := rfl
      rw [NQubitPauliGroupElement.mul_eq, h_mul_op, toSymplectic_add]
      conv_rhs => rw [Pi.add_apply]
    rw [heq]
    exact add_mem hx hy
  · change (x⁻¹).operators.toSymplectic ∈ sympSpan L
    rw [toSymplectic_inv_operators]
    exact hx

/-- Linear relation on the span: zero/add/smul cases are handled once. To prove
  ∀ v ∈ sympSpan L, (Finset.sum indices fun j => v j) = 0, it suffices to prove that
  each row of the check matrix sums to 0 on `indices` (the mem case). -/
theorem sympSpan_sum_eq_zero (L : List (NQubitPauliGroupElement n)) (indices : Finset (Fin (n + n)))
    (h_mem : ∀ k : Fin L.length, Finset.sum indices (fun j => (checkMatrix L k) j) = 0) :
    ∀ v ∈ sympSpan L, Finset.sum indices (fun j => v j) = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    rw [← hk]
    exact h_mem k
  | zero => simp only [Pi.zero_apply, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hx, hy, zero_add]
  | smul a x _ hx =>
    simp only [Pi.smul_apply]
    rw [Finset.sum_congr rfl fun j _ => smul_eq_mul (a := a) (x j)]
    rw [← Finset.mul_sum]
    rw [hx, mul_zero]

/-- Generic "logical not in subgroup" via symplectic span: if `L` has phase 0 and its
  symplectic vector is not in the span of the generators' symplectic vectors, then
  `L` is not in the subgroup closure. -/
theorem not_mem_closure_of_symp_not_in_span (L : List (NQubitPauliGroupElement n))
    (hPhase : AllPhaseZero L) (g : NQubitPauliGroupElement n) (_ : g.phasePower = 0)
    (hg_symp : toSymplectic g.operators ∉ sympSpan L) :
    g ∉ Subgroup.closure (listToSet L) := by
  intro h
  exact hg_symp (mem_closure_implies_symp_in_span L hPhase g h)

/-- When `Subgroup.closure (listToSet L) = H`, use this to reduce "g ∉ H" to
  "g's symplectic vector is not in sympSpan L". Cuts boilerplate per code. -/
theorem not_mem_subgroup_of_symp_not_in_span (L : List (NQubitPauliGroupElement n))
    (H : Subgroup (NQubitPauliGroupElement n)) (h_eq : Subgroup.closure (listToSet L) = H)
    (hPhase : AllPhaseZero L) (g : NQubitPauliGroupElement n) (hg_phase : g.phasePower = 0)
    (hg_symp : toSymplectic g.operators ∉ sympSpan L) : g ∉ H := by
  rw [← h_eq]
  exact not_mem_closure_of_symp_not_in_span L hPhase g hg_phase hg_symp

end NQubitPauliGroupElement

end Quantum
