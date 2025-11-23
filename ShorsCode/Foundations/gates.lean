import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Foundations.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

namespace Quantum
open Matrix

-- basis/index type
abbrev QuantumGate (α : Type*) [DecidableEq α] [Fintype α] :=
  Matrix.unitaryGroup α ℂ

abbrev OneQubitGate : Type :=
  QuantumGate QubitBasis   -- i.e. Matrix.unitaryGroup (Fin 2) ℂ

abbrev TwoQubitGate : Type := QuantumGate TwoQubitBasis

-- Change this later when I generalize QuantumStates
abbrev NQubitGate (n : ℕ) :=
  QuantumGate (Fin (2^n))

open Lean.Parser.Tactic in
open Lean in
/--
Proves goals equating small matrices by expanding out products and simpliying
standard Real arithmetic.
-/
syntax (name := matrix_expand) "matrix_expand"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (" with " rcasesPat+)? : tactic

macro_rules
  | `(tactic| matrix_expand $[[$rules,*]]? $[with $withArg*]?) => do
    let id1 := (withArg.getD ⟨[]⟩).getD 0 (← `(rcasesPat| _))
    let id2 := (withArg.getD ⟨[]⟩).getD 1 (← `(rcasesPat| _))
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      ext i j
      repeat rcases (i : Prod _ _) with ⟨i, $id1⟩
      repeat rcases (j : Prod _ _) with ⟨j, $id2⟩
      fin_cases i
      <;> fin_cases j
      <;> simp [Complex.ext_iff,
        Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
        $rules',* ]
      <;> norm_num
      <;> try field_simp
      <;> try ring_nf
      ))

open Lean.Parser.Tactic in
open Lean in

/--
`vec_expand`:
- turns equality between vectors (functions) into pointwise goals with `ext`,
- case-splits on small index types (`Fin n`, products like `QubitBasis × k`).

It does *not* call `simp` itself; it just prepares the goals for you.
-/
syntax (name := vec_expand) "vec_expand" : tactic

macro_rules
  | `(tactic| vec_expand) => `(
    tactic| (
      ext i
      -- If the index is a pair, split it and case-split each component.
      first
        | (rcases i with ⟨i₁, i₂⟩
           <;> fin_cases i₁
           <;> fin_cases i₂)
        | (fin_cases i)
    ))
open Lean.Parser.Tactic in
open Lean in
/--
`vec_expand_simp [rules]`:
- runs `vec_expand` (ext + case-split),
- then solves each goal with `simp [rules]`.
-/
syntax (name := vec_expand_simp) "vec_expand_simp"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| vec_expand_simp $[[$rules,*]]?) => do
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      vec_expand
      all_goals
        simp [$rules',*]
    ))


noncomputable abbrev applyMatrixVec' {α : Type*}
  [Fintype α] [DecidableEq α] :
  Matrix α α ℂ → (α → ℂ) → (α → ℂ) :=
  Matrix.mulVec

noncomputable abbrev applyMatrixVec
  {α : Type*} [Fintype α] [DecidableEq α] :
  Matrix α α ℂ → Vector α → Vector α :=
  Matrix.mulVec


lemma gate_preserves_norm
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  ∀ v : Vector α, norm (Matrix.mulVec (G.val) v) = norm v :=
by
  -- we'll prove this later using the fact that G is unitary
  admit

noncomputable def applyGate
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  QuantumState α :=
by
  refine
    { val := applyMatrixVec (G.val) ψ.val
    , property := ?_ }
  have h := gate_preserves_norm G ψ.val
  rw [ψ.property] at h
  exact h

def Hermitian {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) : Prop :=
  Mᴴ = M

@[simp] lemma Hermitian_def {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) :
  Hermitian M ↔ Mᴴ = M := Iff.rfl

def Involutary {α : Type*} [Fintype α] [DecidableEq α]
  (M : Matrix α α ℂ) : Prop :=
  M * M = 1

@[simp] lemma Involutary_def {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
  Involutary M ↔ M * M = 1 := Iff.rfl

/-- If a matrix is Hermitian and involutary, then it is unitary (in the sense U
Uᴴ = 1 and Uᴴ U = 1). -/
lemma unitary_of_hermitian_involutary
  {α : Type*} [Fintype α] [DecidableEq α]
  {U : Matrix α α ℂ}
  (hH : Hermitian U) (hI : Involutary U) :
  (U * Uᴴ = 1) ∧ (Uᴴ * U = 1) := by
  have hH' : Uᴴ = U := hH
  refine ⟨?left, ?right⟩
  · simpa [hH'] using hI
  · simpa [hH'] using hI

/- Pauli X matrix -/
def Xmat : Matrix QubitBasis QubitBasis ℂ := !![0, 1; 1, 0]

lemma Xmat_hermitian : Hermitian Xmat := by matrix_expand[Xmat]

lemma Xmat_involutary : Involutary Xmat := by matrix_expand[Xmat]

lemma Xmat_mem_unitaryGroup :
  Xmat ∈ Matrix.unitaryGroup QubitBasis ℂ :=
by
  -- old lemma: gives (UUᴴ = 1 ∧ UᴴU = 1)
  have h := unitary_of_hermitian_involutary Xmat_hermitian Xmat_involutary
  -- we only need U * Uᴴ = 1
  have hU : Xmat * Xmatᴴ = 1 := h.1
  -- mathlib's membership lemma:
  --   A ∈ unitaryGroup ↔ A ⬝ Aᴴ = 1
  exact (Matrix.mem_unitaryGroup_iff.mpr hU)

noncomputable def X : OneQubitGate :=
{ val      := Xmat
, property := Xmat_mem_unitaryGroup }

/-- Pauli Y matrix, indexed by the qubit basis `Fin 2`. -/
def Ymat : Matrix QubitBasis QubitBasis ℂ :=
  !![0, -Complex.I; Complex.I, 0]

lemma Ymat_hermitian : Hermitian Ymat := by matrix_expand[Ymat]

lemma Ymat_involutary : Involutary Ymat := by matrix_expand[Ymat]

/-- `Ymat` is unitary in mathlib's sense. -/
lemma Ymat_mem_unitaryGroup :
  Ymat ∈ Matrix.unitaryGroup QubitBasis ℂ :=
by
  have h := unitary_of_hermitian_involutary
              Ymat_hermitian Ymat_involutary
  exact (Matrix.mem_unitaryGroup_iff.mpr h.1)

/-- Pauli Y as a one-qubit gate. -/
noncomputable def Y : OneQubitGate :=
{ val := Ymat
, property := Ymat_mem_unitaryGroup }

/-- Pauli Z matrix, indexed by the qubit basis `Fin 2`. -/
def Zmat : Matrix QubitBasis QubitBasis ℂ :=
  !![1, 0; 0, -1]

lemma Zmat_hermitian : Hermitian Zmat := by matrix_expand[Zmat]

lemma Zmat_involutary : Involutary Zmat := by matrix_expand[Zmat]

/-- `Zmat` is unitary in mathlib's sense. -/
lemma Zmat_mem_unitaryGroup :
  Zmat ∈ Matrix.unitaryGroup QubitBasis ℂ :=
by
  have h := unitary_of_hermitian_involutary
              Zmat_hermitian Zmat_involutary
  exact (Matrix.mem_unitaryGroup_iff.mpr h.1)

/-- Pauli Z as a one-qubit gate. -/
noncomputable def Z : OneQubitGate :=
{ val := Zmat
, property := Zmat_mem_unitaryGroup }

@[simp] lemma coe_X : (X : Matrix QubitBasis QubitBasis ℂ) = Xmat := rfl
@[simp] lemma coe_Y : (Y : Matrix QubitBasis QubitBasis ℂ) = Ymat := rfl
@[simp] lemma coe_Z : (Z : Matrix QubitBasis QubitBasis ℂ) = Zmat := rfl

lemma X_on_ket0 : applyGate X ket0 = ket1 := by
  vec_expand_simp [applyGate, X, Xmat, ket0, ket1, applyMatrixVec]

lemma X_on_ket1 : applyGate X ket1 = ket0 := by
  vec_expand_simp [applyGate, X, Xmat, ket0, ket1, applyMatrixVec]

-- Controlled version of a gate `g` on `k`, acting on `QubitBasis × k`.
noncomputable def controllize
  {k : Type*} [Fintype k] [DecidableEq k]
  (g : QuantumGate k) : QuantumGate (QubitBasis × k) :=
by
  classical
  refine ⟨
    -- underlying matrix
    Matrix.of (fun (q₁, t₁) (q₂, t₂) =>
      if (q₁, q₂) = (0, 0) then
        -- control = 0: act as identity on k
        (if t₁ = t₂ then (1 : ℂ) else 0)
      else if (q₁, q₂) = (1, 1) then
        -- control = 1: apply g on k
        (g : Matrix k k ℂ) t₁ t₂
      else
        -- off-diagonal blocks: zero
        0)
    ,
    -- proof this matrix is unitary (fill in later)
    by
      -- Goal: the above matrix is in Matrix.unitaryGroup (QubitBasis × k) ℂ
      -- This will use Matrix.mem_unitaryGroup_iff and the unitarity of g.
      -- We’ll come back and prove this carefully later.
      rw [Matrix.mem_unitaryGroup_iff]
      matrix_expand [-Complex.ext_iff] with ti tj;
      · congr 1
        exact propext eq_comm
      · exact congrFun₂ g.2.2 ti tj
  ⟩
scoped notation "C[" g "]" => controllize g

/-- CNOT gate on two qubits: control = first, target = second. -/
noncomputable def CNOT : TwoQubitGate :=
  C[X]
  -- i.e. controllize X, with k = QubitBasis

open Matrix

@[simp] lemma ket00_apply
  (q : QubitBasis) (t : QubitBasis) :
  (ket00 : QuantumState TwoQubitBasis).val (q, t)
    = (if (q, t) = (0, 0) then (1 : ℂ) else 0) :=
by
  -- whatever `rfl` / `simp` matches your actual definition of `ket00`
  -- e.g. if ket00 is a basis vector state at (0,0),
  -- this is likely just `rfl` after unfolding.
  simp [ket00, basisVec]

lemma CNOT_on_ket00 : applyGate CNOT ket00 = ket00 := by
  vec_expand_simp [applyGate, applyMatrixVec, Matrix.mulVec, dotProduct,
                   CNOT, controllize, ket00, basisVec]

lemma CNOT_on_ket01 : applyGate CNOT ket01 = ket01 := by
  vec_expand_simp[applyGate, applyMatrixVec, Matrix.mulVec, dotProduct,
              CNOT, controllize, ket01]

lemma CNOT_on_ket10 : applyGate CNOT ket10 = ket11 := by
  vec_expand_simp[applyGate, applyMatrixVec, Matrix.mulVec, dotProduct,
              CNOT, controllize, ket10, ket11, Xmat]

lemma CNOT_on_ket11 : applyGate CNOT ket11 = ket10 := by
  vec_expand_simp[applyGate, applyMatrixVec, Matrix.mulVec, dotProduct,
              CNOT, controllize, ket10, ket11, Xmat]

end Quantum
