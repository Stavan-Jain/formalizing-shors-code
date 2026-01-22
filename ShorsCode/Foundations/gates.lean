import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Foundations.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

namespace Quantum
open Matrix

abbrev QuantumGate (α : Type*) [DecidableEq α] [Fintype α] :=
  Matrix.unitaryGroup α ℂ

abbrev OneQubitGate : Type :=
  QuantumGate QubitBasis   -- i.e. Matrix.unitaryGroup (Fin 2) ℂ

abbrev TwoQubitGate : Type := QuantumGate TwoQubitBasis

-- 3-qubit basis as a product of three 1-qubit bases.

abbrev ThreeQubitGate : Type := QuantumGate ThreeQubitBasis

@[simp] lemma gate_inv_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  (G⁻¹ : QuantumGate α).val = star G.val := by
  rfl

-- Inverse-related lemmas (API stubs, proofs later)
@[simp] lemma gate_val_inv
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  (G.val)⁻¹ = star G.val := by
  have h_unit := Matrix.UnitaryGroup.det_isUnit G
  have h_star_mul := Matrix.mem_unitaryGroup_iff.1 G.2
  calc (G.val)⁻¹
      = (G.val)⁻¹ * 1 := by rw [mul_one]
    _ = (G.val)⁻¹ * (G.val * star G.val) := by rw [← h_star_mul]
    _ = ((G.val)⁻¹ * G.val) * star G.val := by rw [Matrix.mul_assoc]
    _ = 1 * star G.val := by rw [nonsing_inv_mul _ h_unit]
    _ = star G.val := by rw [one_mul]

@[simp] lemma gate_val_mul_inv
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  G.val * (G⁻¹ : QuantumGate α).val = (1 : Matrix α α ℂ) := by
  rw [gate_inv_val]
  exact Matrix.mem_unitaryGroup_iff.1 G.2

@[simp] lemma gate_val_inv_mul
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  (G⁻¹ : QuantumGate α).val * G.val = (1 : Matrix α α ℂ) := by
  rw [gate_inv_val]
  exact Matrix.mem_unitaryGroup_iff'.1 G.2

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

Proves goals equating `QuantumState`s by calling `vec_expand` and
then solving each goal with `simp[rules]`
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

@[simp] lemma applyGate_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (applyGate G ψ).val = Matrix.mulVec (G.val) ψ.val := rfl

@[simp] lemma applyGate_coe
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (applyGate G ψ : Vector α) = Matrix.mulVec (G.val) ψ := rfl

noncomputable instance smul_Vector_by_QuantumGate
  {α : Type*} [Fintype α] [DecidableEq α] :
  SMul (QuantumGate α) (Vector α) :=
{ smul := fun U v => Matrix.mulVec (U.val) v }

noncomputable instance smul_QuantumState_by_QuantumGate
  {α : Type*} [Fintype α] [DecidableEq α] :
  SMul (QuantumGate α) (QuantumState α) :=
{ smul := applyGate }

@[simp] lemma smul_val
  {α} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (G • ψ : Vector α) = Matrix.mulVec (G.val) ψ := rfl

@[simp] lemma smul_QState_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (G • ψ).val = Matrix.mulVec (G.val) ψ.val := rfl

def Hermitian {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) : Prop :=
  Mᴴ = M

@[simp] lemma Hermitian_def {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) :
  Hermitian M ↔ Mᴴ = M := Iff.rfl

def Involutary {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) : Prop :=
  M * M = 1

@[simp] lemma Involutary_def {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) :
  Involutary M ↔ M * M = 1 := Iff.rfl

-- Inverse-related lemmas (API stubs, proofs later)
lemma involutary_inv_eq
  {α : Type*} [Fintype α] [DecidableEq α]
  {M : Matrix α α ℂ} (h : Involutary M) :
  M⁻¹ = M := by
  have h_mul : M * M = 1 := h
  have h_unit : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.isUnit_of_right_inverse h_mul)
  calc M⁻¹
      = M⁻¹ * 1 := by rw [mul_one]
    _ = M⁻¹ * (M * M) := by rw [← h_mul]
    _ = (M⁻¹ * M) * M := by rw [Matrix.mul_assoc]
    _ = 1 * M := by rw [nonsing_inv_mul _ h_unit]
    _ = M := by rw [one_mul]

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

/-- Identity matrix on the qubit basis. -/
def Imat : Matrix QubitBasis QubitBasis ℂ := 1

lemma Imat_hermitian : Hermitian Imat := by
  rw [Hermitian_def, Imat, conjTranspose_one]

lemma Imat_involutary : Involutary Imat := by
  rw [Involutary_def, Imat, mul_one]

@[simp] lemma Imat_sq : Imat * Imat = 1 := Imat_involutary

lemma Imat_mem_unitaryGroup :
  Imat ∈ Matrix.unitaryGroup QubitBasis ℂ := by
  have h := unitary_of_hermitian_involutary Imat_hermitian Imat_involutary
  exact Matrix.mem_unitaryGroup_iff.mpr h.1

/-- Identity as a one-qubit gate. -/
noncomputable def I : OneQubitGate :=
  ⟨Imat, Imat_mem_unitaryGroup⟩

/- Pauli X matrix -/
def Xmat : Matrix QubitBasis QubitBasis ℂ := !![0, 1; 1, 0]

lemma Xmat_hermitian : Hermitian Xmat := by matrix_expand[Xmat]

lemma Xmat_involutary : Involutary Xmat := by matrix_expand[Xmat]

@[simp] lemma Xmat_sq : Xmat * Xmat = 1 := Xmat_involutary

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

@[simp] lemma Ymat_sq : Ymat * Ymat = 1 := Ymat_involutary

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

@[simp] lemma Zmat_sq : Zmat * Zmat = 1 := Zmat_involutary

/-- Pauli matrix cross products: X * Y = iZ -/
lemma Xmat_mul_Ymat : Xmat * Ymat = Complex.I • Zmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Y * X = -iZ -/
lemma Ymat_mul_Xmat : Ymat * Xmat = -Complex.I • Zmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Y * Z = iX -/
lemma Ymat_mul_Zmat : Ymat * Zmat = Complex.I • Xmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Z * Y = -iX -/
lemma Zmat_mul_Ymat : Zmat * Ymat = -Complex.I • Xmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Z * X = iY -/
lemma Zmat_mul_Xmat : Zmat * Xmat = Complex.I • Ymat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: X * Z = -iY -/
lemma Xmat_mul_Zmat : Xmat * Zmat = -Complex.I • Ymat := by matrix_expand[Xmat, Ymat, Zmat]

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

@[simp] lemma coe_I : (I : Matrix QubitBasis QubitBasis ℂ) = Imat := rfl
@[simp] lemma coe_X : (X : Matrix QubitBasis QubitBasis ℂ) = Xmat := rfl
@[simp] lemma coe_Y : (Y : Matrix QubitBasis QubitBasis ℂ) = Ymat := rfl
@[simp] lemma coe_Z : (Z : Matrix QubitBasis QubitBasis ℂ) = Zmat := rfl

@[simp] lemma inv_I : I⁻¹ = I := by
  ext
  rw [gate_inv_val, coe_I, star_eq_conjTranspose, (Hermitian_def Imat).1 Imat_hermitian]

@[simp] lemma inv_X : X⁻¹ = X := by
  ext
  rw [gate_inv_val, coe_X, star_eq_conjTranspose, (Hermitian_def Xmat).1 Xmat_hermitian]

@[simp] lemma inv_Y : Y⁻¹ = Y := by
  ext
  rw [gate_inv_val, coe_Y, star_eq_conjTranspose, (Hermitian_def Ymat).1 Ymat_hermitian]

@[simp] lemma inv_Z : Z⁻¹ = Z := by
  ext
  rw [gate_inv_val, coe_Z, star_eq_conjTranspose, (Hermitian_def Zmat).1 Zmat_hermitian]

@[simp] lemma X_on_ket0 : X • ket0 = ket1 := by
  vec_expand_simp [Xmat, ket0, ket1]

@[simp] lemma X_on_ket1 : X • ket1 = ket0 := by
  vec_expand_simp [Xmat, ket0, ket1]

-- Controlled version of a gate `g` on `k`, acting on `QubitBasis × k`.
noncomputable def controllize
  {k : Type*} [Fintype k] [DecidableEq k]
  (g : QuantumGate k) : QuantumGate (QubitBasis × k) :=
by
  classical
  exact ⟨
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
    by
      rw [Matrix.mem_unitaryGroup_iff]
      matrix_expand [-Complex.ext_iff] with ti tj;
      · congr 1
        exact propext eq_comm
      · exact congrFun₂ g.2.2 ti tj
  ⟩
scoped notation "C[" g "]" => controllize g

@[simp] lemma controllize_val
  {k : Type*} [Fintype k] [DecidableEq k]
  (g : QuantumGate k) :
  (controllize g : Matrix (QubitBasis × k) (QubitBasis × k) ℂ) =
    Matrix.of (fun (q₁, t₁) (q₂, t₂) =>
      if (q₁, q₂) = (0, 0) then
        (if t₁ = t₂ then (1 : ℂ) else 0)
      else if (q₁, q₂) = (1, 1) then
        (g : Matrix k k ℂ) t₁ t₂
      else
        0) :=
rfl

/-- CNOT gate on two qubits: control = first, target = second. -/
noncomputable def CNOT : TwoQubitGate :=
  C[X]
  -- i.e. controllize X, with k = QubitBasis

@[simp] lemma ket00_apply
  (q : QubitBasis) (t : QubitBasis) :
  (ket00 : QuantumState TwoQubitBasis).val (q, t)
    = (if (q, t) = (0, 0) then (1 : ℂ) else 0) :=
by
  simp [ket00]

lemma CNOT_on_ket00 : CNOT • ket00 = ket00 := by
  vec_expand_simp [Matrix.mulVec, CNOT, ket00]

lemma CNOT_on_ket01 : CNOT • ket01 = ket01 := by
  vec_expand_simp[Matrix.mulVec, CNOT, ket01]

lemma CNOT_on_ket10 : CNOT • ket10 = ket11 := by
  vec_expand_simp[Matrix.mulVec, CNOT, ket10, ket11, Xmat]

lemma CNOT_on_ket11 : CNOT • ket11 = ket10 := by
  vec_expand_simp[Matrix.mulVec, CNOT, ket10, ket11, Xmat]

end Quantum
