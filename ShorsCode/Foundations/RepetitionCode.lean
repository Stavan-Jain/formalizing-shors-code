import Foundations.Basic
import Foundations.Gates

namespace Quantum

-- 3-qubit basis as a product of three 1-qubit bases.
abbrev ThreeQubitBasis := QubitBasis × QubitBasis × QubitBasis

abbrev ThreeQubitState := QuantumState ThreeQubitBasis

abbrev ThreeQubitVec := ThreeQubitBasis → ℂ

abbrev ThreeQubitGate : Type := QuantumGate ThreeQubitBasis

noncomputable def ket000 : ThreeQubitState :=
  ⟨basisVec (0, 0, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 0, 0)))⟩


noncomputable def ket111 : ThreeQubitState :=
  ⟨basisVec (1, 1, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 1, 1)))⟩

-- Logical codewords for the 3-bit repetition code (bit-flip code)
noncomputable def zeroL : ThreeQubitState := ket000
noncomputable def oneL : ThreeQubitState := ket111

@[simp] lemma zeroL_val :
  zeroL.val = basisVec (0, 0, 0) :=
  rfl

@[simp] lemma oneL_val :
  oneL.val = basisVec (1, 1, 1) :=
  rfl

noncomputable def repetitionCodeSpace : Submodule ℂ ThreeQubitVec :=
  Submodule.span ℂ { zeroL.val, oneL.val }

/-- A normalized 3-qubit state lies in the repetition codespace
    if its underlying vector lies in the linear span of |000⟩ and |111⟩. -/
def InRepetitionCode (ψ : ThreeQubitState) : Prop :=
  ψ.val ∈ repetitionCodeSpace

@[simp] lemma zeroL_in_code : InRepetitionCode zeroL:= by
  -- any generator is in the span
  exact Submodule.subset_span (by
    -- the set of generators is {zeroL.val, oneL.val}
    simp)

@[simp] lemma oneL_in_code : InRepetitionCode oneL := by
  exact Submodule.subset_span (by
    simp)

/-!
## Logical qubit and logical operators X_L, Z_L

We now define a tiny abstract "logical qubit" type whose basis elements
correspond to the codewords |0_L⟩ and |1_L⟩. Then we define logical X and Z
on this abstract logical qubit, and relate them back to the actual codewords.

The purpose of this section is to provide a specification for implementations
of Logical Qubit and Logical Operators
-/

/-- Abstract logical qubit basis: two logical basis states 0_L and 1_L. -/
inductive LogicalQubit
  | zeroL
  | oneL
deriving DecidableEq, Repr

namespace LogicalQubit

/-- Interpret a logical basis state as the corresponding 3-qubit codeword. -/
noncomputable def toState : LogicalQubit → ThreeQubitState
  | zeroL => Quantum.zeroL
  | oneL  => Quantum.oneL

@[simp] lemma toState_zeroL :
  toState zeroL = Quantum.zeroL := rfl

@[simp] lemma toState_oneL :
  toState oneL = Quantum.oneL := rfl

/-- Logical X operator on the logical basis:
    X_L |0_L⟩ = |1_L⟩,  X_L |1_L⟩ = |0_L⟩. -/
def X_L : LogicalQubit → LogicalQubit
  | zeroL => oneL
  | oneL  => zeroL

/-- Logical Z operator on the logical *basis*:
    on pure basis states, Z_L acts like the identity on the label.
    (The physically relevant phase on |1_L⟩ will show up when we work with
    superpositions α|0_L⟩ + β|1_L⟩, not at the level of this label type.) -/
def Z_L : LogicalQubit → LogicalQubit
  | zeroL => zeroL
  | oneL  => oneL

@[simp] lemma X_L_zeroL : X_L zeroL = oneL := rfl
@[simp] lemma X_L_oneL : X_L oneL  = zeroL := rfl

@[simp] lemma Z_L_zeroL : Z_L zeroL = zeroL := rfl
@[simp] lemma Z_L_oneL : Z_L oneL  = oneL  := rfl

/-- Logical X on states: acts on basis labels via `X_L`, then interprets as a
    3-qubit state. At this level, this is just a specification function; later
    we will connect it to a concrete 3-qubit gate. -/
noncomputable def X_L_state (ℓ : LogicalQubit) : ThreeQubitState :=
  toState (X_L ℓ)

/-- Logical Z on states: acts on basis labels via `Z_L`, then interprets as
    a 3-qubit state. Again, this is a semantic specification, not yet a
    concrete gate on all three qubits. -/
noncomputable def Z_L_state (ℓ : LogicalQubit) : ThreeQubitState :=
  toState (Z_L ℓ)

@[simp] lemma X_L_on_zeroL_state :
  X_L_state zeroL = Quantum.oneL := by
  simp [X_L_state]

@[simp] lemma X_L_on_oneL_state :
  X_L_state oneL = Quantum.zeroL := by
  simp [X_L_state]

@[simp] lemma Z_L_on_zeroL_state :
  Z_L_state zeroL = Quantum.zeroL := by
  simp [Z_L_state]

@[simp] lemma Z_L_on_oneL_state :
  Z_L_state oneL = Quantum.oneL := by
  simp [Z_L_state]

/-- Every logical basis state lies in the repetition codespace. -/
@[simp] lemma toState_InRepetitionCode (ℓ : LogicalQubit) :
  InRepetitionCode (toState ℓ) := by
  cases ℓ <;> simp [toState]

/-- Logical X maps codewords to codewords (stays in the codespace). -/
@[simp] lemma X_L_state_InRepetitionCode (ℓ : LogicalQubit) :
  InRepetitionCode (X_L_state ℓ) := by
  cases ℓ <;> simp [X_L_state]

/-- Logical Z maps codewords to codewords (stays in the codespace). -/
@[simp] lemma Z_L_state_InRepetitionCode (ℓ : LogicalQubit) :
  InRepetitionCode (Z_L_state ℓ) := by
  cases ℓ <;> simp [Z_L_state]

end LogicalQubit

-- It's probably better to construct these using tensor products
noncomputable def X_L_phys_mat :
  Matrix ThreeQubitBasis ThreeQubitBasis ℂ :=
  fun i j =>
    if j = (0, 0, 0) then
      -- column for |000⟩ is |111⟩
      if i = (1, 1, 1) then (1 : ℂ) else 0
    else if j = (1, 1, 1) then
      -- column for |111⟩ is |000⟩
      if i = (0, 0, 0) then (1 : ℂ) else 0
    else
      -- all other basis states are fixed
      if i = j then (1 : ℂ) else 0

@[simp] lemma X_L_phys_on_zeroL_val :
  applyMatrixVec X_L_phys_mat zeroL.val = oneL.val := by
  classical
  -- equality of functions ThreeQubitBasis → ℂ
  vec_expand_simp [applyMatrixVec, Matrix.mulVec,
                   X_L_phys_mat, zeroL_val, oneL_val, ket000, ket111,
                   basisVec]

@[simp] lemma X_L_phys_on_oneL_val :
  applyMatrixVec X_L_phys_mat oneL.val = zeroL.val := by
  classical
  vec_expand_simp [applyMatrixVec, Matrix.mulVec,
                   X_L_phys_mat, zeroL_val, oneL_val, ket000, ket111,
                   basisVec]


noncomputable def X_L_phys : ThreeQubitGate :=
by
  classical
  refine ⟨X_L_phys_mat, ?_⟩
  -- TODO: prove unitarity of X_L_phys_mat
  sorry

noncomputable def encodeVec (v : QubitVec) : ThreeQubitVec :=
  fun ijk =>
    if _ : ijk = (0, 0, 0) then
      v 0
    else if _ : ijk = (1, 1, 1) then
      v 1
    else
      0

lemma encodeVec_norm (v : QubitVec) :
  norm (encodeVec v) = norm v := by
  -- The sum over ThreeQubitBasis has only two nonzero terms (000 and 111),
  -- and those terms are exactly ‖v 0‖² and ‖v 1‖².
  -- So the norms are equal.
  -- proof outline:
  --   unfold norm
  --   simp [encodeVec, Finset.sum_filter, ...]  -- you'll need a case analysis on ijk
  sorry

-- ## Semantic Encode
/- a mathematical map from a 1-qubit state to a 3-qubit codeword.-/

noncomputable def encode_state (ψ : QubitState) : ThreeQubitState :=
  ⟨encodeVec ψ.val, by
    -- here you'd use `encodeVec_norm` and `ψ.property : norm ψ.val = 1`
    have := ψ.property
    rw [encodeVec_norm]
    exact this⟩

@[simp] lemma encode_state_ket0 :
  encode_state ket0 = zeroL := by
  ext b
  simp [encode_state, encodeVec, ket0, zeroL, ket000, basisVec]

@[simp] lemma encode_state_ket1 :
  encode_state ket1 = oneL := by
  ext b
  simp [encode_state, encodeVec, ket1, oneL, ket111, basisVec]
  intro h0
  rw [h0]
  simp only [Prod.mk.injEq, zero_ne_one, and_self, not_false_eq_true]

lemma encode_state_in_code (ψ : QubitState) :
  InRepetitionCode (encode_state ψ) := by
  -- show that encode_state ψ is in span{zeroL.val, oneL.val}
  -- encode_state ψ is literally (ψ.val 0) • zeroL.val + (ψ.val 1) • oneL.val
  -- so:
  have : encode_state ψ =
    (ψ.val 0) • zeroL.val + (ψ.val 1) • oneL.val := by
    -- prove equality of functions; use `encodeVec` unfolding
    simp [encode_state]
    sorry
  -- then use `this` and the definition of span
  sorry

namespace LogicalQubit

noncomputable def toQubitState : LogicalQubit → QubitState
  | zeroL => ket0
  | oneL  => ket1

-- eg. 0L = encode (0)
@[simp] lemma encode_state_on_logical (ℓ : LogicalQubit) :
  encode_state (toQubitState ℓ) = toState ℓ := by
  cases ℓ <;> simp [toQubitState, toState, encode_state_ket0, encode_state_ket1]

end LogicalQubit

end Quantum
