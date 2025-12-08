import Foundations.Basic
import Foundations.Gates
import Foundations.Tensor

namespace Quantum

-- Logical codewords for the 3-bit repetition code (bit-flip code)
noncomputable abbrev zeroL : ThreeQubitState := ket000
noncomputable abbrev oneL : ThreeQubitState := ket111

@[simp] lemma zeroL_val :
  zeroL.val = basisVec (0, 0, 0) :=
  rfl

@[simp] lemma zeroL_coe :
  (zeroL : ThreeQubitVec) = basisVec (0, 0, 0) := rfl

@[simp] lemma oneL_coe :
  (oneL : ThreeQubitVec) = basisVec (1, 1, 1) := rfl

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

@[simp] lemma X_L_zeroL : X_L zeroL = oneL := rfl
@[simp] lemma X_L_oneL : X_L oneL  = zeroL := rfl

/-- Logical X on states: acts on basis labels via `X_L`, then interprets as a
    3-qubit state. At this level, this is just a specification function; later
    we will connect it to a concrete 3-qubit gate. -/
noncomputable def X_L_state (ℓ : LogicalQubit) : ThreeQubitState :=
  toState (X_L ℓ)

@[simp] lemma X_L_on_zeroL_state :
  X_L_state zeroL = Quantum.oneL := by
  simp [X_L_state]

@[simp] lemma X_L_on_oneL_state :
  X_L_state oneL = Quantum.zeroL := by
  simp [X_L_state]

/-- Every logical basis state lies in the repetition codespace. -/
@[simp] lemma toState_InRepetitionCode (ℓ : LogicalQubit) :
  InRepetitionCode (toState ℓ) := by
  cases ℓ <;> simp [toState]

/-- Logical X maps codewords to codewords (stays in the codespace). -/
@[simp] lemma X_L_state_InRepetitionCode (ℓ : LogicalQubit) :
  InRepetitionCode (X_L_state ℓ) := by
  cases ℓ <;> simp [X_L_state]

end LogicalQubit

-- It's better to construct these using tensor products but I will deal with that later
/- noncomputable def X_L_phys_mat :
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
-/
-- ## Semantic Encode
/-
I want to actually create a quantum circuit that does this
encoding. This is just semantics:
a mathematical map from a 1-qubit state to a 3-qubit codeword.-/

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
  admit

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
  admit

namespace LogicalQubit

noncomputable def toQubitState : LogicalQubit → QubitState
  | zeroL => ket0
  | oneL  => ket1

-- eg. |000> = 0L = encode (0)
@[simp] lemma encode_state_on_logical (ℓ : LogicalQubit) :
  encode_state (toQubitState ℓ) = toState ℓ := by
  cases ℓ <;> simp [toQubitState, toState, encode_state_ket0, encode_state_ket1]

end LogicalQubit

noncomputable def decodeVec (v : ThreeQubitVec) : QubitVec :=
  fun q =>
    match q with
    | 0 => v (0, 0, 0)
    | 1 => v (1, 1, 1)

/-- On the image of `encodeVec`, `decodeVec` is a left inverse. -/
lemma decodeVec_encodeVec (v : QubitVec) :
  decodeVec (encodeVec v) = v := by
  funext q
  -- `q : Fin 2`, so there are only two cases 0 and 1
  fin_cases q <;>
    simp [decodeVec, encodeVec]

/-- Semantic decoder from 3-qubit states back to 1-qubit states.

It simply reads off the amplitudes of |000⟩ and |111⟩ via `decodeVec`.
We postpone the norm proof for now (only the value field matters for
semantic correctness lemmas like `decode_state_encode_state`). -/
noncomputable def decode_state (ψ : ThreeQubitState) : QubitState :=
by
  classical
  refine ⟨decodeVec ψ.val, ?_⟩
  -- TODO: show `norm (decodeVec ψ.val) = 1` for the states we care about
  admit

@[simp] lemma decode_state_encode_state (ψ : QubitState) :
  decode_state (encode_state ψ) = ψ := by
  ext q
  simp [decode_state, encode_state, decodeVec_encodeVec]

/-- Aggregate amplitude for majority-0 basis states. -/
noncomputable def maj0_amp (v : ThreeQubitVec) : ℂ :=
  v (0, 0, 0) + v (0, 0, 1) + v (0, 1, 0) + v (1, 0, 0)

/-- Aggregate amplitude for majority-1 basis states. -/
noncomputable def maj1_amp (v : ThreeQubitVec) : ℂ :=
  v (1, 1, 1) + v (1, 1, 0) + v (1, 0, 1) + v (0, 1, 1)

/-- Semantic recovery on vectors: project onto the codespace by majority vote.

  `recoverVec v` is the vector
    (maj0_amp v) · |000⟩ + (maj1_amp v) · |111⟩. -/
noncomputable def recoverVec (v : ThreeQubitVec) : ThreeQubitVec :=
  fun ijk =>
    if ijk = (0, 0, 0) then
      maj0_amp v
    else if ijk = (1, 1, 1) then
      maj1_amp v
    else
      0

noncomputable def recover_state (ψ : ThreeQubitState) : ThreeQubitState :=
by
  classical
  refine ⟨recoverVec ψ.val, ?_⟩
  -- TODO: show this recovered state has norm 1 for the inputs
  -- we care about (encode_state ψ and encode_state ψ with single X errors).
  admit

@[simp] lemma recover_state_X_q1_3_encode_ket0 :
  recover_state (X_q1_3 • encode_state ket0) = encode_state ket0 := by
  classical
  -- First rewrite in terms of basis states
  have h1 : encode_state ket0 = ket000 := encode_state_ket0
  have h2 : X_q1_3 • ket000 = ket100 := X_q1_3_on_ket000
  -- Reduce the goal to a statement about `ket100` and `ket000`
  -- on the state level:
  --   recover_state ket100 = ket000
  suffices recover_state ket100 = ket000 by
    simpa [h1, h2]  -- applies h1,h2 and turns goal into this suffices
  -- Now prove `recover_state ket100 = ket000` by comparing underlying vectors.
  ext ijk
  -- Unfold `recover_state` and `recoverVec`
  simp [recover_state, recoverVec, ket100, ket000, basisVec_apply,
        maj0_amp, maj1_amp]

@[simp] lemma recover_state_X_q1_3_encode_ket1 :
  recover_state (X_q1_3 • encode_state ket1) = encode_state ket1 := by
  classical
  -- First rewrite in terms of basis states
  have h1 : encode_state ket1 = ket111 := encode_state_ket1
  have h2 : X_q1_3 • ket111 = ket011 := X_q1_3_on_ket111
  -- Reduce the goal to a statement about `ket011` and `ket111`
  -- on the state level:
  --   recover_state ket011 = ket111
  suffices recover_state ket011 = ket111 by
    simpa [h1, h2]
  -- Now prove `recover_state ket011 = ket111` by comparing underlying vectors.
  ext ijk
  simp [recover_state, recoverVec,
        maj0_amp, maj1_amp]
  grind

lemma recover_state_X_q1_3_encode_state (ψ : QubitState) :
  recover_state (X_q1_3 • encode_state ψ) = encode_state ψ := by
  -- This is the nontrivial part.
  -- Conceptually:
  --  - define the linear map F on underlying vectors:
  --        v ↦ recoverVec ((X_q1_3 : ThreeQubitGate).val.mulVec (encodeVec v))
  --  - show F(basisVec 0) = basisVec 0 and F(basisVec 1) = basisVec 1
  --    using `recover_state_X_q1_3_encode_ket0` and `recover_state_X_q1_3_encode_ket1`
  --  - conclude F = id_V, hence the underlying vectors match for general ψ.
  --
  -- For now, we leave this as a proof obligation to fill in later.
  admit

theorem repetition_corrects_single_X_q1 (ψ : QubitState) :
  decode_state (recover_state (X_q1_3 • encode_state ψ)) = ψ := by
  -- use the recovery lemma plus `decode_state_encode_state`
  have h := recover_state_X_q1_3_encode_state ψ
  -- rewrite with h, then apply decode∘encode = id
  simp [h]

end Quantum
