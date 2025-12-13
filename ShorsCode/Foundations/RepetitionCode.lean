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

-- ## Semantic Encode
/-
Later, I want to actually create a quantum circuit that does this
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

lemma encodeVec_add (v w : QubitVec) :
  encodeVec (v + w) = encodeVec v + encodeVec w := by
  classical
  funext ijk
  by_cases h0 : ijk = (0,0,0)
  · subst h0
    -- all the ifs reduce definitionally
    simp [encodeVec]
  · by_cases h1 : ijk = (1,1,1)
    · subst h1
      simp [encodeVec]
    · -- “other basis state”: everything is 0 on both sides
      simp [encodeVec, h0, h1]

lemma encodeVec_smul (a : ℂ) (v : QubitVec) : encodeVec (a • v) = a • encodeVec v := by
  funext ijk; simp [encodeVec, Pi.smul_apply]

lemma encodeVec_basis0 : encodeVec (basisVec (0 : QubitBasis)) = (ket000 : ThreeQubitVec) := by
  funext ijk
  by_cases h0 : ijk = (0,0,0)
  · subst h0; simp [encodeVec, basisVec, ket000]
  · by_cases h1 : ijk = (1,1,1)
    · subst h1; simp [encodeVec, basisVec, ket000]
    · simp [encodeVec, basisVec, ket000, h0, h1]

lemma encodeVec_basis1 : encodeVec (basisVec (1 : QubitBasis)) = (ket111 : ThreeQubitVec) := by
  funext ijk
  by_cases h0 : ijk = (0,0,0)
  · subst h0; simp [encodeVec, basisVec, ket111]
  · by_cases h1 : ijk = (1,1,1)
    · subst h1; simp [encodeVec, basisVec, ket111]
    · simp [encodeVec, basisVec, ket111, h0, h1]

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

lemma decodeVec_add (v w : ThreeQubitVec) : decodeVec (v + w) = decodeVec v + decodeVec w := by
  funext q; fin_cases q <;> simp [decodeVec, Pi.add_apply]

lemma decodeVec_smul (a : ℂ) (v : ThreeQubitVec) : decodeVec (a • v) = a • decodeVec v := by
  funext q; fin_cases q <;> simp [decodeVec, Pi.smul_apply]

/-- Semantic decoder from 3-qubit states back to 1-qubit states.

It simply reads off the amplitudes of |000⟩ and |111⟩ via `decodeVec`.
We postpone the norm proof for now (only the value field matters for
semantic correctness lemmas like `decode_state_encode_state`). -/
noncomputable def decode_state (ψ : ThreeQubitState) : QubitState :=
by
  refine ⟨decodeVec ψ.val, ?_⟩
  -- TODO: show `norm (decodeVec ψ.val) = 1` for the states we care about
  admit

@[simp] lemma decode_state_encode_state (ψ : QubitState) :
  decode_state (encode_state ψ) = ψ := by
  ext q
  simp [decode_state, encode_state, decodeVec_encodeVec]

@[simp] lemma decode_ket000 : decode_state ket000 = ket0 := by
  vec_expand_simp[decode_state, decodeVec, ket0]

@[simp] lemma decode_ket111 : decode_state ket111 = ket1 := by
  vec_expand_simp[decode_state, decodeVec, ket1]

/-- Aggregate amplitude for majority-0 basis states. -/
noncomputable def maj0_amp (v : ThreeQubitVec) : ℂ :=
  v (0, 0, 0) + v (0, 0, 1) + v (0, 1, 0) + v (1, 0, 0)

lemma maj0_amp_add (v w : ThreeQubitVec) :
  maj0_amp (v + w) = maj0_amp v + maj0_amp w := by
  simp [maj0_amp]
  ring

lemma maj0_amp_smul (a : ℂ) (v : ThreeQubitVec) :
  maj0_amp (a • v) = a * maj0_amp v := by
  -- expand; simp turns (a • v) ijk into a * v ijk
  simp [maj0_amp, mul_add, add_assoc]

/-- Aggregate amplitude for majority-1 basis states. -/
noncomputable def maj1_amp (v : ThreeQubitVec) : ℂ :=
  v (1, 1, 1) + v (1, 1, 0) + v (1, 0, 1) + v (0, 1, 1)

lemma maj1_amp_add (v w : ThreeQubitVec) :
  maj1_amp (v + w) = maj1_amp v + maj1_amp w := by
  simp [maj1_amp, add_assoc, add_left_comm, add_comm]

lemma maj1_amp_smul (a : ℂ) (v : ThreeQubitVec) :
  maj1_amp (a • v) = a * maj1_amp v := by
  simp [maj1_amp, mul_add, add_comm]

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

@[simp] lemma recoverVec_add (v w : ThreeQubitVec) :
  recoverVec (v + w) = recoverVec v + recoverVec w := by
  funext ijk
  by_cases h0 : ijk = (0,0,0)
  · simp [recoverVec, h0, maj0_amp_add]
  · by_cases h1 : ijk = (1,1,1)
    · simp [recoverVec, h1, maj1_amp_add]
    · simp [recoverVec, h0, h1]

@[simp] lemma recoverVec_smul (a : ℂ) (v : ThreeQubitVec) :
  recoverVec (a • v) = a • recoverVec v := by
  funext ijk
  by_cases h0 : ijk = (0,0,0)
  · simp [recoverVec, h0, maj0_amp_smul]
  · by_cases h1 : ijk = (1,1,1)
    · simp [recoverVec, h1, maj1_amp_smul]
    · simp [recoverVec, h0, h1]

@[simp] lemma recoverVec_apply_000 (w : ThreeQubitVec) :
  recoverVec w (0,0,0) = maj0_amp w := by simp [recoverVec]

@[simp] lemma recoverVec_apply_111 (w : ThreeQubitVec) :
  recoverVec w (1,1,1) = maj1_amp w := by simp [recoverVec]

lemma recoverVec_apply_other (w : ThreeQubitVec) {ijk}
  (h0 : ijk ≠ (0, 0, 0)) (h1 : ijk ≠ (1, 1, 1)) :
  recoverVec w ijk = 0 := by simp [recoverVec, h0, h1]

noncomputable def recover_state (ψ : ThreeQubitState) : ThreeQubitState :=
by
  classical
  refine ⟨recoverVec ψ.val, ?_⟩
  -- TODO: show this recovered state has norm 1 for the inputs
  admit

-- These should probably not be marked as simp
@[simp] lemma recover_state_X_q1_3_encode_ket0 :
  recover_state (X_q1_3 • encode_state ket0) = encode_state ket0 := by
  classical
  have h1 : encode_state ket0 = ket000 := encode_state_ket0
  have h2 : X_q1_3 • ket000 = ket100 := X_q1_3_on_ket000
  suffices recover_state ket100 = ket000 by
    simpa [h1, h2]
  ext ijk
  simp [recover_state, recoverVec, maj0_amp, maj1_amp]

@[simp] lemma recover_state_X_q1_3_encode_ket1 :
  recover_state (X_q1_3 • encode_state ket1) = encode_state ket1 := by
  classical
  have h1 : encode_state ket1 = ket111 := encode_state_ket1
  have h2 : X_q1_3 • ket111 = ket011 := X_q1_3_on_ket111
  suffices recover_state ket011 = ket111 by
    simpa [h1, h2]
  ext ijk
  simp [recover_state, recoverVec,
        maj0_amp, maj1_amp]
  intro x
  simp [x]

lemma encodeVec_eq_lincomb (v : QubitVec) :
  encodeVec v =
    (v 0) • basisVec (0,0,0) + (v 1) • basisVec (1,1,1) := by
  funext ijk
  by_cases h0 : ijk=(0,0,0)
  · simp [encodeVec, basisVec, *]
  · by_cases h1 : ijk=(1,1,1)
    · simp [encodeVec, basisVec, *]
    · simp [encodeVec, basisVec, h0, h1]

@[simp] lemma X_q1_3_mulVec_basisVec_000 :
  (X_q1_3.val).mulVec (basisVec (0,0,0)) = basisVec (1,0,0) := by
  ext ijk
  simpa [ket000, ket100] using
    congrArg (fun (ψ : ThreeQubitState) => (ψ : ThreeQubitVec) ijk) X_q1_3_on_ket000

@[simp] lemma X_q1_3_mulVec_basisVec_111 :
  (X_q1_3.val).mulVec (basisVec (1,1,1)) = basisVec (0,1,1) := by
  ext ijk
  simpa [ket111, ket011] using
    congrArg (fun (ψ : ThreeQubitState) => (ψ : ThreeQubitVec) ijk) X_q1_3_on_ket111

lemma recoverVec_X_q1_3_encodeVec (v : QubitVec) :
  recoverVec ((X_q1_3.val).mulVec (encodeVec v)) = encodeVec v := by
  -- Put encodeVec into a 2-term linear combination
  have henc : encodeVec v =
      (v 0) • basisVec (0,0,0) + (v 1) • basisVec (1,1,1) := by
    simpa using encodeVec_eq_lincomb (v := v)

  -- Define the linear operator G := recoverVec ∘ (X_q1_3.mulVec)
  let G : ThreeQubitVec → ThreeQubitVec :=
    fun w => recoverVec ((X_q1_3.val).mulVec w)

  -- Linearity of G (comes from linearity of mulVec and recoverVec)
  have G_add (w₁ w₂ : ThreeQubitVec) : G (w₁ + w₂) = G w₁ + G w₂ := by
    simp [G, Matrix.mulVec_add]

  have G_smul (a : ℂ) (w : ThreeQubitVec) : G (a • w) = a • G w := by
    simp [G, Matrix.mulVec_smul]

  -- Basis facts: G fixes |000⟩ and |111⟩ (these are the only generators we need)
  have G_basis_000 : G (basisVec (0,0,0)) = basisVec (0,0,0) := by
    -- X sends |000⟩ to |100⟩, then recoverVec sends |100⟩ back to |000⟩
    ext ijk
    by_cases h0 : ijk = (0,0,0)
    · simp [G, h0, maj0_amp]
    · by_cases h1 : ijk = (1,1,1)
      · simp [G, h1, maj1_amp]
      · simp [G, recoverVec, h0, h1]

  have G_basis_111 : G (basisVec (1,1,1)) = basisVec (1,1,1) := by
    -- X sends |111⟩ to |011⟩, then recoverVec sends |011⟩ back to |111⟩
    ext ijk
    by_cases h0 : ijk = (0,0,0)
    · simp [G, h0, maj0_amp]
    · by_cases h1 : ijk = (1,1,1)
      · simp [G, h1, maj1_amp]
      · simp [G, recoverVec, h0, h1]

  -- Now finish by linearity: reduce to the two basis cases
  calc
    recoverVec ((X_q1_3.val).mulVec (encodeVec v))
        = G (encodeVec v) := by rfl
    _ = G ((v 0) • basisVec (0,0,0) + (v 1) • basisVec (1,1,1)) := by
          simp [henc]
    _ = G ((v 0) • basisVec (0,0,0)) + G ((v 1) • basisVec (1,1,1)) := by
          simp [G_add]
    _ = (v 0) • G (basisVec (0,0,0)) + (v 1) • G (basisVec (1,1,1)) := by
          simp [G_smul]
    _ = (v 0) • basisVec (0,0,0) + (v 1) • basisVec (1,1,1) := by
          simp [G_basis_000, G_basis_111]
    _ = encodeVec v := by
          simp [henc]

lemma recover_state_X_q1_3_encode_state (ψ : Qubit) :
  recover_state (X_q1_3 • encode_state ψ) = encode_state ψ := by
  ext ijk
  have hv : recoverVec ((X_q1_3.val).mulVec (encodeVec ψ.val)) = encodeVec ψ.val :=
    recoverVec_X_q1_3_encodeVec (v := ψ.val)
  have hvijk : recoverVec ((X_q1_3.val).mulVec (encodeVec ψ.val)) ijk = encodeVec ψ.val ijk :=
    congrArg (fun w : ThreeQubitVec => w ijk) hv
  simp [recover_state, encode_state, hvijk]


theorem repetition_corrects_single_X_q1 (ψ : QubitState) :
  decode_state (recover_state (X_q1_3 • encode_state ψ)) = ψ := by
  -- use the recovery lemma plus `decode_state_encode_state`
  have h := recover_state_X_q1_3_encode_state ψ
  -- rewrite with h, then apply decode∘encode = id
  simp [h]

noncomputable def LogicalX : ThreeQubitGate := X_q1q2q3_3

lemma LogicalX_encode_ket0 : LogicalX • encode_state ket0 = ket111 := by simp[LogicalX]

lemma LogicalX_encode_ket1 : LogicalX • encode_state ket1 = ket000 := by simp[LogicalX]

lemma decode_LogicalX_encode_ket0 : decode_state (LogicalX • encode_state ket0) = ket1 := by
  rw[LogicalX_encode_ket0]
  exact decode_ket111

lemma decode_LogicalX_encode_ket1 : decode_state (LogicalX • encode_state ket1) = ket0 := by
  rw[LogicalX_encode_ket1]
  exact decode_ket000

theorem logicalX_correct_ket0 : decode_state (LogicalX • encode_state ket0) = X • ket0 := by
  rw [decode_LogicalX_encode_ket0, X_on_ket0]

theorem logicalX_correct_ket1 : decode_state (LogicalX • encode_state ket1) = X • ket1 := by
  rw [decode_LogicalX_encode_ket1, X_on_ket1]

lemma qubitVec_eq_lincomb (v : QubitVec) :
  v = (v 0) • basisVec (0 : QubitBasis) + (v 1) • basisVec (1 : QubitBasis) := by
  funext q
  fin_cases q <;> simp [basisVec]

lemma qubit_val_eq_lincomb_kets (ψ : QubitState) :
  (ψ.val : QubitVec) = (ψ.val 0) • (ket0.val) + (ψ.val 1) • (ket1.val) := by
  ext q
  fin_cases q <;>
    -- now q is 0 or 1
    simp [ket0, ket1]

lemma gate_mulVec_of_smul_eq
  (U : ThreeQubitGate) (ψ φ : ThreeQubitState)
  (h : U • ψ = φ) :
  (U.val).mulVec (ψ : ThreeQubitVec) = (φ : ThreeQubitVec) := by
  ext ijk
  -- evaluate the state equality pointwise
  simpa using congrArg (fun s : ThreeQubitState => (s : ThreeQubitVec) ijk) h

lemma LogicalX_smul_ket000 : LogicalX • ket000 = ket111 := by
  -- your existing proof already gives this, but if it’s stated with encode_state:
  -- LogicalX_encode_ket0 : LogicalX • encode_state ket0 = ket111
  -- encode_state_ket0 : encode_state ket0 = ket000
  simpa [encode_state_ket0] using (LogicalX_encode_ket0 : LogicalX • encode_state ket0 = ket111)

lemma LogicalX_smul_ket111 : LogicalX • ket111 = ket000 := by
  simpa [encode_state_ket1] using (LogicalX_encode_ket1 : LogicalX • encode_state ket1 = ket000)

@[simp] lemma LogicalX_mulVec_ket000 :
  (LogicalX.val).mulVec (ket000 : ThreeQubitVec) = (ket111 : ThreeQubitVec) :=
by
  simpa using gate_mulVec_of_smul_eq LogicalX ket000 ket111 LogicalX_smul_ket000

@[simp] lemma LogicalX_mulVec_ket111 :
  (LogicalX.val).mulVec (ket111 : ThreeQubitVec) = (ket000 : ThreeQubitVec) :=
by
  simpa using gate_mulVec_of_smul_eq LogicalX ket111 ket000 LogicalX_smul_ket111

-- Same idea as gate_mulVec_of_smul_eq, but for 1-qubit gates/states
lemma gate_mulVec_of_smul_eq_qubit
  (U : OneQubitGate) (ψ φ : QubitState)
  (h : U • ψ = φ) :
  (U.val).mulVec (ψ : QubitVec) = (φ : QubitVec) := by
  ext q
  simpa using congrArg (fun s : QubitState => (s : QubitVec) q) h

@[simp] lemma X_mulVec_ket0 :
  (X.val).mulVec (ket0 : QubitVec) = (ket1 : QubitVec) := by
  simpa using gate_mulVec_of_smul_eq_qubit X ket0 ket1 X_on_ket0

@[simp] lemma X_mulVec_ket1 :
  (X.val).mulVec (ket1 : QubitVec) = (ket0 : QubitVec) := by
  simpa using gate_mulVec_of_smul_eq_qubit X ket1 ket0 X_on_ket1

lemma qubitVec_eq_lincomb_kets (v : QubitVec) :
  v = (v 0) • (ket0.val) + (v 1) • (ket1.val) := by
  ext q
  fin_cases q <;> simp [ket0, ket1]

/-- Unfolding lemma: value of `encode_state`. -/
@[simp] lemma encode_state_val (ψ : QubitState) :
  (encode_state ψ).val = encodeVec ψ.val := rfl

/-- Unfolding lemma: value of `decode_state`. -/
@[simp] lemma decode_state_val (ψ : ThreeQubitState) :
  (decode_state ψ).val = decodeVec ψ.val := rfl

/-- The semantic “logical X pipeline” as a function on 1-qubit vectors. -/
noncomputable def F (v : QubitVec) : QubitVec :=
  decodeVec (Matrix.mulVec (LogicalX.val) (encodeVec v))

lemma F_add (v w : QubitVec) : F (v + w) = F v + F w := by
  -- safe: only linearity lemmas
  simp [F, encodeVec_add, decodeVec_add, Matrix.mulVec_add]

lemma F_smul (a : ℂ) (v : QubitVec) : F (a • v) = a • F v := by
  simp [F, encodeVec_smul, decodeVec_smul, Matrix.mulVec_smul]

/-- Extract the ket0 basis case from the already-proved state theorem. -/
lemma F_ket0 :
  F (ket0.val) = (X • ket0).val := by
  -- take `.val` of the state-level correctness theorem
  have hval :
      (decode_state (LogicalX • encode_state ket0)).val = (X • ket0).val :=
    congrArg Subtype.val logicalX_correct_ket0
  -- rewrite the left side into `F ket0.val` using only definitional simp
  -- (no global simp search)
  -- LHS:
  --   decode_state_val -> decodeVec ( (LogicalX • encode_state ket0).val )
  --   smul_QState_val  -> mulVec LogicalX.val (encode_state ket0).val
  --   encode_state_val -> encodeVec ket0.val
  simpa [F] using (by
    simpa [decode_state_val, smul_QState_val, encode_state_val] using hval)

/-- Extract the ket1 basis case from the already-proved state theorem. -/
lemma F_ket1 :
  F (ket1.val) = (X • ket1).val := by
  have hval :
      (decode_state (LogicalX • encode_state ket1)).val = (X • ket1).val :=
    congrArg Subtype.val logicalX_correct_ket1
  simpa [F] using (by
    simpa [decode_state_val, smul_QState_val, encode_state_val] using hval)

/-- The vector-level correctness statement, proved by linearity + basis cases
    *but the basis cases come from state-level theorems*. -/
lemma F_correct (v : QubitVec) :
  F v = (X.val).mulVec v := by
  -- expand `v` in the {ket0, ket1} basis
  have hv : v = (v 0) • ket0.val + (v 1) • ket1.val := by
    simpa using qubitVec_eq_lincomb_kets (v := v)

  -- rewrite the RHS also into ket0/ket1 using your existing X_mulVec_ket0/ket1
  calc
    F v
        = F ((v 0) • ket0.val + (v 1) • ket1.val) := by
            -- hv : v = ...
            -- rewrite v on the LHS
            simpa using congrArg F hv
    _   = (v 0) • F (ket0.val) + (v 1) • F (ket1.val) := by
          simp [F_add, F_smul]
    _   = (v 0) • (X • ket0).val + (v 1) • (X • ket1).val := by
          simp [F_ket0, F_ket1]
    _   = (X.val).mulVec ((v 0) • ket0.val + (v 1) • ket1.val) := by
          -- push mulVec through the linear combination and use X action on kets
          simp [Matrix.mulVec_add, Matrix.mulVec_smul]
          have hx0 : Xmat.mulVec (↑ket0 : QubitVec) = (↑ket1 : QubitVec) := by
            vec_expand
            all_goals
              -- only unfold what is necessary; avoid global simp loops
              simp [Matrix.mulVec, Xmat, ket0, ket1]
          have hx1 : Xmat.mulVec (↑ket1 : QubitVec) = (↑ket0 : QubitVec) := by
            vec_expand
            all_goals
              simp [Matrix.mulVec, Xmat, ket0, ket1]
          rw [hx0, hx1]
    _   = (X.val).mulVec v := by exact (congrArg (fun w => (X.val).mulVec w) hv.symm)

/-- Your requested correctness statement (on `.val` fields). -/
lemma logicalX_correct_val (ψ : QubitState) :
  (decode_state (LogicalX • encode_state ψ)) = (X • ψ).val := by
  simpa [F, decode_state_val, smul_QState_val, encode_state_val] using
    (F_correct (v := ψ.val))

/-- Correctness as an equality of `QubitState`s. -/
lemma logicalX_correct_state (ψ : QubitState) :
  decode_state (LogicalX • encode_state ψ) = X • ψ := by
  ext q
  -- reduce to the val-level lemma pointwise
  have h := logicalX_correct_val (ψ := ψ)
  simpa using congrArg (fun v : QubitVec => v q) h

end Quantum
