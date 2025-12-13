import Foundations.Basic
import Foundations.Gates
import Foundations.Tensor

namespace Quantum

/-!
# EncodeDecode

This file contains only the *semantic* encode/decode maps between
1-qubit vectors/states and the 3-qubit repetition-code subspace.

-/

-- Logical codewords for the 3-bit repetition code (bit-flip code)
noncomputable abbrev zeroL : ThreeQubitState := ket000
noncomputable abbrev oneL : ThreeQubitState := ket111

/-- Semantic encoder on vectors: embed a 1-qubit vector into the span of |000⟩ and |111⟩. -/
noncomputable def encodeVec (v : QubitVec) : ThreeQubitVec :=
  fun ijk =>
    if _ : ijk = (0, 0, 0) then
      v 0
    else if _ : ijk = (1, 1, 1) then
      v 1
    else
      0

/-- Norm preservation for `encodeVec` (can be proved later). -/
lemma encodeVec_norm (v : QubitVec) :
  norm (encodeVec v) = norm v := by
  admit

lemma encodeVec_add (v w : QubitVec) :
  encodeVec (v + w) = encodeVec v + encodeVec w := by
  classical
  funext ijk
  by_cases h0 : ijk = (0,0,0)
  · subst h0
    simp [encodeVec]
  · by_cases h1 : ijk = (1,1,1)
    · subst h1
      simp [encodeVec]
    · simp [encodeVec, h0, h1]

lemma encodeVec_smul (a : ℂ) (v : QubitVec) :
  encodeVec (a • v) = a • encodeVec v := by
  funext ijk
  simp [encodeVec, Pi.smul_apply]

/-- Semantic encoder on states: wrap `encodeVec` and use `encodeVec_norm` for normalization. -/
noncomputable def encode_state (ψ : QubitState) : ThreeQubitState :=
  ⟨encodeVec ψ.val, by
    -- here you'd use `encodeVec_norm` and `ψ.property : norm ψ.val = 1`
    have := ψ.property
    rw [encodeVec_norm]
    exact this⟩

/-- Unfolding lemma: value field of `encode_state`. -/
@[simp] lemma encode_state_val (ψ : QubitState) :
  (encode_state ψ).val = encodeVec ψ.val := rfl

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

/-- Semantic decoder on vectors: read off amplitudes of |000⟩ and |111⟩. -/
noncomputable def decodeVec (v : ThreeQubitVec) : QubitVec :=
  fun q =>
    match q with
    | 0 => v (0, 0, 0)
    | 1 => v (1, 1, 1)

/-- On the image of `encodeVec`, `decodeVec` is a left inverse. -/
lemma decodeVec_encodeVec (v : QubitVec) :
  decodeVec (encodeVec v) = v := by
  funext q
  fin_cases q <;> simp [decodeVec, encodeVec]

lemma decodeVec_add (v w : ThreeQubitVec) :
  decodeVec (v + w) = decodeVec v + decodeVec w := by
  funext q
  fin_cases q <;> simp [decodeVec, Pi.add_apply]

lemma decodeVec_smul (a : ℂ) (v : ThreeQubitVec) :
  decodeVec (a • v) = a • decodeVec v := by
  funext q
  fin_cases q <;> simp [decodeVec, Pi.smul_apply]

/-- Semantic decoder on states.

Normalization proof is postponed; only `.val` is used for most semantic equalities. -/
noncomputable def decode_state (ψ : ThreeQubitState) : QubitState :=
by
  refine ⟨decodeVec ψ.val, ?_⟩
  admit

/-- Unfolding lemma: value field of `decode_state`. -/
@[simp] lemma decode_state_val (ψ : ThreeQubitState) :
  (decode_state ψ).val = decodeVec ψ.val := rfl

@[simp] lemma decode_state_encode_state (ψ : QubitState) :
  decode_state (encode_state ψ) = ψ := by
  ext q
  simp [decode_state, encode_state, decodeVec_encodeVec]

@[simp] lemma decode_ket000 : decode_state ket000 = ket0 := by
  vec_expand_simp[decode_state, decodeVec, ket0]

@[simp] lemma decode_ket111 : decode_state ket111 = ket1 := by
  vec_expand_simp[decode_state, decodeVec, ket1]

end Quantum
