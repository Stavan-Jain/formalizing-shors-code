import RepetitionCode.EncodeDecode
import Foundations.Basic
import Foundations.Gates
import Foundations.Tensor

namespace Quantum
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

end Quantum
