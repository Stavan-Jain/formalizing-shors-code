import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import ShorsCode.Foundations.Foundations
import ShorsCode.Stabilizer.PauliGroupSingle
import ShorsCode.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

namespace NQubitPauliGroupElement

/-!
# Matrix/Gate Representation
-/

@[simp] lemma toMatrix_one (n : ℕ) :
  ((1 : NQubitPauliGroupElement n).toMatrix) = (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
  simp only [toMatrix, one_def, PauliGroupElement.phasePowerToComplex_0, one_smul,
    NQubitPauliOperator.identity_toMatrix]

/-- The identity n-qubit Pauli group element maps to the identity gate. -/
@[simp] lemma toGate_one (n : ℕ) :
  toGate (1 : NQubitPauliGroupElement n) = (1 : QuantumGate (NQubitBasis n)) := by
  apply Subtype.ext
  rw [toGate_val, toMatrix_one]
  rfl

/-- Group multiplication corresponds to matrix multiplication. -/
lemma toMatrix_mul (p q : NQubitPauliGroupElement n) :
  (p * q).toMatrix = p.toMatrix * q.toMatrix := by
    unfold Quantum.NQubitPauliGroupElement.toMatrix;
    ext b₁ b₂;
    have h_expand : (p.operators.toMatrix * q.operators.toMatrix) b₁ b₂ =
    ∑ k : Fin n → QubitBasis, (∏ i, (p.operators i).toMatrix (b₁ i) (k i)) *
    (∏ i, (q.operators i).toMatrix (k i) (b₂ i)) := by
      rfl;
    have h_expand_further : ∑ k : Fin n → QubitBasis,
    (∏ i, (p.operators i).toMatrix (b₁ i) (k i)) *
    (∏ i, (q.operators i).toMatrix (k i) (b₂ i)) =
    ∏ i, (∑ k : QubitBasis, (p.operators i).toMatrix (b₁ i) k *
    (q.operators i).toMatrix k (b₂ i)) := by
      simp only [← Finset.prod_mul_distrib];
      exact
        Eq.symm
          (Fintype.prod_sum fun i j ↦
            (p.operators i).toMatrix (b₁ i) j * (q.operators i).toMatrix j (b₂ i));
    have h_expand_single_qubit :
        ∀ i : Fin n,
          (∑ k : QubitBasis,
              (p.operators i).toMatrix (b₁ i) k * (q.operators i).toMatrix k (b₂ i)) =
            Quantum.PauliGroupElement.phasePowerToComplex
                (Quantum.PauliOperator.mulOp (p.operators i) (q.operators i)).phasePower *
              (Quantum.PauliOperator.mulOp (p.operators i) (q.operators i)).operator.toMatrix
                (b₁ i) (b₂ i) := by
      intro i
      have h_single_qubit :
          ∀ (P Q : Quantum.PauliOperator),
            (P.toMatrix * Q.toMatrix) =
              Quantum.PauliGroupElement.phasePowerToComplex
                  (Quantum.PauliOperator.mulOp P Q).phasePower •
                (Quantum.PauliOperator.mulOp P Q).operator.toMatrix := by
        exact fun P Q ↦ PauliGroupElement.PauliOperator.toMatrix_mul P Q
      convert
        congr_arg (fun m => m (b₁ i) (b₂ i)) (h_single_qubit (p.operators i) (q.operators i))
          using 1
    simp_all +decide [Finset.prod_mul_distrib, Matrix.mul_apply]
    have h_phasePowerToComplex :
        Quantum.PauliGroupElement.phasePowerToComplex (p.mul q).phasePower =
          Quantum.PauliGroupElement.phasePowerToComplex p.phasePower *
            Quantum.PauliGroupElement.phasePowerToComplex q.phasePower *
            (∏ i,
              Quantum.PauliGroupElement.phasePowerToComplex
                ((p.operators i).mulOp (q.operators i)).phasePower) := by
      have h_phasePowerToComplex :
          ∀ (a b c : Fin 4),
            Quantum.PauliGroupElement.phasePowerToComplex (a + b + c) =
              Quantum.PauliGroupElement.phasePowerToComplex a *
                Quantum.PauliGroupElement.phasePowerToComplex b *
                Quantum.PauliGroupElement.phasePowerToComplex c := by
        exact fun a b c ↦ Eq.symm (PauliGroupElement.phasePowerToComplex_add3 a b c)
      convert
        h_phasePowerToComplex p.phasePower q.phasePower
            (∑ i : Fin n,
              ((p.operators i).mulOp (q.operators i) |> Quantum.PauliGroupElement.phasePower))
          using 1
      have h_phasePowerToComplex :
          ∀ (s : Finset (Fin n)),
            (∏ i ∈ s,
                Quantum.PauliGroupElement.phasePowerToComplex
                  ((p.operators i).mulOp (q.operators i)).phasePower) =
              Quantum.PauliGroupElement.phasePowerToComplex
                (∑ i ∈ s, ((p.operators i).mulOp (q.operators i)).phasePower) := by
        intro s
        induction s using Finset.induction <;>
          simp_all +decide [Finset.sum_insert, Finset.prod_insert]
        (expose_names;
          exact
            PauliGroupElement.phasePowerToComplex_add
              ((p.operators a).mulOp (q.operators a)).phasePower
              (∑ i ∈ s, ((p.operators i).mulOp (q.operators i)).phasePower))
      rw [h_phasePowerToComplex]
    simp_all +decide [ mul_comm, mul_left_comm ];
    convert
      congr_arg
          (fun x : ℂ =>
            x *
              (Quantum.PauliGroupElement.phasePowerToComplex p.phasePower *
                Quantum.PauliGroupElement.phasePowerToComplex q.phasePower))
          h_expand.symm using 1 <;>
      ring_nf
    · simp +decide [  mul_comm, mul_left_comm, NQubitPauliOperator.toMatrix ];
      simp +decide [ NQubitPauliGroupElement.mul ];
      simp +decide [  NQubitPauliGroupElement.mulOp ];
      ring;
    · simp +decide only [mul_comm, Finset.mul_sum _ _ _];
      ac_rfl

/-- Group inverse corresponds to matrix inverse. -/
lemma toMatrix_inv (p : NQubitPauliGroupElement n) :
  (p⁻¹).toMatrix = (p.toMatrix)⁻¹ := by
  have h_unitary :
      ∀ (p : NQubitPauliGroupElement n), p.toMatrix⁻¹ = p⁻¹.toMatrix := by
    intro p
    rw [Matrix.inv_eq_right_inv]
    have h_unitary :
        ∀ (p : NQubitPauliGroupElement n),
          p.toMatrix * p⁻¹.toMatrix = (p * p⁻¹).toMatrix := by
      exact fun p ↦ Eq.symm (toMatrix_mul p p⁻¹)
    rw [h_unitary, mul_inv_cancel, toMatrix_one]
  exact h_unitary p ▸ rfl

/-- `toGate` is a group homomorphism. -/
lemma toGate_mul (p q : NQubitPauliGroupElement n) : toGate (p * q) = toGate p * toGate q := by
  apply Subtype.ext
  rw [toGate_val, gate_mul_val, toGate_val, toGate_val]
  exact toMatrix_mul p q

/-- `toGate` preserves inverse. -/
lemma toGate_inv (p : NQubitPauliGroupElement n) : toGate (p⁻¹) = (toGate p)⁻¹ := by
  apply Subtype.ext
  rw [toGate_val, toMatrix_inv p, gate_inv_val (toGate p), ← gate_val_inv (toGate p), ← toGate_val]

end NQubitPauliGroupElement

end Quantum
