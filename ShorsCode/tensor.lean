import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import ShorsCode.Basic

lemma pow2_pos (r : ℕ) : 0 < 2 ^ r := Nat.pow_pos (by decide)

/-- given `k : Fin (2^(n+m))`,
return the pair `(i, j)` such that `k = i * 2^m + j`. -/
def splitIndex {n m : ℕ} (k : Fin (2 ^ (n + m))) :
    Fin (2^n) × Fin (2^m) :=
  (⟨ k.val / 2^m,
      -- proof: k.val / 2^m < 2^n because k.val < 2^(n+m) = (2^n)*(2^m)
      by
        have hk : k.val < 2^(n+m) := k.isLt
        have : k.val < (2^n) * (2^m) := by simpa [Nat.pow_add] using hk
        rw [mul_comm] at this
        exact Nat.div_lt_of_lt_mul this⟩,
   ⟨ k.val % 2^m,
      -- proof: remainder is always < divisor
      Nat.mod_lt k.val (pow2_pos m) ⟩)

def tensorVec {n m : ℕ}
  (v : Fin (2 ^ n) → ℂ) (w : Fin (2 ^ m) → ℂ) :
  Fin (2^(n+m)) → ℂ :=
  fun k =>
    let ij := splitIndex k
    v ij.1 * w ij.2

open scoped BigOperators

/-- Tensor product of two normalized quantum states. -/
def tensorState {n m : ℕ}
  (ψ : QState n) (φ : QState m) :
  QState (n + m) :=
{ state := tensorVec ψ.state φ.state,
  normalized := by
    classical
  -- start from the *definition* of vector norm
  -- (this line just unfolds `normsq` for a vector)
    change (∑ k, ‖(tensorVec ψ.state φ.state) k‖^2) = 1
    -- Compute ∑ |ψ⊗φ|² and show it equals 1
      -- rewrite each term using the definition of tensorVec
  -- and the fact ‖a*b‖ = ‖a‖ * ‖b‖ for complex numbers
    have step1 :
      (∑ k, ‖(tensorVec ψ.state φ.state) k‖^2)
        =
      ∑ k,
        (‖ψ.state (splitIndex k).1‖^2) *
        (‖φ.state (splitIndex k).2‖^2) := by
        classical
      apply Finset.sum_congr rfl
      intro k _
      -- use: (abs (a*b))^2 = (abs a)^2 * (abs b)^2
      have hnorm :
        ‖ψ.state (splitIndex k).1 * φ.state (splitIndex k).2‖
          = ‖ψ.state (splitIndex k).1‖
            * ‖φ.state (splitIndex k).2‖ := by
        simpa using Complex.abs.mul
          (ψ.state (splitIndex n m k).1)
          (φ.state (splitIndex n m k).2)
      -- square both sides; use pow_two and mul_pow
      simp [tensorVec, pow_two, mul_comm, mul_left_comm, mul_assoc]
    rw [step1]
    sorry
    }




/-- Combine `(i, j)` into a single index `k = i * 2^m + j`. -/
def combineIndex {n m : ℕ} (p : Fin (2 ^ n) × Fin (2 ^ m)) :
    Fin (2^(n+m)) :=
  ⟨ p.1.val * 2^m + p.2.val,
    by
      have hi : p.1.val < 2^n := p.1.isLt
      have hj : p.2.val < 2^m := p.2.isLt

      -- step 1: i*2^m + j < (i+1)*2^m
      have h_step1 :
        p.1.val * 2^m + p.2.val < (p.1.val + 1) * 2^m := by
        have := Nat.add_lt_add_left hj (p.1.val * 2^m)   -- i*2^m + j < i*2^m + 2^m
        -- rewrite the RHS i*2^m + 2^m = (i+1)*2^m
        simp [Nat.succ_mul, Nat.add_comm]
      -- step 2: (i+1)*2^m ≤ (2^n)*2^m
      have h_step2 :
        (p.1.val + 1) * 2^m ≤ (2^n) * 2^m := by
        have : p.1.val + 1 ≤ 2^n := Nat.succ_le_of_lt hi
        exact Nat.mul_le_mul_right _ this

      -- chain and rewrite 2^n * 2^m = 2^(n+m)
      have hlt : p.1.val * 2^m + p.2.val < (2^n) * 2^m :=
        lt_of_lt_of_le h_step1 h_step2
      simpa [Nat.pow_add, Nat.mul_comm] using hlt
  ⟩

lemma sanity_lemma {n m : ℕ} {i : Fin (2 ^ n)} {j : Fin (2 ^ m)} :
  splitIndex (combineIndex (i, j)) = (i, j) := by sorry
