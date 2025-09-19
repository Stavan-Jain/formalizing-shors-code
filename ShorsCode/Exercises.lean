import Mathlib/Data/Complex/Basic
import Mathlib/LinearAlgebra/Matrix
import Mathlib/Data/Matrix/Notation

open Matrix Complex

abbrev I2 := Matrix (Fin 2) (Fin 2) ℂ
def I₂ : I2 := !![1, 0; 0, 1]
def X  : I2 := !![0, 1; 1, 0]
def Z  : I2 := !![1, 0; 0, -1]

lemma X_sq : X ⬝ X = I₂ := by
  ext i j <;> fin_cases i <;> fin_cases j
  <;> simp [X, I₂, Matrix.mul_apply]

lemma XZ_neg_ZX : X ⬝ Z = - (Z ⬝ X) := by
  ext i j <;> fin_cases i <;> fin_cases j
  <;> simp [X, Z, Matrix.mul_apply, sub_eq_add_neg, Complex.ofReal]
