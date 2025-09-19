import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul

open Matrix Complex

abbrev QuantumGate := Matrix (Fin 2) (Fin 2) ℂ
abbrev Qubit := Matrix (Fin 2) (Fin 1) ℂ
abbrev i := I

def QuantumWire : QuantumGate := !![1,0;0,1]
def X : QuantumGate := !![0,1;1,0]
def Z : QuantumGate := !![1,0;0,-1]
def Y : QuantumGate := !![0, -i; i, 0]

def Involutary (X : QuantumGate) : Prop := X * X = QuantumWire

def ket0 : Qubit := !![1 ; 0]
def ket1 : Qubit := !![0 ; 1]

def applyGate (U : QuantumGate) (ψ : Qubit) := U * ψ

@[simp] lemma X_def : X = !![0, 1; 1, 0] := rfl
@[simp] lemma Z_def : Z = !![1, 0; 0, -1] := rfl
@[simp] lemma Y_def : Y = !![0, -i; i, 0] := rfl
@[simp] lemma QuantumWire_def : QuantumWire = !![1, 0; 0, 1] := rfl
@[simp] lemma applyGate_def {U : QuantumGate} {ψ : Qubit} : applyGate U ψ  = U * ψ := rfl

lemma X_on_ket0 : applyGate X ket0 = ket1 := by
  ext i j
  simp [ket0, ket1]

lemma X_on_ket1 : applyGate X ket1 = ket0 := by
  ext i j
  simp [X, ket0, ket1]

lemma X_involutary : Involutary X := by
  ext i j
  simp

lemma Z_involutary : Involutary Z := by
  ext i j
  simp

lemma Y_involutary : Involutary Y := by
  ext i j
  simp

example : Matrix.map X id  = X := by
  ext i j
  apply map_apply

lemma XZ_neg_ZX : X * Z = - (Z * X) := by
  ext i j
  fin_cases i <;> fin_cases j
  <;> rw [Matrix.mul_apply]
  <;> simp
