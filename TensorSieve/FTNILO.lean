import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# Discrete Integer Matrix Contractions and Indicator Gates (`FTNILO`)

This module defines elementary integer-valued matrix contractions and binary
indicator gates (`diracDeltaGate`, `leftToRightContraction`, `halfPartialTrace`),
operating independently of the `p`-adic divisor quiver in `Operator.lean`.

It proves:
1. `delta_consistency`: `diracDeltaGate x y ∈ {0, 1}`.
2. `diracDeltaGate_comm`: `diracDeltaGate x y = diracDeltaGate y x`.
3. `leftToRightContraction_eq_mul`: `leftToRightContraction A B = A * B`.
4. `halfPartialTrace_eq_sum`: `halfPartialTrace A j = ∑ i, A i j`.
-/

namespace KinematicRiemann

/-- Finite integer matrix used for discrete contraction sums. -/
abbrev BinaryMatrix (n m : ℕ) := Matrix (Fin n) (Fin m) ℤ

/-- Kronecker/Dirac indicator gate on `ℤ`: returns `1` when `x = y` and `0` otherwise. -/
def diracDeltaGate (x y : ℤ) : ℤ :=
  if x == y then 1 else 0

/-- `diracDeltaGate` takes values strictly in `{0, 1}`. -/
lemma delta_consistency (x y : ℤ) : diracDeltaGate x y = 1 ∨ diracDeltaGate x y = 0 := by
  dsimp [diracDeltaGate]
  split
  · left; rfl
  · right; rfl

/-- `diracDeltaGate` is symmetric in its arguments. -/
lemma diracDeltaGate_comm (x y : ℤ) : diracDeltaGate x y = diracDeltaGate y x := by
  dsimp [diracDeltaGate]
  by_cases h : x = y
  · subst h; simp
  · have h1 : (x == y) = false := beq_false_of_ne h
    have h2 : (y == x) = false := beq_false_of_ne (Ne.symm h)
    simp [h1, h2]

private lemma foldl_add_int_eq_sum (l : List ℤ) (init : ℤ) :
    l.foldl (· + ·) init = init + l.sum := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih (init + hd)]
    ring

/-- Left-to-right sum-of-products matrix contraction over a shared finite index. -/
def leftToRightContraction {n m k : ℕ} (A : BinaryMatrix n m) (B : BinaryMatrix m k) :
    BinaryMatrix n k :=
  fun i j =>
    let sum := (List.finRange m).map (fun l => A i l * B l j)
    sum.foldl (· + ·) 0

/-- `leftToRightContraction` agrees identically with standard matrix multiplication `A * B`. -/
theorem leftToRightContraction_eq_mul {n m k : ℕ}
    (A : BinaryMatrix n m) (B : BinaryMatrix m k) :
    leftToRightContraction A B = A * B := by
  ext i j
  simp only [leftToRightContraction, Matrix.mul_apply, foldl_add_int_eq_sum, zero_add,
    Fin.sum_univ_def]

/-- Constant all-ones vector on `Fin n`. -/
def plusVector (n : ℕ) : Fin n → ℤ :=
  fun _ => 1

/-- Column summation via contraction against `plusVector`. -/
def halfPartialTrace {n m : ℕ} (A : BinaryMatrix n m) : Fin m → ℤ :=
  fun j =>
    let sum := (List.finRange n).map (fun i => A i j * plusVector n i)
    sum.foldl (· + ·) 0

/-- `halfPartialTrace A j` equals the exact column sum `∑ i, A i j`. -/
theorem halfPartialTrace_eq_sum {n m : ℕ} (A : BinaryMatrix n m) (j : Fin m) :
    halfPartialTrace A j = ∑ i : Fin n, A i j := by
  simp only [halfPartialTrace, plusVector, mul_one, foldl_add_int_eq_sum, zero_add,
    Fin.sum_univ_def]

end KinematicRiemann
