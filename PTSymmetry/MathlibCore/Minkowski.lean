import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import PTSymmetry.MathlibCore.IndefiniteMetric

/-!
# Minkowski Spacetime Validation

Isolating the fundamental metric requires a standalone algebraic target. Minkowski spacetime
($\mathbb{R}^{1,3}$) executes this exact function. It validates the core `IndefiniteMetric`
structure and `indefiniteQuadraticForm` boundary evaluations without utilizing topological
classes or operator formalisms.
-/

namespace PTSymmetry.MathlibCore.Krein.Examples

open LinearMap
open Mathlib.Analysis.InnerProductSpace.Krein

/--
The standard bilinear form for Minkowski spacetime with signature (-, +, +, +).
-/
def minkowskiBilin : LinearMap.BilinForm ℝ (Fin 4 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => -(x 0 * y 0) + (x 1 * y 1) + (x 2 * y 2) + (x 3 * y 3))
    (fun x y z => by simp; ring)
    (fun a x y => by simp; ring)
    (fun x y z => by simp; ring)
    (fun a x y => by simp; ring)

theorem minkowski_isSymm : LinearMap.BilinForm.IsSymm minkowskiBilin :=
  ⟨fun x y => by
    change -(x 0 * y 0) + (x 1 * y 1) + (x 2 * y 2) + (x 3 * y 3) =
      -(y 0 * x 0) + (y 1 * x 1) + (y 2 * x 2) + (y 3 * x 3)
    ring⟩

theorem minkowski_non_degenerate :
    ∀ (x : Fin 4 → ℝ), (∀ y, minkowskiBilin x y = 0) → x = 0 := by
  intro x hx
  -- We want to show the vector x is identically zero across all coordinates.
  ext i
  -- Evaluate the bilinear form against the standard basis vectors for each coordinate.
  have h0 := hx (fun j => if j = 0 then 1 else 0)
  have h1 := hx (fun j => if j = 1 then 1 else 0)
  have h2 := hx (fun j => if j = 2 then 1 else 0)
  have h3 := hx (fun j => if j = 3 then 1 else 0)
  -- Expand the definition of minkowskiBilin to expose the coordinate arithmetic.
  dsimp [minkowskiBilin] at h0 h1 h2 h3
  -- Case split on the index i (which can only be 0, 1, 2, or 3).
  fin_cases i
  -- For each case, the evaluation simplifies to an equation where x i = 0,
  -- which we solve using the linarith tactic.
  · change x 0 = 0; linarith [h0]
  · change x 1 = 0; linarith [h1]
  · change x 2 = 0; linarith [h2]
  · change x 3 = 0; linarith [h3]

/--
Minkowski spacetime as a strictly algebraic Indefinite Metric space.
-/
def minkowskiSpace : IndefiniteMetric ℝ (Fin 4 → ℝ) :=
  ⟨minkowskiBilin, minkowski_isSymm, minkowski_non_degenerate⟩

/--
The quadratic form mapping used to extract the positive and negative metric cones.
-/
def minkowskiQuadratic : QuadraticForm ℝ (Fin 4 → ℝ) :=
  indefiniteQuadraticForm minkowskiSpace

theorem exists_negative_norm : ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ minkowskiQuadratic v < 0 := by
  -- Provide an explicit vector (1, 0, 0, 0) representing the time-like direction.
  use fun i => if i = 0 then 1 else 0
  constructor
  -- Prove the vector is non-zero by evaluating it at index 0.
  · intro h
    have h0 := congr_fun h 0
    simp at h0
  -- Evaluate the quadratic form and show it simplifies to a negative value (-1 < 0).
  · change -(1 * 1) + (0 * 0) + (0 * 0) + (0 * 0) < (0 : ℝ)
    norm_num

theorem exists_zero_norm_nonzero : ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ minkowskiQuadratic v = 0 := by
  -- Provide an explicit null vector (1, 1, 0, 0) representing light-like propagation.
  use fun i => if i = 0 then 1 else if i = 1 then 1 else 0
  constructor
  -- Prove the vector is non-zero by evaluating it at index 0.
  · intro h
    have h0 := congr_fun h 0
    simp at h0
  -- Evaluate the quadratic form and show it simplifies to zero (-1 + 1 = 0).
  · change -(1 * 1) + (1 * 1) + (0 * 0) + (0 * 0) = (0 : ℝ)
    norm_num

end PTSymmetry.MathlibCore.Krein.Examples
