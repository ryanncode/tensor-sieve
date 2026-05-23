import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Indefinite Metrics

This module establishes the formal foundations for Indefinite Metric Spaces,
where the fundamental inner product is no longer guaranteed to be positive definite.
This provides the algebraic bedrock for pseudo-Riemannian geometries (e.g., Minkowski space)
and generalized indefinite inner product spaces.
-/

namespace Mathlib.Analysis.InnerProductSpace.Krein

open LinearMap

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/--
Defines a non-degenerate, indefinite bilinear metric over a module `V`.
Unlike standard Hilbert space inner products, this metric permits negative
and zero evaluations for non-zero vectors.
-/
structure IndefiniteMetric (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  bilin : LinearMap.BilinForm R V
  symm : bilin.IsSymm
  non_degenerate : ∀ (x : V), (∀ (y : V), bilin x y = 0) → x = 0

/--
Maps the indefinite bilinear metric into its associated quadratic form.
This form is strictly used to evaluate whether a unit vector belongs to
the positive cone, negative cone, or neutral (isotropic) cone.
-/
def indefiniteQuadraticForm (M : IndefiniteMetric R V) : QuadraticForm R V :=
  LinearMap.BilinMap.toQuadraticMap M.bilin

end Mathlib.Analysis.InnerProductSpace.Krein
