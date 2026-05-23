import PTSymmetry.Physics.MajorantTopology
import PTSymmetry.MathlibCore.KreinBundle
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace PTSymmetry.Physics

open Bundle Set ContinuousLinearMap
open scoped Manifold Bundle
open Mathlib.Analysis.InnerProductSpace.Krein
open Mathlib.Geometry.Manifold

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-
Defines a smooth field of J-operators acting on the tangent bundle.
-/
class JOperatorField (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [KreinBundle I M] where
  fiber_J : ∀ x : M, HasJOperator 𝕜 (TangentSpace I x)

instance {x : M} [KreinBundle I M] [JOperatorField I M] : HasJOperator 𝕜 (TangentSpace I x) :=
  JOperatorField.fiber_J x

/-
Lifts the Majorant topology to induce a positive-definite inner product
bundle across the entire pseudo-Riemannian manifold.
-/
class MajorantBundle (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [KreinBundle I M] [JOperatorField I M] where
  fiber_majorant : ∀ x : M, MajorantPositiveDefinite 𝕜 (TangentSpace I x)

end PTSymmetry.Physics
