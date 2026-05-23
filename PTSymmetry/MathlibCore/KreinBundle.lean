import PTSymmetry.MathlibCore.KreinSpace
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace Mathlib.Geometry.Manifold

open Bundle Set ContinuousLinearMap
open scoped Manifold Bundle
open Mathlib.Analysis.InnerProductSpace.Krein

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

-- TangentSpace I x is definitionally E, so we can lift its UniformSpace
instance {x : M} : UniformSpace (TangentSpace I x) := show UniformSpace E by infer_instance

/-
Assigns a Krein space structure to the tangent space at every point x on the manifold.
-/
class KreinBundle (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  fiber_krein : ∀ x : M, KreinSpace 𝕜 (TangentSpace I x)

instance {x : M} [KreinBundle I M] : KreinSpace 𝕜 (TangentSpace I x) :=
  KreinBundle.fiber_krein x

end Mathlib.Geometry.Manifold
