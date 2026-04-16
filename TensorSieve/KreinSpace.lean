import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# Phase 1: Algebraic Foundations and Indefinite Metrics
-/

namespace KinematicRiemann

open LinearMap

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

structure IndefiniteMetric (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  bilin : LinearMap.BilinForm R V
  symm : bilin.IsSymm

def indefiniteQuadraticForm (M : IndefiniteMetric R V) : QuadraticForm R V :=
  LinearMap.BilinMap.toQuadraticMap M.bilin

class KreinSpace (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  metric : IndefiniteMetric R V
  V_plus : Submodule R V
  V_minus : Submodule R V
  is_compl : IsCompl V_plus V_minus

/-!
# Phase 2: The Symmetry Operator and Majorant Topology
-/

/-- The symmetry operator J as an involutive linear equivalence. -/
class HasJOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [KreinSpace R V] where
  J : V ≃ₗ[R] V
  J_involutive : J.trans J = LinearEquiv.refl R V

/-- The type alias strategy to compartmentalize the topology. -/
def MajorantTopology (V : Type*) := V

instance {V} [AddCommGroup V] : AddCommGroup (MajorantTopology V) :=
  ‹AddCommGroup V›

instance {R V} [CommRing R] [AddCommGroup V] [Module R V] : Module R (MajorantTopology V) :=
  ‹Module R V›

/-- The majorant bilinear form ⟨x, y⟩_J = [Jx, y] -/
def majorantBilinForm {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] : LinearMap.BilinForm 𝕜 E :=
  (KreinSpace.metric (R := 𝕜) (V := E)).bilin.comp (HasJOperator.J (R := 𝕜) (V := E) : E →ₗ[𝕜] E) LinearMap.id

class MajorantPositiveDefinite (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] where
  re_inner_nonneg : ∀ x : E, 0 ≤ RCLike.re (majorantBilinForm (𝕜 := 𝕜) (E := E) x x)
  definite : ∀ x : E, majorantBilinForm (𝕜 := 𝕜) (E := E) x x = 0 → x = 0
  symm : (majorantBilinForm (𝕜 := 𝕜) (E := E)).IsSymm

noncomputable instance {𝕜 E} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] [MajorantPositiveDefinite 𝕜 E] :
    NormedAddCommGroup (MajorantTopology E) := sorry

noncomputable instance {𝕜 E} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] [MajorantPositiveDefinite 𝕜 E] :
    InnerProductSpace 𝕜 (MajorantTopology E) where
  inner x y := majorantBilinForm (𝕜 := 𝕜) (E := E) x y
  conj_inner_symm := sorry
  add_left := sorry
  smul_left := sorry
  norm_sq_eq_re_inner := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry
  norm_smul_le := sorry

-- To make it a Banach space, we assume completeness
class MajorantCompleteSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] [MajorantPositiveDefinite 𝕜 E] where
  complete : CompleteSpace (MajorantTopology E)

instance {𝕜 E} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] [MajorantPositiveDefinite 𝕜 E] [MajorantCompleteSpace 𝕜 E] :
    CompleteSpace (MajorantTopology E) :=
  MajorantCompleteSpace.complete (𝕜 := 𝕜) (E := E)

end KinematicRiemann
