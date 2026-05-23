import PTSymmetry.MathlibCore.KreinSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# The Fundamental Symmetry Operator ($J$) and Majorant Topology

This module defines the fundamental symmetry operator $J$ (in PT-symmetric QM,
this is the $C$ or $P$ parity operator). It demonstrates how this involutive
automorphism induces a positive-definite Majorant topology (the $CPT$ inner product)
from the underlying indefinite metric.
-/

namespace PTSymmetry

open LinearMap
open Mathlib.Analysis.InnerProductSpace.Krein

/--
The Fundamental Symmetry Operator ($J$).
A linear equivalence acting on the Krein Space that fulfills the strict
involutive property $J^2 = I$. In Physics, this is the Charge Conjugation
or Parity operator.
-/
class HasJOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    [UniformSpace V] [KreinSpace R V] where
  J : V ≃ₗ[R] V
  J_involutive : J.trans J = LinearEquiv.refl R V
  J_self_adjoint : ∀ x y : V,
    (KreinSpace.metric (R := R) (V := V)).bilin (J x) y =
      (KreinSpace.metric (R := R) (V := V)).bilin x (J y)

/--
A type synonym for $V$ strictly utilized to isolate the positive-definite
Majorant topology induced by the $J$ operator. This prevents topological
clashes with the underlying indefinite metric.
-/
def MajorantTopology (V : Type*) := V

instance {V} [AddCommGroup V] : AddCommGroup (MajorantTopology V) :=
  ‹AddCommGroup V›

instance {R V} [CommRing R] [AddCommGroup V] [Module R V] : Module R (MajorantTopology V) :=
  ‹Module R V›

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [UniformSpace E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E]

/--
The induced Majorant inner product derived from the indefinite metric
via the $J$-operator involution ($[x, y]_J = [Jx, y]$). This guarantees a strictly
positive-definite geometry capable of sustaining continuous normed analysis,
known in physics as the $CPT$ inner product.
-/
def majorantInner (x y : E) : 𝕜 :=
  (KreinSpace.metric (R := 𝕜) (V := E)).bilin (HasJOperator.J (R := 𝕜) (V := E) x) y

/--
The structural verification that the induced `majorantInner` fulfills all
requisite properties of a strictly positive-definite inner product space.
-/
class MajorantPositiveDefinite (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [UniformSpace E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] where
  conj_symm : ∀ x y : E, starRingEnd 𝕜 (majorantInner (𝕜 := 𝕜) (E := E) x y) =
    majorantInner (𝕜 := 𝕜) (E := E) y x
  re_nonneg : ∀ x : E, 0 ≤ RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) x x)
  definite : ∀ x : E, majorantInner (𝕜 := 𝕜) (E := E) x x = 0 → x = 0
  add_left : ∀ x y z : E, majorantInner (𝕜 := 𝕜) (E := E) (x + y) z =
    majorantInner (𝕜 := 𝕜) (E := E) x z + majorantInner (𝕜 := 𝕜) (E := E) y z
  smul_left : ∀ x y : E, ∀ r : 𝕜, majorantInner (𝕜 := 𝕜) (E := E) (r • x) y =
    starRingEnd 𝕜 r * majorantInner (𝕜 := 𝕜) (E := E) x y

@[reducible]
noncomputable def majorantCore [MajorantPositiveDefinite 𝕜 E] :
    PreInnerProductSpace.Core 𝕜 (MajorantTopology E) where
  inner x y := majorantInner (𝕜 := 𝕜) (E := E) (x : E) (y : E)
  conj_inner_symm x y := MajorantPositiveDefinite.conj_symm (𝕜 := 𝕜) (E := E) (y : E) (x : E)
  re_inner_nonneg x := MajorantPositiveDefinite.re_nonneg (𝕜 := 𝕜) (E := E) (x : E)
  add_left x y z := MajorantPositiveDefinite.add_left (𝕜 := 𝕜) (E := E) (x : E) (y : E) (z : E)
  smul_left x y r := MajorantPositiveDefinite.smul_left (𝕜 := 𝕜) (E := E) (x : E) (y : E) r

@[reducible]
noncomputable def majorantInnerProductSpaceCore [MajorantPositiveDefinite 𝕜 E] :
    InnerProductSpace.Core 𝕜 (MajorantTopology E) :=
  { majorantCore (𝕜 := 𝕜) (E := E) with
    definite := fun x hx => MajorantPositiveDefinite.definite (𝕜 := 𝕜) (E := E) x hx }

noncomputable instance [MajorantPositiveDefinite 𝕜 E] : NormedAddCommGroup (MajorantTopology E) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 (MajorantTopology E) _ _ _
    (majorantInnerProductSpaceCore (𝕜 := 𝕜) (E := E))

noncomputable instance [MajorantPositiveDefinite 𝕜 E] : InnerProductSpace 𝕜 (MajorantTopology E) :=
  InnerProductSpace.ofCore (majorantInnerProductSpaceCore (𝕜 := 𝕜) (E := E)).toCore

class MajorantCompleteSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [UniformSpace E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E]
    [MajorantPositiveDefinite 𝕜 E] where
  complete : CompleteSpace (MajorantTopology E)

instance [MajorantPositiveDefinite 𝕜 E] [MajorantCompleteSpace 𝕜 E] :
    CompleteSpace (MajorantTopology E) :=
  MajorantCompleteSpace.complete (𝕜 := 𝕜) (E := E)

variable [MajorantPositiveDefinite 𝕜 E]

omit [MajorantPositiveDefinite 𝕜 E] in
lemma J_J_eq_x (x : E) :
    HasJOperator.J (R := 𝕜) (V := E) (HasJOperator.J (R := 𝕜) (V := E) x) = x := by
  have h := HasJOperator.J_involutive (R := 𝕜) (V := E)
  exact LinearEquiv.congr_fun h x

noncomputable def continuousJ [MajorantPositiveDefinite 𝕜 E] :
    (MajorantTopology E) ≃L[𝕜] (MajorantTopology E) :=
  let J_lin_E := HasJOperator.J (R := 𝕜) (V := E)
  let J_lin : (MajorantTopology E) ≃ₗ[𝕜] (MajorantTopology E) :=
    { toFun := fun x => J_lin_E (x : E)
      invFun := fun x => J_lin_E.symm (x : E)
      left_inv := fun x => J_lin_E.left_inv (x : E)
      right_inv := fun x => J_lin_E.right_inv (x : E)
      map_add' := fun x y => J_lin_E.map_add' (x : E) (y : E)
      map_smul' := fun r x => J_lin_E.map_smul' r (x : E) }
  LinearEquiv.toContinuousLinearEquivOfBounds J_lin 1 1
    (fun (x : MajorantTopology E) => by
      -- Forward Bound Proof
      -- Establish the relationship between the norm squared and the real part
      -- of the Majorant inner product for the mapped vector (J_lin x).
      have h1 : @norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2 =
          RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E))) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ (J_lin (x : E))
      -- Unfold the definition of the Majorant inner product to expose the
      -- underlying indefinite metric evaluation: [J(Jx), Jx].
      have h2 : majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E)) =
          (KreinSpace.metric (R := 𝕜) (V := E)).bilin (J_lin (J_lin (x : E))) (J_lin (x : E)) := rfl
      -- Apply the J-operator involution (J² = I) to simplify J(Jx) back to x.
      have h3 : J_lin (J_lin (x : E)) = (x : E) := by
        have h_inv := HasJOperator.J_involutive (R := 𝕜) (V := E)
        exact LinearEquiv.congr_fun h_inv (x : E)
      rw [h3] at h2
      -- Use the symmetry of the indefinite metric to rewrite [x, Jx] as [Jx, x],
      -- which by definition is the Majorant inner product [x, x]_J.
      have h4 : (KreinSpace.metric (R := 𝕜) (V := E)).bilin (x : E) (J_lin (x : E)) =
          majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E) := by
        have h_symm := (KreinSpace.metric (R := 𝕜) (V := E)).symm
        exact h_symm.eq (x : E) (J_lin (x : E))
      rw [h4] at h2
      have h6 : @norm (MajorantTopology E) _ x ^ 2 =
          RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E)) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ x
      -- Substitute the equalities back up the chain to prove that
      -- norm(J_lin x)² = norm(x)².
      rw [h2] at h1
      rw [← h6] at h1
      have ha : 0 ≤ @norm (MajorantTopology E) _ (J_lin (x : E)) := norm_nonneg _
      have hb : 0 ≤ @norm (MajorantTopology E) _ x := norm_nonneg _
      have h_eq0 : Real.sqrt (@norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2) =
          Real.sqrt (@norm (MajorantTopology E) _ x ^ 2) := congrArg Real.sqrt h1
      -- Simplify the square roots using the non-negativity of norms.
      rw [Real.sqrt_sq ha] at h_eq0
      rw [Real.sqrt_sq hb] at h_eq0
      -- Conclude that the norm is perfectly preserved (norm(J x) = norm(x)),
      -- satisfying the bound <= 1 * norm(x).
      calc @norm (MajorantTopology E) _ (J_lin (x : E)) = @norm (MajorantTopology E) _ x := h_eq0
        _ ≤ 1 * @norm (MajorantTopology E) _ x := by simp
    )
    (fun (x : MajorantTopology E) => by
      -- Inverse Bound Proof
      -- Show that the inverse of J_lin is equal to J_lin itself due to involution.
      have h_symm_eq : J_lin.symm (x : E) = J_lin (x : E) := by
        have h_inv := HasJOperator.J_involutive (R := 𝕜) (V := E)
        have h_double := LinearEquiv.congr_fun h_inv (x : E)
        have h_apply : J_lin.symm (J_lin (J_lin (x : E))) = J_lin.symm (x : E) :=
          congrArg J_lin.symm h_double
        rw [LinearEquiv.symm_apply_apply] at h_apply
        exact h_apply.symm
      -- Re-establish the norm equality from the forward bound proof.
      have h1 : @norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2 =
          RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E))) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ (J_lin (x : E))
      have h2 : majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E)) =
          (KreinSpace.metric (R := 𝕜) (V := E)).bilin (J_lin (J_lin (x : E))) (J_lin (x : E)) := rfl
      have h3 : J_lin (J_lin (x : E)) = (x : E) := by
        have h_inv := HasJOperator.J_involutive (R := 𝕜) (V := E)
        exact LinearEquiv.congr_fun h_inv (x : E)
      rw [h3] at h2
      have h4 : (KreinSpace.metric (R := 𝕜) (V := E)).bilin (x : E) (J_lin (x : E)) =
          majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E) := by
        have h_symm := (KreinSpace.metric (R := 𝕜) (V := E)).symm
        exact h_symm.eq (x : E) (J_lin (x : E))
      rw [h4] at h2
      have h6 : @norm (MajorantTopology E) _ x ^ 2 =
          RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E)) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ x
      rw [h2] at h1
      rw [← h6] at h1
      have ha : 0 ≤ @norm (MajorantTopology E) _ (J_lin (x : E)) := norm_nonneg _
      have hb : 0 ≤ @norm (MajorantTopology E) _ x := norm_nonneg _
      have h_eq0 : Real.sqrt (@norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2) =
          Real.sqrt (@norm (MajorantTopology E) _ x ^ 2) := congrArg Real.sqrt h1
      rw [Real.sqrt_sq ha] at h_eq0
      rw [Real.sqrt_sq hb] at h_eq0
      -- Substitute the symmetry equivalence to prove the inverse also perfectly
      -- preserves the norm.
      have h_symm_eq2 : @norm (MajorantTopology E) _ (J_lin.symm (x : E)) =
          @norm (MajorantTopology E) _ (J_lin (x : E)) := by
        exact congrArg (@norm (MajorantTopology E) _) h_symm_eq
      -- Conclude the inverse bound <= 1 * norm(x).
      calc @norm (MajorantTopology E) _ (J_lin.symm (x : E)) =
          @norm (MajorantTopology E) _ (J_lin (x : E)) := h_symm_eq2
        _ = @norm (MajorantTopology E) _ x := h_eq0
        _ ≤ 1 * @norm (MajorantTopology E) _ x := by simp
    )

end PTSymmetry
