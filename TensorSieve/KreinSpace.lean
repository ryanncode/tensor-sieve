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
# Phase 2 & 3: The Symmetry Operator and Endomorphisms
-/

class HasJOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [KreinSpace R V] where
  J : V ≃ₗ[R] V
  J_involutive : J.trans J = LinearEquiv.refl R V

def MajorantTopology (V : Type*) := V

instance {V} [AddCommGroup V] : AddCommGroup (MajorantTopology V) :=
  ‹AddCommGroup V›

instance {R V} [CommRing R] [AddCommGroup V] [Module R V] : Module R (MajorantTopology V) :=
  ‹Module R V›

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E]

def majorantInner (x y : E) : 𝕜 :=
  (KreinSpace.metric (R := 𝕜) (V := E)).bilin (HasJOperator.J (R := 𝕜) (V := E) x) y

class MajorantPositiveDefinite (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] where
  conj_symm : ∀ x y : E, starRingEnd 𝕜 (majorantInner (𝕜 := 𝕜) (E := E) x y) = majorantInner (𝕜 := 𝕜) (E := E) y x
  re_nonneg : ∀ x : E, 0 ≤ RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) x x)
  definite : ∀ x : E, majorantInner (𝕜 := 𝕜) (E := E) x x = 0 → x = 0
  add_left : ∀ x y z : E, majorantInner (𝕜 := 𝕜) (E := E) (x + y) z = majorantInner (𝕜 := 𝕜) (E := E) x z + majorantInner (𝕜 := 𝕜) (E := E) y z
  smul_left : ∀ x y : E, ∀ r : 𝕜, majorantInner (𝕜 := 𝕜) (E := E) (r • x) y = starRingEnd 𝕜 r * majorantInner (𝕜 := 𝕜) (E := E) x y

-- Create Core structure proving the requested InnerProductSpace axioms via exact proofs from the class assumptions
@[reducible]
noncomputable def majorantCore [MajorantPositiveDefinite 𝕜 E] : PreInnerProductSpace.Core 𝕜 (MajorantTopology E) where
  inner x y := majorantInner (𝕜 := 𝕜) (E := E) (x : E) (y : E)
  conj_inner_symm x y := MajorantPositiveDefinite.conj_symm (𝕜 := 𝕜) (E := E) (y : E) (x : E)
  re_inner_nonneg x := MajorantPositiveDefinite.re_nonneg (𝕜 := 𝕜) (E := E) (x : E)
  add_left x y z := MajorantPositiveDefinite.add_left (𝕜 := 𝕜) (E := E) (x : E) (y : E) (z : E)
  smul_left x y r := MajorantPositiveDefinite.smul_left (𝕜 := 𝕜) (E := E) (x : E) (y : E) r

noncomputable def majorantInnerProductSpaceCore [MajorantPositiveDefinite 𝕜 E] : InnerProductSpace.Core 𝕜 (MajorantTopology E) :=
  { majorantCore (𝕜 := 𝕜) (E := E) with
    definite := fun x hx => MajorantPositiveDefinite.definite (𝕜 := 𝕜) (E := E) x hx }

noncomputable instance [MajorantPositiveDefinite 𝕜 E] : NormedAddCommGroup (MajorantTopology E) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 (MajorantTopology E) _ _ _ (majorantInnerProductSpaceCore (𝕜 := 𝕜) (E := E))

noncomputable instance [MajorantPositiveDefinite 𝕜 E] : InnerProductSpace 𝕜 (MajorantTopology E) :=
  InnerProductSpace.ofCore (majorantInnerProductSpaceCore (𝕜 := 𝕜) (E := E)).toCore

class MajorantCompleteSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] [MajorantPositiveDefinite 𝕜 E] where
  complete : CompleteSpace (MajorantTopology E)

instance [MajorantPositiveDefinite 𝕜 E] [MajorantCompleteSpace 𝕜 E] : CompleteSpace (MajorantTopology E) :=
  MajorantCompleteSpace.complete (𝕜 := 𝕜) (E := E)

variable [MajorantPositiveDefinite 𝕜 E]

-- 3. Establish Continuous Equivalence

lemma J_J_eq_x (x : E) : HasJOperator.J (R := 𝕜) (V := E) (HasJOperator.J (R := 𝕜) (V := E) x) = x := by
  have h := HasJOperator.J_involutive (R := 𝕜) (V := E)
  exact LinearEquiv.congr_fun h x

noncomputable def continuousJ : (MajorantTopology E) ≃L[𝕜] (MajorantTopology E) :=
  let J_lin := HasJOperator.J (R := 𝕜) (V := E)
  LinearEquiv.toContinuousLinearEquivOfBounds J_lin 1 1
    (fun (x : MajorantTopology E) => by
      have h1 : @norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2 = RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E))) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ (J_lin (x : E))
      have h2 : majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E)) = (KreinSpace.metric (R := 𝕜) (V := E)).bilin (J_lin (J_lin (x : E))) (J_lin (x : E)) := rfl
      have h3 : J_lin (J_lin (x : E)) = (x : E) := by
        have h_inv := HasJOperator.J_involutive (R := 𝕜) (V := E)
        exact LinearEquiv.congr_fun h_inv (x : E)
      rw [h3] at h2
      have h4 : (KreinSpace.metric (R := 𝕜) (V := E)).bilin (x : E) (J_lin (x : E)) = majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E) := by
        have h_symm := (KreinSpace.metric (R := 𝕜) (V := E)).symm
        exact h_symm.eq (x : E) (J_lin (x : E))
      rw [h4] at h2
      have h6 : @norm (MajorantTopology E) _ x ^ 2 = RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E)) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ x
      rw [h2] at h1
      rw [← h6] at h1
      have ha : 0 ≤ @norm (MajorantTopology E) _ (J_lin (x : E)) := norm_nonneg _
      have hb : 0 ≤ @norm (MajorantTopology E) _ x := norm_nonneg _
      have h_eq0 : Real.sqrt (@norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2) = Real.sqrt (@norm (MajorantTopology E) _ x ^ 2) := congrArg Real.sqrt h1
      rw [Real.sqrt_sq ha] at h_eq0
      rw [Real.sqrt_sq hb] at h_eq0
      calc @norm (MajorantTopology E) _ (J_lin (x : E)) = @norm (MajorantTopology E) _ x := h_eq0
        _ ≤ 1 * @norm (MajorantTopology E) _ x := by simp
    )
    (fun (x : MajorantTopology E) => by
      have h_symm_eq : J_lin.symm (x : E) = J_lin (x : E) := by
        have h_inv := HasJOperator.J_involutive (R := 𝕜) (V := E)
        have h_double := LinearEquiv.congr_fun h_inv (x : E)
        have h_apply : J_lin.symm (J_lin (J_lin (x : E))) = J_lin.symm (x : E) := congrArg J_lin.symm h_double
        rw [LinearEquiv.symm_apply_apply] at h_apply
        exact h_apply.symm
      have h1 : @norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2 = RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E))) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ (J_lin (x : E))
      have h2 : majorantInner (𝕜 := 𝕜) (E := E) (J_lin (x : E)) (J_lin (x : E)) = (KreinSpace.metric (R := 𝕜) (V := E)).bilin (J_lin (J_lin (x : E))) (J_lin (x : E)) := rfl
      have h3 : J_lin (J_lin (x : E)) = (x : E) := by
        have h_inv := HasJOperator.J_involutive (R := 𝕜) (V := E)
        exact LinearEquiv.congr_fun h_inv (x : E)
      rw [h3] at h2
      have h4 : (KreinSpace.metric (R := 𝕜) (V := E)).bilin (x : E) (J_lin (x : E)) = majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E) := by
        have h_symm := (KreinSpace.metric (R := 𝕜) (V := E)).symm
        exact h_symm.eq (x : E) (J_lin (x : E))
      rw [h4] at h2
      have h6 : @norm (MajorantTopology E) _ x ^ 2 = RCLike.re (majorantInner (𝕜 := 𝕜) (E := E) (x : E) (x : E)) :=
        @InnerProductSpace.norm_sq_eq_re_inner 𝕜 (MajorantTopology E) _ _ _ x
      rw [h2] at h1
      rw [← h6] at h1
      have ha : 0 ≤ @norm (MajorantTopology E) _ (J_lin (x : E)) := norm_nonneg _
      have hb : 0 ≤ @norm (MajorantTopology E) _ x := norm_nonneg _
      have h_eq0 : Real.sqrt (@norm (MajorantTopology E) _ (J_lin (x : E)) ^ 2) = Real.sqrt (@norm (MajorantTopology E) _ x ^ 2) := congrArg Real.sqrt h1
      rw [Real.sqrt_sq ha] at h_eq0
      rw [Real.sqrt_sq hb] at h_eq0
      have h_symm_eq2 : @norm (MajorantTopology E) _ (J_lin.symm (x : E)) = @norm (MajorantTopology E) _ (J_lin (x : E)) := by
        exact congrArg (@norm (MajorantTopology E) _) h_symm_eq
      calc @norm (MajorantTopology E) _ (J_lin.symm (x : E)) = @norm (MajorantTopology E) _ (J_lin (x : E)) := h_symm_eq2
        _ = @norm (MajorantTopology E) _ x := h_eq0
        _ ≤ 1 * @norm (MajorantTopology E) _ x := by simp
    )

class IsJAdjoint (A : E →ₗ[𝕜] E) : Prop where
  j_adjoint : ∀ x y : E,
    (KreinSpace.metric (R := 𝕜) (V := E)).bilin (A x) y = (KreinSpace.metric (R := 𝕜) (V := E)).bilin x (A y)

def indefOrthogonal (K : Submodule 𝕜 E) : Submodule 𝕜 E where
  carrier := { v : E | ∀ u ∈ K, (KreinSpace.metric (R := 𝕜) (V := E)).bilin v u = 0 }
  add_mem' h1 h2 u hu := by
    rw [LinearMap.map_add₂]
    rw [h1 u hu, h2 u hu, zero_add]
  zero_mem' u _ := by
    rw [LinearMap.map_zero₂]
  smul_mem' c v hv u hu := by
    rw [LinearMap.map_smul₂, hv u hu, smul_zero]

variable [Invertible (2 : 𝕜)]

-- 2. Verify the Projection Operators
noncomputable def P_plus : (MajorantTopology E) →L[𝕜] (MajorantTopology E) :=
  (⅟(2 : 𝕜)) • (ContinuousLinearMap.id 𝕜 (MajorantTopology E) + continuousJ.toContinuousLinearMap)

noncomputable def P_minus : (MajorantTopology E) →L[𝕜] (MajorantTopology E) :=
  (⅟(2 : 𝕜)) • (ContinuousLinearMap.id 𝕜 (MajorantTopology E) - continuousJ.toContinuousLinearMap)

theorem P_plus_add_P_minus : P_plus (𝕜 := 𝕜) (E := E) + P_minus (𝕜 := 𝕜) (E := E) = ContinuousLinearMap.id 𝕜 (MajorantTopology E) := by
  dsimp [P_plus, P_minus]
  rw [smul_add, smul_sub]
  have h1 : (⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) : (MajorantTopology E) →L[𝕜] (MajorantTopology E)) +
            (⅟(2 : 𝕜) • continuousJ.toContinuousLinearMap : (MajorantTopology E) →L[𝕜] (MajorantTopology E)) +
            ((⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) : (MajorantTopology E) →L[𝕜] (MajorantTopology E)) -
            (⅟(2 : 𝕜) • continuousJ.toContinuousLinearMap : (MajorantTopology E) →L[𝕜] (MajorantTopology E))) =
            (⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) : (MajorantTopology E) →L[𝕜] (MajorantTopology E)) +
            (⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) : (MajorantTopology E) →L[𝕜] (MajorantTopology E)) := by
    abel
  rw [h1]
  rw [← add_smul]
  have h2 : ⅟(2 : 𝕜) + ⅟(2 : 𝕜) = 1 := by
    calc
      ⅟(2 : 𝕜) + ⅟(2 : 𝕜) = (1 : 𝕜) * ⅟(2 : 𝕜) + (1 : 𝕜) * ⅟(2 : 𝕜) := by simp
      _ = (1 + 1 : 𝕜) * ⅟(2 : 𝕜) := by rw [add_mul]
      _ = (2 : 𝕜) * ⅟(2 : 𝕜) := by norm_num
      _ = 1 := mul_invOf_self 2
  rw [h2, one_smul]

end KinematicRiemann
