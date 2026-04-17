import TensorSieve.KreinSpace
import TensorSieve.Kinematics
import TensorSieve.Operator
import TensorSieve.Distribution
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

namespace KinematicRiemann.TestSuite
open KinematicRiemann
open LinearMap
open Finset

-- 1. KreinSpace.lean Tests

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] [MajorantPositiveDefinite 𝕜 E]

#synth InnerProductSpace 𝕜 (MajorantTopology E)

omit [HasJOperator 𝕜 E] [MajorantPositiveDefinite 𝕜 E] in
lemma V_plus_inter_V_minus_eq_bot :
    (KreinSpace.V_plus (R := 𝕜) (V := E)) ⊓ (KreinSpace.V_minus (R := 𝕜) (V := E)) = ⊥ :=
  (KreinSpace.is_compl (R := 𝕜) (V := E)).inf_eq_bot

-- Explicit space for exists_negative_norm
def myBilin : LinearMap.BilinForm ℝ (ℝ × ℝ) where
  toFun := fun x => {
    toFun := fun y => x.1 * y.1 - x.2 * y.2
    map_add' := fun y1 y2 => by simp [mul_add, sub_add] ; ring
    map_smul' := fun c y => by simp ; ring
  }
  map_add' := fun x1 x2 => LinearMap.ext fun y => by simp [add_mul] ; ring
  map_smul' := fun c x => LinearMap.ext fun y => by simp ; ring

theorem exists_negative_norm : ∃ x : ℝ × ℝ, myBilin x x < 0 := by
  use (0, 1)
  change (0 : ℝ) * 0 - 1 * 1 < 0
  norm_num

variable [Invertible (2 : 𝕜)]
theorem P_plus_idempotent (x : MajorantTopology E) :
    P_plus (𝕜 := 𝕜) (E := E) (P_plus (𝕜 := 𝕜) (E := E) x) = P_plus (𝕜 := 𝕜) (E := E) x := by
  have h_J : (continuousJ (𝕜 := 𝕜) (E := E)) ((continuousJ (𝕜 := 𝕜) (E := E)) x) = x := by
    let y : E := x
    have h : HasJOperator.J (R := 𝕜) (V := E) (HasJOperator.J (R := 𝕜) (V := E) y) = y := J_J_eq_x y
    exact h
  dsimp [P_plus]
  simp only [map_smul, map_add, h_J]
  have h_comm : (continuousJ (𝕜 := 𝕜) (E := E)) x + x = x + (continuousJ (𝕜 := 𝕜) (E := E)) x :=
    add_comm _ _
  rw [h_comm, ← add_smul]
  have h_half : (⅟(2:𝕜) + ⅟(2:𝕜)) = 1 := by
    calc ⅟(2:𝕜) + ⅟(2:𝕜) = 2 * ⅟(2:𝕜) := by ring
    _ = 1 := mul_invOf_self 2
  rw [h_half, one_smul]

-- 2. Add IsJAdjoint test
instance : IsJAdjoint (HasJOperator.J (R := 𝕜) (V := E)).toLinearMap where
  j_adjoint x y := by
    -- bilin (J x) y = bilin x (J y)
    -- since J is an isometry of the Krein metric:
    -- bilin (J x) y = bilin (J (J x)) (J y)
    -- = bilin x (J y)
    -- We assume this property holds or use a lemma
    sorry

-- 2. Kinematics.lean Tests

-- Provide Decidable instance for isPrimeStep
instance (a b : SemanticAddress) : Decidable (isPrimeStep a b) :=
  if h : a.val ∣ b.val ∧ (b.val / a.val).Prime then
    isTrue <| by
      rcases h with ⟨h1, h2⟩
      use (b.val / a.val)
      exact ⟨h2, by rw [Nat.mul_div_cancel' h1]⟩
  else
    isFalse <| by
      intro ⟨p, hp1, hp2⟩
      apply h
      have h1 : a.val ∣ b.val := Dvd.intro p (Eq.symm hp2)
      refine ⟨h1, ?_⟩
      rw [hp2, Nat.mul_div_cancel_left p a.pos]
      exact hp1

#eval isPrimeStep ⟨4, by decide⟩ ⟨8, by decide⟩
#eval isPrimeStep ⟨4, by decide⟩ ⟨12, by decide⟩

lemma laplacian_row_sum_eq_zero (a : SemanticAddress) (S : Finset SemanticAddress)
    (h_self : a ∈ S)
    (h_deg : S.sum (fun b => if a.val == b.val then (0 : ℤ) else adjacency a b) =
      localDegree a) :
    S.sum (fun b => combinatorialLaplacian a b) = 0 := by
  have h_split : ∀ b, combinatorialLaplacian a b =
      (if a.val == b.val then (localDegree a : ℤ) else 0) +
      (if a.val == b.val then (0 : ℤ) else - adjacency a b) := by
    intro b
    dsimp [combinatorialLaplacian]
    split_ifs <;> ring
  calc S.sum (fun b => combinatorialLaplacian a b)
    _ = S.sum (fun b => (if a.val == b.val then (localDegree a : ℤ) else 0) +
        (if a.val == b.val then (0 : ℤ) else - adjacency a b)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact h_split b
    _ = S.sum (fun b => if a.val == b.val then (localDegree a : ℤ) else 0) +
        S.sum (fun b => if a.val == b.val then (0 : ℤ) else - adjacency a b) := by
      rw [Finset.sum_add_distrib]
    _ = (localDegree a : ℤ) - S.sum (fun b =>
        if a.val == b.val then (0 : ℤ) else adjacency a b) := by
      have h1 : S.sum (fun b => if a.val == b.val then (localDegree a : ℤ) else 0) =
          (localDegree a : ℤ) := by
        have h_single : S.sum (fun b => if a.val == b.val then (localDegree a : ℤ) else 0) =
            if a.val == a.val then (localDegree a : ℤ) else 0 := by
          apply Finset.sum_eq_single a
          · intro b _ hb_neq
            split_ifs with h_eq
            · exfalso
              apply hb_neq
              have h_val : b.val = a.val := (beq_iff_eq.mp h_eq).symm
              rcases a with ⟨av, ap⟩
              rcases b with ⟨bv, bp⟩
              simp only at h_val
              subst h_val
              rfl
            · rfl
          · intro h_not_in
            contradiction
        rw [h_single]
        simp
      have h2 : S.sum (fun b => if a.val == b.val then (0 : ℤ) else - adjacency a b) =
          - S.sum (fun b => if a.val == b.val then (0 : ℤ) else adjacency a b) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> ring
      rw [h1, h2]
      ring
    _ = 0 := by
      rw [h_deg, sub_self]

-- Note: kinematicSieve is noncomputable, so #eval cannot be used directly.
-- Requires work on universal boundary
theorem kinematicSieve_120 : kinematicSieve ⟨120, by decide⟩ = 0 := by sorry

-- 3. Operator.lean Tests
#eval pAdicValuation 360 2
#eval pAdicValuation 360 7
#eval addressToKreinUnit 4
#eval addressToKreinUnit 8
#eval traceHamiltonian [7]

-- 4. Distribution.lean Tests
theorem sliceToFunction_10_246_5 : sliceToFunction 10 [2, 4, 6] 5 = 0 := rfl

lemma connectedComponent_eq_singleton (x : ℤ) : connectedComponent x = {x} := by
  exact _root_.connectedComponent_eq_singleton x

noncomputable instance : AdelicMeasureSpace ℤ where
  volume := MeasureTheory.Measure.count
  is_add_haar_measure := {
    toIsAddLeftInvariant := inferInstance
    lt_top_of_isCompact := by
      intro K hK
      have h_fin : K.Finite := hK.finite_of_discrete
      exact (MeasureTheory.Measure.count_apply_lt_top.mpr h_fin)
    open_pos := by
      intro U _ hU_nonempty
      have ⟨x, hx⟩ := hU_nonempty
      have h_subset : {x} ⊆ U := Set.singleton_subset_iff.mpr hx
      have h_le : (1 : ENNReal) ≤ MeasureTheory.Measure.count U := by
        calc (1 : ENNReal) = MeasureTheory.Measure.count {x} := by
               rw [MeasureTheory.Measure.count_singleton]
             _ ≤ MeasureTheory.Measure.count U :=
               MeasureTheory.measure_mono (μ := MeasureTheory.Measure.count) h_subset
      intro h_zero
      rw [h_zero] at h_le
      revert h_le
      norm_num
  }

#synth AdelicMeasureSpace ℤ

end KinematicRiemann.TestSuite
