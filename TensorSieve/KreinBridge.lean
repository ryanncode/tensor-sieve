import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Instances.Real.Lemmas
import PTSymmetry.MathlibCore.IndefiniteMetric
import PTSymmetry.MathlibCore.KreinSpace
import PTSymmetry.Physics.MajorantTopology
import PTSymmetry.Physics.JAdjointHamiltonian
import TensorSieve.Operator

/-!
# Finite-Dimensional Krein Bridge (`PTSymmetry` ↔ `TensorSieve.Operator`)

This module instantiates the standalone `PTSymmetry` Krein space hierarchy
(`IndefiniteMetric`, `KreinSpace`, `HasJOperator`, `MajorantPositiveDefinite`,
and `IsJAdjoint`) on the concrete finite-dimensional arithmetic slice space
`SliceVec slice := Fin slice.length → ℝ` equipped with the parity involution
`paritySignR` from `TensorSieve.Operator`.

It proves without custom axioms or `sorry`:
1. `SliceVec slice` forms a complete `KreinSpace ℝ` with fundamental symmetry `J`.
2. The induced Majorant inner product `[J x, y]` is strictly positive definite
   (coinciding with the Euclidean inner product on `Fin slice.length → ℝ`).
3. The real part `sliceRealKreinOp slice = J_ℝ * H_ℝ` of `sliceKreinOperator`
   satisfies `PTSymmetry.IsJAdjoint`.
-/

namespace KinematicRiemann

open Matrix
open Mathlib.Analysis.InnerProductSpace.Krein
open PTSymmetry

/-- Real parity sign `±1` associated with a node `a : ℕ`, matching `paritySign`. -/
def paritySignR (a : ℕ) : ℝ :=
  ((KreinBilin (addressToKreinUnit a) (1, 1) : ℤ) : ℝ)

theorem paritySignR_eq_one_or_neg_one (a : ℕ) :
    paritySignR a = 1 ∨ paritySignR a = -1 := by
  unfold paritySignR KreinBilin
  rcases addressToKreinUnit_cases a with h | h <;> rw [h] <;> simp

theorem paritySignR_mul_self (a : ℕ) : paritySignR a * paritySignR a = 1 := by
  rcases paritySignR_eq_one_or_neg_one a with h | h <;> rw [h] <;> ring

theorem paritySign_re (a : ℕ) : (paritySign a).re = paritySignR a := by
  unfold paritySign paritySignR
  simp

theorem paritySign_im (a : ℕ) : (paritySign a).im = 0 := by
  unfold paritySign
  simp

/-- Finite-dimensional real state space on a horizontal divisibility slice. -/
def SliceVec (slice : List ℕ) : Type := Fin slice.length → ℝ

instance (slice : List ℕ) : AddCommGroup (SliceVec slice) :=
  inferInstanceAs (AddCommGroup (Fin slice.length → ℝ))

instance (slice : List ℕ) : Module ℝ (SliceVec slice) :=
  inferInstanceAs (Module ℝ (Fin slice.length → ℝ))

instance (slice : List ℕ) : UniformSpace (SliceVec slice) :=
  inferInstanceAs (UniformSpace (Fin slice.length → ℝ))

instance (slice : List ℕ) : CompleteSpace (SliceVec slice) :=
  inferInstanceAs (CompleteSpace (Fin slice.length → ℝ))

/-- Parity sign at index `i` of a horizontal slice. -/
def sliceParityR (slice : List ℕ) (i : Fin slice.length) : ℝ :=
  paritySignR (slice.get ⟨i.val, i.isLt⟩)

theorem sliceParityR_eq_one_or_neg_one (slice : List ℕ) (i : Fin slice.length) :
    sliceParityR slice i = 1 ∨ sliceParityR slice i = -1 :=
  paritySignR_eq_one_or_neg_one _

theorem sliceParityR_mul_self (slice : List ℕ) (i : Fin slice.length) :
    sliceParityR slice i * sliceParityR slice i = 1 :=
  paritySignR_mul_self _

/-- Indefinite Krein bilinear form `[x, y]_J = ∑ i, s_i x_i y_i` on `SliceVec slice`. -/
def sliceBilin (slice : List ℕ) : LinearMap.BilinForm ℝ (SliceVec slice) :=
  LinearMap.mk₂ ℝ
    (fun x y => ∑ i : Fin slice.length, sliceParityR slice i * x i * y i)
    (fun x y z => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      change sliceParityR slice i * (x i + y i) * z i =
        sliceParityR slice i * x i * z i + sliceParityR slice i * y i * z i
      ring)
    (fun a x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change sliceParityR slice i * (a * x i) * y i = a * (sliceParityR slice i * x i * y i)
      ring)
    (fun x y z => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      change sliceParityR slice i * x i * (y i + z i) =
        sliceParityR slice i * x i * y i + sliceParityR slice i * x i * z i
      ring)
    (fun a x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change sliceParityR slice i * x i * (a * y i) = a * (sliceParityR slice i * x i * y i)
      ring)

theorem sliceBilin_apply (slice : List ℕ) (x y : SliceVec slice) :
    sliceBilin slice x y = ∑ i : Fin slice.length, sliceParityR slice i * x i * y i := rfl

theorem sliceBilin_isSymm (slice : List ℕ) : (sliceBilin slice).IsSymm :=
  ⟨fun x y => by
    simp only [sliceBilin_apply]
    refine Finset.sum_congr rfl fun i _ => by ring⟩

theorem sliceBilin_non_degenerate (slice : List ℕ) :
    ∀ x : SliceVec slice, (∀ y : SliceVec slice, sliceBilin slice x y = 0) → x = 0 := by
  intro x hx
  funext i
  let ei : SliceVec slice := fun j => if j = i then sliceParityR slice i else 0
  have h := hx ei
  rw [sliceBilin_apply] at h
  have hsum :
      (∑ j : Fin slice.length, sliceParityR slice j * x j * ei j) =
        sliceParityR slice i * x i * sliceParityR slice i := by
    rw [Finset.sum_eq_single i]
    · simp [ei]
    · intro j _ hji
      simp [ei, hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum] at h
  have hsq : sliceParityR slice i * x i * sliceParityR slice i = x i := by
    calc sliceParityR slice i * x i * sliceParityR slice i
        = (sliceParityR slice i * sliceParityR slice i) * x i := by ring
      _ = 1 * x i := by rw [sliceParityR_mul_self]
      _ = x i := one_mul _
  rw [hsq] at h
  exact h

/-- Concrete `PTSymmetry` `IndefiniteMetric` on a horizontal divisibility slice. -/
def sliceIndefiniteMetric (slice : List ℕ) :
    Mathlib.Analysis.InnerProductSpace.Krein.IndefiniteMetric ℝ (SliceVec slice) where
  bilin := sliceBilin slice
  symm := sliceBilin_isSymm slice
  non_degenerate := sliceBilin_non_degenerate slice

/-- Positive-parity subspace `V⁺` supported on indices with `paritySignR = +1`. -/
def sliceVPlus (slice : List ℕ) : Submodule ℝ (SliceVec slice) where
  carrier := { x | ∀ i, sliceParityR slice i = -1 → x i = 0 }
  add_mem' {x y} hx hy i hi := by
    change x i + y i = 0
    rw [hx i hi, hy i hi, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c {x} hx i hi := by
    change c * x i = 0
    rw [hx i hi, mul_zero]

/-- Negative-parity subspace `V⁻` supported on indices with `paritySignR = -1`. -/
def sliceVMinus (slice : List ℕ) : Submodule ℝ (SliceVec slice) where
  carrier := { x | ∀ i, sliceParityR slice i = 1 → x i = 0 }
  add_mem' {x y} hx hy i hi := by
    change x i + y i = 0
    rw [hx i hi, hy i hi, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c {x} hx i hi := by
    change c * x i = 0
    rw [hx i hi, mul_zero]

theorem sliceVPlus_isCompl_sliceVMinus (slice : List ℕ) :
    IsCompl (sliceVPlus slice) (sliceVMinus slice) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxm
    funext i
    rcases sliceParityR_eq_one_or_neg_one slice i with h1 | hm1
    · exact hxm i h1
    · exact hxp i hm1
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    let xp : SliceVec slice := fun i => if sliceParityR slice i = 1 then x i else 0
    let xm : SliceVec slice := fun i => if sliceParityR slice i = -1 then x i else 0
    have hxp : xp ∈ sliceVPlus slice := by
      intro i hi
      dsimp [xp]
      rw [hi]
      norm_num
    have hxm : xm ∈ sliceVMinus slice := by
      intro i hi
      dsimp [xm]
      rw [hi]
      norm_num
    have hadd : xp + xm = x := by
      funext i
      change (if sliceParityR slice i = 1 then x i else 0) +
          (if sliceParityR slice i = -1 then x i else 0) = x i
      rcases sliceParityR_eq_one_or_neg_one slice i with h1 | hm1
      · rw [h1]; norm_num
      · rw [hm1]; norm_num
    exact Submodule.mem_sup.mpr ⟨xp, hxp, xm, hxm, hadd⟩

theorem sliceVPlus_ortho_sliceVMinus (slice : List ℕ) :
    ∀ x ∈ sliceVPlus slice, ∀ y ∈ sliceVMinus slice,
      (sliceIndefiniteMetric slice).bilin x y = 0 := by
  intro x hx y hy
  change ∑ i : Fin slice.length, sliceParityR slice i * x i * y i = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases sliceParityR_eq_one_or_neg_one slice i with h1 | hm1
  · have hy0 : y i = 0 := hy i h1
    rw [hy0, mul_zero]
  · have hx0 : x i = 0 := hx i hm1
    rw [hx0, mul_zero, zero_mul]

/-- Every finite horizontal slice carries a complete `PTSymmetry` `KreinSpace ℝ` instance. -/
instance sliceKreinSpace (slice : List ℕ) :
    Mathlib.Analysis.InnerProductSpace.Krein.KreinSpace ℝ (SliceVec slice) where
  metric := sliceIndefiniteMetric slice
  V_plus := sliceVPlus slice
  V_minus := sliceVMinus slice
  is_compl := sliceVPlus_isCompl_sliceVMinus slice
  ortho := sliceVPlus_ortho_sliceVMinus slice
  complete := inferInstance

/-- Fundamental involutive parity symmetry `J` on `SliceVec slice`. -/
def sliceJEquiv (slice : List ℕ) : SliceVec slice ≃ₗ[ℝ] SliceVec slice where
  toFun x i := sliceParityR slice i * x i
  invFun x i := sliceParityR slice i * x i
  left_inv x := by
    funext i
    dsimp only
    rw [← mul_assoc, sliceParityR_mul_self, one_mul]
  right_inv x := by
    funext i
    dsimp only
    rw [← mul_assoc, sliceParityR_mul_self, one_mul]
  map_add' x y := by
    funext i
    change sliceParityR slice i * (x i + y i) =
      sliceParityR slice i * x i + sliceParityR slice i * y i
    ring
  map_smul' c x := by
    funext i
    change sliceParityR slice i * (c * x i) = c * (sliceParityR slice i * x i)
    ring

/-- Every finite horizontal slice carries a `PTSymmetry.HasJOperator ℝ` instance. -/
instance sliceHasJOperator (slice : List ℕ) : PTSymmetry.HasJOperator ℝ (SliceVec slice) where
  J := sliceJEquiv slice
  J_involutive := by
    ext x
    funext i
    change sliceParityR slice i * (sliceParityR slice i * x i) = x i
    rw [← mul_assoc, sliceParityR_mul_self, one_mul]
  J_self_adjoint x y := by
    change ∑ i : Fin slice.length, sliceParityR slice i * (sliceParityR slice i * x i) * y i =
      ∑ i : Fin slice.length, sliceParityR slice i * x i * (sliceParityR slice i * y i)
    refine Finset.sum_congr rfl fun i _ => by ring

theorem slice_majorantInner_eq_dot (slice : List ℕ) (x y : SliceVec slice) :
    PTSymmetry.majorantInner (𝕜 := ℝ) (E := SliceVec slice) x y =
      ∑ i : Fin slice.length, x i * y i := by
  change ∑ i : Fin slice.length, sliceParityR slice i * (sliceParityR slice i * x i) * y i =
    ∑ i : Fin slice.length, x i * y i
  refine Finset.sum_congr rfl fun i _ => ?_
  calc sliceParityR slice i * (sliceParityR slice i * x i) * y i
      = (sliceParityR slice i * sliceParityR slice i) * (x i * y i) := by ring
    _ = 1 * (x i * y i) := by rw [sliceParityR_mul_self]
    _ = x i * y i := one_mul _

/-- The Majorant inner product `[J x, y]` on `SliceVec slice` is strictly positive definite. -/
instance sliceMajorantPositiveDefinite (slice : List ℕ) :
    PTSymmetry.MajorantPositiveDefinite ℝ (SliceVec slice) where
  conj_symm x y := by
    simp only [starRingEnd_apply, star_trivial, slice_majorantInner_eq_dot]
    refine Finset.sum_congr rfl fun i _ => by ring
  re_nonneg x := by
    simp only [RCLike.re_to_real, slice_majorantInner_eq_dot]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  definite x hx := by
    rw [slice_majorantInner_eq_dot] at hx
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin slice.length)), x i * x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (x i)).mp hx
    funext i
    exact mul_self_eq_zero.mp (hzero i (Finset.mem_univ i))
  add_left x y z := by
    simp only [slice_majorantInner_eq_dot, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (x i + y i) * z i = x i * z i + y i * z i
    ring
  smul_left x y r := by
    simp only [starRingEnd_apply, star_trivial, slice_majorantInner_eq_dot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (r * x i) * y i = r * (x i * y i)
    ring

/-- Real symmetric coherence matrix `H_ℝ = Re(sliceMatrix slice)`. -/
def sliceRealMatrix (slice : List ℕ) : Matrix (Fin slice.length) (Fin slice.length) ℝ :=
  Matrix.of fun i j => (sliceMatrix slice i j).re

theorem sliceRealMatrix_symm (slice : List ℕ) (i j : Fin slice.length) :
    sliceRealMatrix slice j i = sliceRealMatrix slice i j := by
  unfold sliceRealMatrix
  simp only [Matrix.of_apply]
  have h := congrArg (fun M => (M i j).re) (sliceMatrix_isHermitian slice).eq
  simpa [Matrix.conjTranspose_apply, Complex.star_def] using h

/-- Concrete real $J$-self-adjoint slice operator `C_ℝ = J_ℝ * H_ℝ`. -/
def sliceRealKreinOp (slice : List ℕ) : Matrix (Fin slice.length) (Fin slice.length) ℝ :=
  Matrix.diagonal (sliceParityR slice) * sliceRealMatrix slice

/-- Exact compatibility: `sliceRealKreinOp` equals the real part of `sliceKreinOperator`. -/
theorem sliceRealKreinOp_eq_re_sliceKreinOperator (slice : List ℕ)
    (i j : Fin slice.length) :
    sliceRealKreinOp slice i j = (sliceKreinOperator slice i j).re := by
  unfold sliceRealKreinOp sliceKreinOperator sliceJ sliceRealMatrix sliceParityR
  simp only [Matrix.diagonal_mul, Matrix.of_apply, Complex.mul_re, paritySign_re,
    paritySign_im, zero_mul, sub_zero]

/-- Linear map action of `sliceRealKreinOp` on `SliceVec slice`. -/
def sliceRealKreinLinearMap (slice : List ℕ) : SliceVec slice →ₗ[ℝ] SliceVec slice :=
  Matrix.mulVecLin (sliceRealKreinOp slice)

/-- `sliceRealKreinLinearMap` is `PTSymmetry.IsJAdjoint` in `SliceVec slice`. -/
instance sliceRealKreinLinearMap_isJAdjoint (slice : List ℕ) :
    PTSymmetry.IsJAdjoint (𝕜 := ℝ) (E := SliceVec slice) (sliceRealKreinLinearMap slice) where
  j_adjoint x y := by
    change ∑ i : Fin slice.length,
        sliceParityR slice i * (sliceRealKreinOp slice *ᵥ x) i * y i =
      ∑ i : Fin slice.length,
        sliceParityR slice i * x i * (sliceRealKreinOp slice *ᵥ y) i
    have hL :
        (∑ i : Fin slice.length, sliceParityR slice i * (sliceRealKreinOp slice *ᵥ x) i * y i) =
          ∑ i : Fin slice.length, ∑ j : Fin slice.length,
            sliceRealMatrix slice i j * x j * y i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, sliceRealKreinOp, Matrix.diagonal_mul,
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc sliceParityR slice i * (sliceParityR slice i * sliceRealMatrix slice i j * x j) * y i
          = (sliceParityR slice i * sliceParityR slice i) *
              (sliceRealMatrix slice i j * x j * y i) := by ring
        _ = 1 * (sliceRealMatrix slice i j * x j * y i) := by rw [sliceParityR_mul_self]
        _ = sliceRealMatrix slice i j * x j * y i := one_mul _
    have hR :
        (∑ i : Fin slice.length, sliceParityR slice i * x i * (sliceRealKreinOp slice *ᵥ y) i) =
          ∑ i : Fin slice.length, ∑ j : Fin slice.length,
            sliceRealMatrix slice i j * x i * y j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, sliceRealKreinOp, Matrix.diagonal_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc sliceParityR slice i * x i *
              (sliceParityR slice i * sliceRealMatrix slice i j * y j)
          = (sliceParityR slice i * sliceParityR slice i) *
              (sliceRealMatrix slice i j * x i * y j) := by ring
        _ = 1 * (sliceRealMatrix slice i j * x i * y j) := by rw [sliceParityR_mul_self]
        _ = sliceRealMatrix slice i j * x i * y j := one_mul _
    rw [hL, hR, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sliceRealMatrix_symm slice i j]

end KinematicRiemann
