import TensorSieve.Kinematics
import TensorSieve.Operator
import TensorSieve.LambdaRing
import TensorSieve.FTNILO
import TensorSieve.AxCal
import TensorSieve.PunctureMask

/-!
# Slice Trace Integrality and Constant-Weight Parity Theorems

This module establishes exact structural properties of the discrete slice
coherence matrix `sliceMatrix` and Krein operator `sliceKreinOperator` from
`TensorSieve.Operator`:

1. `SemanticAddressMetric`: equips `SemanticAddress` with the symmetric,
   division-free `p`-adic `L¹` tree distance `valuationDivergence`.
2. `addressToKreinUnit_parity` & `diagonalAmplitudeInt_eq`: proves that
   the diagonal amplitude of node `a` equals `(-1)^Ω(a) · Ω(a)`.
3. `countFactors_eq_primeFactorsList_length` & `countFactors_div_prime`:
   proves `countFactors` equals `Nat.primeFactorsList.length` and drops by
   exactly `1` under division by any prime factor `p ∣ n`.
4. `traceHamiltonian_is_int` & `traceHamiltonian_of_uniform_weight`:
   proves the trace over any slice is an integer, and evaluates in closed form
   to `(-1)^k · k · |slice|` on any constant-weight slice (`∀ x ∈ slice, Ω(x) = k`).
5. `sliceJ_of_uniform_weight` & `sliceKreinOperator_isHermitian_of_uniform_weight`:
   proves that on any constant-weight slice, the Krein symmetry reduces to the
   scalar matrix `J = (-1)^k · I`, so `C = J · H` is itself Hermitian.
-/

namespace KinematicRiemann

open Matrix

/--
Division-free `p`-adic `L¹` tree distance on `SemanticAddress`,
using `valuationDivergence` from `TensorSieve.Operator`.
-/
instance SemanticAddressMetric : DivisionFreeMetric SemanticAddress where
  dist_sq a b := (valuationDivergence a.val b.val : ℤ)
  dist_sq_computable _ _ := inferInstance

/-- The `p`-adic tree distance on `SemanticAddress` is symmetric. -/
theorem SemanticAddressMetric_symm (a b : SemanticAddress) :
    @DivisionFreeMetric.dist_sq SemanticAddress SemanticAddressMetric a b =
      @DivisionFreeMetric.dist_sq SemanticAddress SemanticAddressMetric b a := by
  change (valuationDivergence a.val b.val : ℤ) = (valuationDivergence b.val a.val : ℤ)
  rw [valuationDivergence_comm]

/-- Computes the integer diagonal amplitude for a node `a`. -/
def diagonalAmplitudeInt (a : ℕ) : ℤ :=
  let g := sharedSemanticRoot a a
  let w := countFactors g
  let unitG := addressToKreinUnit g
  let basis : KreinCoord := (1, 1)
  let vecG := KreinScalarMul (w : ℤ) unitG
  KreinBilin vecG basis

/-- Applying `KreinJ` negates the indefinite pairing against `(1, 1)`. -/
lemma kreinBilin_kreinJ_ones (v : KreinCoord) :
    KreinBilin (KreinJ v) (1, 1) = -KreinBilin v (1, 1) := by
  dsimp [KreinBilin, KreinJ]
  ring

/-- The Krein parity sign of `addressToKreinUnit n` equals `(-1)^(countFactors n)`. -/
theorem addressToKreinUnit_parity (n : ℕ) :
    KreinBilin (addressToKreinUnit n) (1, 1) = (-1 : ℤ) ^ countFactors n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold addressToKreinUnit countFactors
    split_ifs with h
    · have h1 : 1 < n.minFac := (Nat.minFac_prime (ne_of_gt h)).one_lt
      have h2 : n / n.minFac < n := Nat.div_lt_self (Nat.lt_trans (by decide) h) h1
      rw [kreinBilin_kreinJ_ones, ih (n / n.minFac) h2, pow_add, pow_one]
      ring
    · dsimp [KreinBilin]

/-- Complex `paritySign a` equals `((-1 : ℤ) ^ countFactors a : ℂ)`. -/
theorem paritySign_eq_neg_one_pow (a : ℕ) :
    paritySign a = (((-1 : ℤ) ^ countFactors a : ℤ) : ℂ) := by
  unfold paritySign
  rw [addressToKreinUnit_parity]

/-- Closed form for the integer diagonal amplitude: `(-1)^Ω(a) · Ω(a)`. -/
theorem diagonalAmplitudeInt_eq (a : ℕ) :
    diagonalAmplitudeInt a = (-1 : ℤ) ^ countFactors a * (countFactors a : ℤ) := by
  unfold diagonalAmplitudeInt sharedSemanticRoot
  rw [Nat.gcd_self]
  have hmul : KreinBilin (KreinScalarMul (countFactors a : ℤ) (addressToKreinUnit a)) (1, 1) =
      (countFactors a : ℤ) * KreinBilin (addressToKreinUnit a) (1, 1) := by
    dsimp [KreinBilin, KreinScalarMul]
    ring
  rw [hmul, addressToKreinUnit_parity]
  ring

/-- `countFactors n` agrees identically with Mathlib's `n.primeFactorsList.length`. -/
theorem countFactors_eq_primeFactorsList_length (n : ℕ) :
    countFactors n = n.primeFactorsList.length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold countFactors
    split_ifs with h
    · have hne0 : n ≠ 0 := by omega
      have hne1 : n ≠ 1 := by omega
      have hp : n.minFac.Prime := Nat.minFac_prime hne1
      have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hdiv_lt : n / n.minFac < n := Nat.div_lt_self (by omega) hp.one_lt
      have hdiv_ne0 : n / n.minFac ≠ 0 := by
        intro h0
        have hmul := Nat.mul_div_cancel' hdvd
        rw [h0, mul_zero] at hmul
        exact hne0 hmul.symm
      have hperm := Nat.perm_primeFactorsList_mul hp.ne_zero hdiv_ne0
      rw [Nat.mul_div_cancel' hdvd] at hperm
      rw [hperm.length_eq, List.length_append, Nat.primeFactorsList_prime hp, List.length_singleton,
        ih (n / n.minFac) hdiv_lt]
    · interval_cases n <;> simp

/-- Dividing a positive integer `n` by any prime factor `p ∣ n` reduces `countFactors` by `1`. -/
theorem countFactors_div_prime {n p : ℕ} (hp : p.Prime) (hdvd : p ∣ n) (hn : n ≠ 0) :
    countFactors (n / p) + 1 = countFactors n := by
  rw [countFactors_eq_primeFactorsList_length, countFactors_eq_primeFactorsList_length]
  have hdiv_ne0 : n / p ≠ 0 := by
    intro h0
    have hmul := Nat.mul_div_cancel' hdvd
    rw [h0, mul_zero] at hmul
    exact hn hmul.symm
  have hperm := Nat.perm_primeFactorsList_mul hp.ne_zero hdiv_ne0
  rw [Nat.mul_div_cancel' hdvd] at hperm
  rw [hperm.length_eq, List.length_append, Nat.primeFactorsList_prime hp, List.length_singleton]
  omega

/-- Diagonal cross-branch amplitudes are exact casts of `diagonalAmplitudeInt`. -/
lemma crossBranchAmplitude_self_eq_cast (a : ℕ) :
    crossBranchAmplitude a a = (diagonalAmplitudeInt a : ℂ) := by
  dsimp [crossBranchAmplitude, diagonalAmplitudeInt]
  have h_eq : (a == a) = true := beq_self_eq_true a
  rw [h_eq, if_pos rfl]
  apply Complex.ext
  · simp
  · simp

/-- Folding diagonal amplitudes across a list preserves integer values. -/
lemma foldl_diagonal_eq_cast (l : List ℕ) (init : ℤ) :
    l.foldl (fun acc a => acc + crossBranchAmplitude a a) (init : ℂ) =
      ((l.foldl (fun acc a => acc + diagonalAmplitudeInt a) init : ℤ) : ℂ) := by
  induction l generalizing init with
  | nil => rfl
  | cons head tail ih =>
    dsimp [List.foldl]
    rw [crossBranchAmplitude_self_eq_cast head]
    have h_add : (init : ℂ) + (diagonalAmplitudeInt head : ℂ) =
        ((init + diagonalAmplitudeInt head : ℤ) : ℂ) := by
      push_cast
      rfl
    rw [h_add]
    exact ih (init + diagonalAmplitudeInt head)

/-- The trace of the coherence matrix over any finite slice is an integer. -/
theorem traceHamiltonian_is_int (slice : List ℕ) :
    ∃ (bound : ℤ), traceHamiltonian slice = bound := by
  dsimp [traceHamiltonian]
  use slice.foldl (fun acc a => acc + diagonalAmplitudeInt a) 0
  have h0 : (0 : ℂ) = ((0 : ℤ) : ℂ) := by simp
  rw [h0]
  exact foldl_diagonal_eq_cast slice 0

private lemma foldl_diagonal_uniform (l : List ℕ) (k : ℕ) (init : ℤ)
    (hunif : ∀ x ∈ l, countFactors x = k) :
    l.foldl (fun acc a => acc + diagonalAmplitudeInt a) init =
      init + ((-1 : ℤ) ^ k * (k : ℤ)) * (l.length : ℤ) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hhd : countFactors hd = k := hunif hd (by simp)
    have htl : ∀ x ∈ tl, countFactors x = k := fun x hx => hunif x (by simp [hx])
    rw [diagonalAmplitudeInt_eq hd, hhd, ih (init + (-1 : ℤ) ^ k * (k : ℤ)) htl]
    ring

/--
Closed-form trace identity on any constant-weight slice (`∀ x ∈ slice, Ω(x) = k`):
`traceHamiltonian slice = (-1)^k · k · |slice|`.
-/
theorem traceHamiltonian_of_uniform_weight (slice : List ℕ) (k : ℕ)
    (hunif : ∀ x ∈ slice, countFactors x = k) :
    traceHamiltonian slice = (((-1 : ℤ) ^ k * (k : ℤ) * (slice.length : ℤ) : ℤ) : ℂ) := by
  dsimp [traceHamiltonian]
  have h0 : (0 : ℂ) = ((0 : ℤ) : ℂ) := by simp
  rw [h0, foldl_diagonal_eq_cast, foldl_diagonal_uniform slice k 0 hunif, zero_add]

/--
On any constant-weight slice (`∀ x ∈ slice, Ω(x) = k`), the Krein symmetry matrix
reduces to a scalar multiple of the identity: `sliceJ slice = (-1)^k · I`.
-/
theorem sliceJ_of_uniform_weight (slice : List ℕ) (k : ℕ)
    (hunif : ∀ x ∈ slice, countFactors x = k) :
    sliceJ slice =
      ((((-1 : ℤ) ^ k : ℤ) : ℂ) • (1 : Matrix (Fin slice.length) (Fin slice.length) ℂ)) := by
  ext i j
  simp only [sliceJ, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    have hmem : slice.get ⟨i.val, i.isLt⟩ ∈ slice := List.get_mem slice ⟨i.val, i.isLt⟩
    rw [if_pos rfl, if_pos rfl, mul_one, paritySign_eq_neg_one_pow, hunif _ hmem]
  · simp [h]

/--
Corollary: On any constant-weight horizontal slice, the Krein operator
`C = J · H` equals `±H` and is itself strictly Hermitian (hence all its
eigenvalues are real; broken-PT complex conjugate pairs require mixing levels
of opposite `Ω`-parity).
-/
theorem sliceKreinOperator_isHermitian_of_uniform_weight (slice : List ℕ) (k : ℕ)
    (hunif : ∀ x ∈ slice, countFactors x = k) :
    (sliceKreinOperator slice).IsHermitian := by
  unfold sliceKreinOperator
  rw [sliceJ_of_uniform_weight slice k hunif, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
  have hH : star ((sliceMatrix slice) j i) = (sliceMatrix slice) i j := by
    have := congrFun (congrFun (sliceMatrix_isHermitian slice).eq i) j
    simpa [Matrix.conjTranspose_apply] using this
  have hs : star ((((-1 : ℤ) ^ k : ℤ) : ℂ)) = (((-1 : ℤ) ^ k : ℤ) : ℂ) := by
    simp
  rw [hs, hH]

/--
Combined slice integrality and binary-gate summary for a horizontal slice
(retains the original theorem name for compatibility with `TestSuite.lean`).
-/
theorem global_spectral_invariance
  (N : SemanticAddress)
  (slice : List ℕ)
  (_h_slice : slice = nextSlice [N.val]) :
  ∃ (bound : ℤ),
    traceHamiltonian slice = bound ∧
    (∀ x ∈ slice,
      diracDeltaGate (x : ℤ) (N.val : ℤ) = 1 ∨ diracDeltaGate (x : ℤ) (N.val : ℤ) = 0) := by
  obtain ⟨bound, h_bound⟩ := traceHamiltonian_is_int slice
  refine ⟨bound, h_bound, ?_⟩
  intro x _
  exact delta_consistency (x : ℤ) (N.val : ℤ)

end KinematicRiemann
