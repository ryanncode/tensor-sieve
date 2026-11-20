import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Group.List.Basic
import TensorSieve.Kinematics
import TensorSieve.KreinSpace

/-!
# The Discrete Arithmetic Slice Operator and Krein Spectral Structure

This module defines the computable Hermitian coherence matrix `sliceMatrix` and
the associated finite-dimensional $J$-self-adjoint Krein operator `sliceKreinOperator`
acting on horizontal divisibility slices of the integers.

It proves without custom axioms or `sorry`:
1. Symmetry of `valuationDivergence` and conjugate symmetry of `crossBranchAmplitude`.
2. `sliceMatrix_isHermitian`: `(sliceMatrix slice).IsHermitian`.
3. `sliceKreinOperator_isJAdjoint`: `J * C = Cᴴ * J` for `C = J * H`.
4. `krein_eigenvalue_real_of_non_isotropic`: every non-isotropic eigenvector (`[v, v] ≠ 0`)
   of a $J$-self-adjoint matrix has a strictly real eigenvalue (`λ.im = 0`).
-/

namespace KinematicRiemann

open Matrix

/-- Computable helper to strictly count prime factors with multiplicity (`Ω(n)`). -/
def countFactors (n : ℕ) : ℕ :=
  if h : n > 1 then
    have h1 : 1 < n.minFac := (Nat.minFac_prime (ne_of_gt h)).one_lt
    have h2 : n / n.minFac < n := Nat.div_lt_self (Nat.lt_trans (by decide) h) h1
    1 + countFactors (n / n.minFac)
  else 0
termination_by n

/-- Computes the local topological degree `Ω(a)`. -/
def compLocalDegree (a : SemanticAddress) : ℕ :=
  countFactors a.val

/-- Recursively extracts distinct prime factors with explicit fuel. -/
def distinctPrimeFactorsFuel (fuel : ℕ) (n : ℕ) (p : ℕ) (acc : List ℕ) : List ℕ :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if n <= 1 then acc
    else if p * p > n then
      if !acc.contains n then n :: acc else acc
    else if n % p == 0 then
      let rec remove_p (y : ℕ) (f2 : ℕ) :=
        match f2 with
        | 0 => y
        | f3 + 1 => if y % p == 0 then remove_p (y / p) f3 else y
      distinctPrimeFactorsFuel f (remove_p n f) (p + 1) (if !acc.contains p then p :: acc else acc)
    else
      distinctPrimeFactorsFuel f n (p + 1) acc

/-- Computes distinct prime factors of `n`. -/
def distinctPrimeFactors (n : ℕ) : List ℕ :=
  distinctPrimeFactorsFuel n n 2 []

/-- Computes the exponent of `p` in the prime factorization of `n`. -/
def pAdicValuation (n p : ℕ) : ℕ :=
  if h : p > 1 ∧ n > 0 then
    if n % p == 0 then
      have : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero
        (fun h0 => by rw [h0] at h; exact Nat.lt_irrefl 0 h.2)) h.1
      1 + pAdicValuation (n / p) p
    else 0
  else 0
termination_by n

/-- Computes the L1-norm divergence between two numbers based on their `p`-adic valuations. -/
def valuationDivergence (a b : ℕ) : ℕ :=
  let primesA := distinctPrimeFactors a
  let primesB := distinctPrimeFactors b
  let allPrimes := (primesA ++ primesB).dedup
  allPrimes.foldl (fun acc p =>
    let va := pAdicValuation a p
    let vb := pAdicValuation b p
    acc + (if va > vb then va - vb else vb - va)
  ) 0

private lemma foldl_add_nat_eq_sum (l : List ℕ) (f : ℕ → ℕ) (init : ℕ) :
    l.foldl (fun acc p => acc + f p) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (init + f hd)]
    omega

/-- `valuationDivergence` is symmetric: `valuationDivergence a b = valuationDivergence b a`. -/
theorem valuationDivergence_comm (a b : ℕ) :
    valuationDivergence a b = valuationDivergence b a := by
  unfold valuationDivergence
  dsimp only
  set l1 := (distinctPrimeFactors a ++ distinctPrimeFactors b).dedup
  set l2 := (distinctPrimeFactors b ++ distinctPrimeFactors a).dedup
  set f : ℕ → ℕ := fun p =>
    let va := pAdicValuation a p
    let vb := pAdicValuation b p
    if va > vb then va - vb else vb - va
  set g : ℕ → ℕ := fun p =>
    let vb := pAdicValuation b p
    let va := pAdicValuation a p
    if vb > va then vb - va else va - vb
  have hfg : f = g := by
    funext p
    dsimp only [f, g]
    split_ifs <;> omega
  have hperm : l1.Perm l2 := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)]
    intro x
    simp only [List.mem_dedup, List.mem_append]
    exact Or.comm
  rw [foldl_add_nat_eq_sum l1 f 0, foldl_add_nat_eq_sum l2 g 0, hfg]
  simp only [Nat.zero_add]
  exact (hperm.map g).sum_eq

/-- Greatest common divisor as shared structural depth between two nodes. -/
def sharedSemanticRoot (a b : ℕ) : ℕ := Nat.gcd a b

theorem sharedSemanticRoot_comm (a b : ℕ) :
    sharedSemanticRoot a b = sharedSemanticRoot b a :=
  Nat.gcd_comm a b

/-- Computable 2D Krein coordinate system over `ℤ`. -/
def KreinCoord := ℤ × ℤ

/-- Involutive `J` operator swapping positive and negative subspaces. -/
def KreinJ (v : KreinCoord) : KreinCoord := (v.2, v.1)

/-- Indefinite bilinear metric `[x, y] = x₁y₁ - x₂y₂`. -/
def KreinBilin (u v : KreinCoord) : ℤ := u.1 * v.1 - u.2 * v.2

/-- Maps a natural number to its Krein parity unit vector via `Ω(n) mod 2`. -/
def addressToKreinUnit (n : ℕ) : KreinCoord :=
  if h : n > 1 then
    have h1 : 1 < n.minFac := (Nat.minFac_prime (ne_of_gt h)).one_lt
    have h2 : n / n.minFac < n := Nat.div_lt_self (Nat.lt_trans (by decide) h) h1
    let parent_vec := addressToKreinUnit (n / n.minFac)
    KreinJ parent_vec
  else
    (1, 0)
termination_by n

/-- Scales a Krein coordinate vector by an integer weight. -/
def KreinScalarMul (c : ℤ) (v : KreinCoord) : KreinCoord :=
  (c * v.1, c * v.2)

theorem addressToKreinUnit_cases (n : ℕ) :
    addressToKreinUnit n = (1, 0) ∨ addressToKreinUnit n = (0, 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold addressToKreinUnit
    split_ifs with h
    · have h1 : 1 < n.minFac := (Nat.minFac_prime (ne_of_gt h)).one_lt
      have h2 : n / n.minFac < n := Nat.div_lt_self (Nat.lt_trans (by decide) h) h1
      rcases ih (n / n.minFac) h2 with hp | hp
      · right; simp [KreinJ, hp]
      · left; simp [KreinJ, hp]
    · left; rfl

/-- Complex parity sign `±1` associated with node `a`, matching `krein/src/lib.rs`. -/
def paritySign (a : ℕ) : ℂ :=
  ((KreinBilin (addressToKreinUnit a) (1, 1) : ℤ) : ℂ)

theorem paritySign_eq_one_or_neg_one (a : ℕ) :
    paritySign a = 1 ∨ paritySign a = -1 := by
  unfold paritySign KreinBilin
  rcases addressToKreinUnit_cases a with h | h <;> rw [h] <;> simp

theorem paritySign_mul_self (a : ℕ) : paritySign a * paritySign a = 1 := by
  rcases paritySign_eq_one_or_neg_one a with h | h <;> rw [h] <;> ring

theorem star_paritySign (a : ℕ) : star (paritySign a) = paritySign a := by
  rcases paritySign_eq_one_or_neg_one a with h | h <;> rw [h] <;> simp

/--
The Hermitian coherence amplitude between nodes `a` and `b`.
The real part is symmetric in `(a, b)` and the imaginary part is antisymmetric,
breaking time-reversal symmetry while guaranteeing exact Hermiticity.
-/
def crossBranchAmplitude (a b : ℕ) : ℂ :=
  let g := sharedSemanticRoot a b
  let w := countFactors g
  let unitG := addressToKreinUnit g
  let basis : KreinCoord := (1, 1)
  if a == b then
    let vecG := KreinScalarMul (w : ℤ) unitG
    let realPart := KreinBilin vecG basis
    Complex.mk (realPart : ℝ) 0
  else
    let dist := valuationDivergence a b
    if dist > w then
      Complex.mk 0 0
    else
      let vecG := KreinScalarMul ((w - dist) : ℤ) unitG
      let realPart := KreinBilin vecG basis
      let distR := (dist : ℝ)
      let imag := if a > b then distR else -distR
      Complex.mk (realPart : ℝ) imag

/-- Conjugate symmetry of `crossBranchAmplitude`. -/
theorem crossBranchAmplitude_conj_symm (a b : ℕ) :
    star (crossBranchAmplitude b a) = crossBranchAmplitude a b := by
  unfold crossBranchAmplitude
  by_cases hab : a = b
  · subst hab
    simp only [beq_self_eq_true, ↓reduceIte]
    apply Complex.ext <;> simp
  · have hba : b ≠ a := Ne.symm hab
    have h1 : (a == b) = false := beq_false_of_ne hab
    have h2 : (b == a) = false := beq_false_of_ne hba
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    rw [sharedSemanticRoot_comm b a, valuationDivergence_comm b a]
    by_cases hd : valuationDivergence a b > countFactors (sharedSemanticRoot a b)
    · simp only [hd, ↓reduceIte]
      apply Complex.ext <;> simp
    · simp only [hd, ↓reduceIte]
      by_cases hgt : a > b
      · have hnot : ¬ (b > a) := by omega
        apply Complex.ext <;> simp [hgt, hnot]
      · have hgt' : b > a := by omega
        apply Complex.ext <;> simp [hgt, hgt']

/-- Formal Hermitian coherence matrix `H` on a horizontal slice. -/
def sliceMatrix (slice : List ℕ) : Matrix (Fin slice.length) (Fin slice.length) ℂ :=
  Matrix.of fun i j =>
    crossBranchAmplitude (slice.get ⟨i.val, i.isLt⟩) (slice.get ⟨j.val, j.isLt⟩)

/-- `sliceMatrix slice` is strictly Hermitian (`Hᴴ = H`). -/
theorem sliceMatrix_isHermitian (slice : List ℕ) :
    (sliceMatrix slice).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, sliceMatrix, Matrix.of_apply]
  exact crossBranchAmplitude_conj_symm _ _

/-- Fundamental diagonal Krein symmetry matrix `J = diag(paritySign(a_i))` on a slice. -/
def sliceJ (slice : List ℕ) : Matrix (Fin slice.length) (Fin slice.length) ℂ :=
  Matrix.diagonal (fun i => paritySign (slice.get ⟨i.val, i.isLt⟩))

/-- `J² = I` on every horizontal slice. -/
theorem sliceJ_sq (slice : List ℕ) : sliceJ slice * sliceJ slice = 1 := by
  unfold sliceJ
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i : Fin slice.length =>
      paritySign (slice.get ⟨i.val, i.isLt⟩) * paritySign (slice.get ⟨i.val, i.isLt⟩)) =
      fun _ => (1 : ℂ) := by
    funext i
    exact paritySign_mul_self _
  rw [h, Matrix.diagonal_one]

/-- `Jᴴ = J` on every horizontal slice. -/
theorem sliceJ_isHermitian (slice : List ℕ) : (sliceJ slice).IsHermitian := by
  unfold sliceJ
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp [star_paritySign]
  · have h' : j ≠ i := Ne.symm h
    simp [h, h']

/--
The concrete finite-dimensional Krein slice operator `C = J * H`,
matching the exact matrix diagonalized in `krein/src/lib.rs`.
-/
def sliceKreinOperator (slice : List ℕ) : Matrix (Fin slice.length) (Fin slice.length) ℂ :=
  sliceJ slice * sliceMatrix slice

/-- Linear map realization of `sliceKreinOperator` acting on `Fin slice.length → ℂ`. -/
def sliceKreinLinearMap (slice : List ℕ) :
    (Fin slice.length → ℂ) →ₗ[ℂ] (Fin slice.length → ℂ) :=
  Matrix.mulVecLin (sliceKreinOperator slice)

/-- `C = J * H` is strictly $J$-self-adjoint: `J * C = Cᴴ * J`. -/
theorem sliceKreinOperator_isJAdjoint (slice : List ℕ) :
    sliceJ slice * sliceKreinOperator slice = (sliceKreinOperator slice)ᴴ * sliceJ slice := by
  unfold sliceKreinOperator
  rw [← Matrix.mul_assoc, sliceJ_sq, Matrix.one_mul]
  rw [Matrix.conjTranspose_mul, (sliceMatrix_isHermitian slice).eq, (sliceJ_isHermitian slice).eq,
    Matrix.mul_assoc, sliceJ_sq, Matrix.mul_one]

/--
Finite-dimensional Krein Spectral Reality Theorem:
If `J` is Hermitian, `C` is `J`-self-adjoint (`J * C = Cᴴ * J`), and `C *ᵥ v = lam • v`
with non-zero Krein inner product `[v, v]_J = ⟪v, J v⟫ ≠ 0`, then `lam` is strictly real.
Equivalently, complex conjugate eigenvalue pairs can arise ONLY on neutral/isotropic
eigenvectors (`[v, v]_J = 0`).
-/
theorem krein_eigenvalue_real_of_non_isotropic {n : ℕ}
    (J C : Matrix (Fin n) (Fin n) ℂ)
    (hJC : J * C = Cᴴ * J)
    (v : Fin n → ℂ) (lam : ℂ)
    (heig : C *ᵥ v = lam • v)
    (hnoniso : dotProduct (star v) (J *ᵥ v) ≠ 0) :
    lam.im = 0 := by
  have h1 : dotProduct (star v) (J *ᵥ (C *ᵥ v)) = lam * dotProduct (star v) (J *ᵥ v) := by
    rw [heig, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : dotProduct (star v) (J *ᵥ (C *ᵥ v)) = star lam * dotProduct (star v) (J *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hJC, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star, heig]
    simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', dotProduct,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : (lam - star lam) * dotProduct (star v) (J *ᵥ v) = 0 := by
    linear_combination h1.symm.trans h2
  have h4 : lam - star lam = 0 := (mul_eq_zero.mp h3).resolve_right hnoniso
  have h5 : lam = star lam := sub_eq_zero.mp h4
  have him := congrArg Complex.im h5
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- Computes the trace of the coherence matrix across a horizontal slice. -/
def traceHamiltonian (slice : List ℕ) : ℂ :=
  slice.foldl (fun acc a => acc + crossBranchAmplitude a a) 0

/-- Computes the next horizontal topological slice moving downward by single prime steps. -/
def nextSlice (slice : List ℕ) : List ℕ :=
  let next_nodes := slice.flatMap (fun x =>
    let factors := distinctPrimeFactors x
    factors.map (fun p => x / p)
  )
  List.eraseDups next_nodes

/-- Sequence of downward slice states `(level, x, localDegree)`. -/
def emissionSpectrumDown (start : ℕ) (steps : ℕ) : List (ℕ × ℕ × ℕ) :=
  let rec loop (slice : List ℕ) (n : ℕ) (acc : List (ℕ × ℕ × ℕ)) :=
    match n with
    | 0 => acc.reverse
    | n' + 1 =>
        if slice.isEmpty then acc.reverse
        else if slice.all (fun x => x <= 1) then acc.reverse
        else
          let w := if slice.isEmpty then 0 else countFactors (slice.head!)
          let new_acc := slice.foldl (fun (lst : List (ℕ × ℕ × ℕ)) (x : ℕ) =>
            let deg := countFactors x
            (w, x, deg) :: lst
          ) acc
          let next_s := nextSlice slice
          loop next_s n' new_acc
  loop [start] steps []

end KinematicRiemann
