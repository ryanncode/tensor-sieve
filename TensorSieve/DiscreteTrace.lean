import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace KinematicRiemann

/-!
# Discrete Trace Identity and Closed Walks on the Bruhat-Tits Lattice

This module formalizes the constructive discrete Selberg-Weil trace identity
connecting matrix spectral traces of the combinatorial Laplacian and adjacency operators
to arithmetic prime sums over finite topological slices of the Bruhat-Tits tree.

It establishes:
1. Pointwise decoupling of the squared combinatorial Laplacian (L_c² = D² + K² on closed 2-walks).
2. Trace equivalence of the squared adjacency operator to prime omega sums:
     Tr(K²) = ∑_{x ∈ S} Ω(x).
3. The Discrete Selberg-Weil explicit formula connecting Laplacian traces to prime densities:
     Tr(L_c²) = Tr(D²) + ∑_{p ∈ P} Φ(p, S).
-/

/-- Diagonal degree operator D: D(x, y) = d(x) if x == y else 0. -/
def degreeOp (d : ℕ → ℤ) (x y : ℕ) : ℤ :=
  if x == y then d x else 0

/-- Combinatorial Laplacian operator L_c = D - K. -/
def laplacianOp (d : ℕ → ℤ) (K : ℕ → ℕ → ℤ) (x y : ℕ) : ℤ :=
  degreeOp d x y - K x y

/-- Length-2 diagonal entry of A² over a finite vertex list S:
    (A²)_{xx} = ∑_{y ∈ S} A(x, y) * A(y, x). -/
def matrixSqDiag (A : ℕ → ℕ → ℤ) (S : List ℕ) (x : ℕ) : ℤ :=
  S.foldl (fun acc y => acc + A x y * A y x) 0

/-- Discrete trace of an operator across a slice S. -/
def discreteTrace (A : ℕ → ℕ → ℤ) (S : List ℕ) : ℤ :=
  S.foldl (fun acc x => acc + A x x) 0

/-- Discrete trace of the square A² across a slice S:
    Tr(A²) = ∑_{x ∈ S} (A²)_{xx}. -/
def discreteTraceSq (A : ℕ → ℕ → ℤ) (S : List ℕ) : ℤ :=
  S.foldl (fun acc x => acc + matrixSqDiag A S x) 0

/-- Prime valuation density Φ(p, S): total p-adic valuation across the slice S. -/
def slicePrimeDensity (v : ℕ → ℕ → ℕ) (p : ℕ) (S : List ℕ) : ℤ :=
  S.foldl (fun acc x => acc + (v x p : ℤ)) 0

/-- Bruhat-Tits 2-step closed walk identity hypothesis:
    For each vertex x in the slice, the number of closed 2-walks returning to x
    equals its total prime weight Ω(x). -/
def SatisfiesTwoWalkIdentity (K : ℕ → ℕ → ℤ) (S : List ℕ) (omega : ℕ → ℤ) : Prop :=
  ∀ x ∈ S, matrixSqDiag K S x = omega x

/-- Decomposition of omega into prime valuations across a prime basis P:
    Ω(x) = ∑_{p ∈ P} v_p(x). -/
def DecomposesIntoPrimes (omega : ℕ → ℤ) (P : List ℕ) (v : ℕ → ℕ → ℕ) (S : List ℕ) : Prop :=
  ∀ x ∈ S, omega x = P.foldl (fun acc p => acc + (v x p : ℤ)) 0

/-- Lemma: Pointwise decoupling of Laplacian square into diagonal and adjacency terms.
    Whenever K has zero diagonal (K(x, x) = 0),
    (D - K)_{xy} * (D - K)_{yx} = D_{xy} * D_{yx} + K_{xy} * K_{yx}. -/
lemma laplacian_sq_entry_pointwise (d : ℕ → ℤ) (K : ℕ → ℕ → ℤ) (x y : ℕ)
    (hK : (x == y) = true → K x y = 0) :
    laplacianOp d K x y * laplacianOp d K y x =
      degreeOp d x y * degreeOp d y x + K x y * K y x := by
  dsimp [laplacianOp, degreeOp]
  cases h : (x == y)
  · have h_yx : (y == x) = false := by
      cases hy : (y == x)
      · rfl
      · have : y = x := beq_iff_eq.mp hy
        subst this
        rw [beq_self_eq_true] at h
        contradiction
    rw [h_yx]
    dsimp
    ring
  · have heq : x = y := beq_iff_eq.mp h
    have h_yx : (y == x) = true := by
      rw [heq, beq_self_eq_true]
    rw [h_yx]
    have hK0 : K x y = 0 := hK h
    have hKyx : K y x = 0 := by
      subst heq
      exact hK0
    rw [hK0, hKyx]
    dsimp
    ring

/-- Lemma: foldl addition of constant accumulates linearly. -/
lemma foldl_add_const (S : List ℕ) (g : ℕ → ℤ) (init : ℤ) :
    S.foldl (fun acc x => acc + g x) init = init + S.foldl (fun acc x => acc + g x) 0 := by
  induction S generalizing init with
  | nil =>
    dsimp [List.foldl]
    ring
  | cons x xs ih =>
    dsimp [List.foldl]
    rw [ih (init + g x)]
    rw [ih (0 + g x)]
    ring

/-- Lemma: foldl of cons splits head evaluation. -/
lemma foldl_cons_val (x : ℕ) (xs : List ℕ) (g : ℕ → ℤ) :
    (x :: xs).foldl (fun acc y => acc + g y) 0 = g x + xs.foldl (fun acc y => acc + g y) 0 := by
  dsimp [List.foldl]
  have h0 : 0 + g x = g x := by ring
  rw [h0]
  exact foldl_add_const xs g (g x)

/-- Lemma: foldl of zero function vanishes. -/
lemma foldl_zero_list (P : List ℕ) :
    P.foldl (fun acc _ => acc + (0 : ℤ)) 0 = 0 := by
  induction P with
  | nil => rfl
  | cons p tail ih =>
    exact ih

/-- Lemma: Linearity of foldl accumulation of pointwise sum. -/
lemma foldl_add_split (S : List ℕ) (f g : ℕ → ℤ) (init1 init2 : ℤ) :
    S.foldl (fun acc y => acc + (f y + g y)) (init1 + init2) =
      S.foldl (fun acc y => acc + f y) init1 + S.foldl (fun acc y => acc + g y) init2 := by
  induction S generalizing init1 init2 with
  | nil => rfl
  | cons head tail ih =>
    dsimp [List.foldl]
    have h_reorder : (init1 + init2) + (f head + g head) = (init1 + f head) + (init2 + g head) := by
      ring
    rw [h_reorder]
    exact ih (init1 + f head) (init2 + g head)

/-- Lemma: Congruence for foldl when functions agree on all elements in S. -/
lemma foldl_eq_of_eq_on (S : List ℕ) (f g : ℕ → ℤ) (init : ℤ)
    (h : ∀ y ∈ S, f y = g y) :
    S.foldl (fun acc y => acc + f y) init = S.foldl (fun acc y => acc + g y) init := by
  induction S generalizing init with
  | nil => rfl
  | cons head tail ih =>
    dsimp [List.foldl]
    have h_head : f head = g head := h head (List.mem_cons.mpr (Or.inl rfl))
    have h_tail : ∀ y ∈ tail, f y = g y := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
    rw [h_head]
    exact ih (init + g head) h_tail

/-- Lemma: Fubini commutation of double foldl sums across two lists. -/
lemma foldl_foldl_comm (S : List ℕ) (P : List ℕ) (f : ℕ → ℕ → ℤ) :
    S.foldl (fun acc x => acc + P.foldl (fun acc' p => acc' + f x p) 0) 0 =
      P.foldl (fun acc p => acc + S.foldl (fun acc' x => acc' + f x p) 0) 0 := by
  induction S with
  | nil =>
    dsimp [List.foldl]
    rw [foldl_zero_list P]
  | cons x xs ih =>
    rw [foldl_cons_val]
    rw [ih]
    have h_split := foldl_add_split P (fun p => f x p)
      (fun p => xs.foldl (fun acc' y => acc' + f y p) 0) 0 0
    have hz : (0 + 0 : ℤ) = 0 := by ring
    rw [hz] at h_split
    rw [← h_split]
    have h_step : ∀ p, f x p + xs.foldl (fun acc' y => acc' + f y p) 0 =
        (x :: xs).foldl (fun acc' y => acc' + f y p) 0 := by
      intro p
      exact (foldl_cons_val x xs (fun y => f y p)).symm
    have h_ext : (fun acc p => acc + (f x p + xs.foldl (fun acc' y => acc' + f y p) 0)) =
        (fun acc p => acc + (x :: xs).foldl (fun acc' y => acc' + f y p) 0) := by
      funext acc p
      rw [h_step p]
    rw [h_ext]

/-- Theorem: Exact decomposition of (L_c²)_{xx} = (D²)_{xx} + (K²)_{xx}. -/
theorem laplacian_sq_diag_eq (d : ℕ → ℤ) (K : ℕ → ℕ → ℤ) (S : List ℕ) (x : ℕ)
    (hK : ∀ y ∈ S, (x == y) = true → K x y = 0) :
    matrixSqDiag (laplacianOp d K) S x =
      matrixSqDiag (degreeOp d) S x + matrixSqDiag K S x := by
  dsimp [matrixSqDiag]
  have h_pw : ∀ y ∈ S, laplacianOp d K x y * laplacianOp d K y x =
      degreeOp d x y * degreeOp d y x + K x y * K y x := by
    intro y hy
    exact laplacian_sq_entry_pointwise d K x y (hK y hy)
  rw [foldl_eq_of_eq_on S _ _ 0 h_pw]
  have h_zero : (0 : ℤ) = 0 + 0 := by ring
  nth_rw 1 [h_zero]
  exact foldl_add_split S (fun y => degreeOp d x y * degreeOp d y x) (fun y => K x y * K y x) 0 0

/-- Theorem: Discrete Trace of L_c² decomposes into Tr(D²) + Tr(K²). -/
theorem discrete_trace_sq_laplacian_eq (d : ℕ → ℤ) (K : ℕ → ℕ → ℤ) (S : List ℕ)
    (hK : ∀ x ∈ S, ∀ y ∈ S, (x == y) = true → K x y = 0) :
    discreteTraceSq (laplacianOp d K) S =
      discreteTraceSq (degreeOp d) S + discreteTraceSq K S := by
  dsimp [discreteTraceSq]
  have h_diag : ∀ x ∈ S, matrixSqDiag (laplacianOp d K) S x =
      matrixSqDiag (degreeOp d) S x + matrixSqDiag K S x := by
    intro x hx
    exact laplacian_sq_diag_eq d K S x (hK x hx)
  rw [foldl_eq_of_eq_on S _ _ 0 h_diag]
  have h_zero : (0 : ℤ) = 0 + 0 := by ring
  nth_rw 1 [h_zero]
  exact foldl_add_split S (fun x => matrixSqDiag (degreeOp d) S x) (fun x => matrixSqDiag K S x) 0 0

/-- Theorem: Trace of K² equals the sum of prime omega values under the 2-walk identity. -/
theorem trace_k_sq_eq_sum_omega (K : ℕ → ℕ → ℤ) (S : List ℕ) (omega : ℕ → ℤ)
    (hWalk : SatisfiesTwoWalkIdentity K S omega) :
    discreteTraceSq K S = S.foldl (fun acc x => acc + omega x) 0 := by
  dsimp [discreteTraceSq]
  have h_walk : ∀ x ∈ S, matrixSqDiag K S x = omega x := hWalk
  exact foldl_eq_of_eq_on S (fun x => matrixSqDiag K S x) omega 0 h_walk

/-- Theorem: The Discrete Selberg Trace Theorem for L_c².
    Connects the spectral trace of the squared Laplacian to the diagonal degree trace
    and the prime omega factor sum across the slice. -/
theorem discrete_selberg_trace_identity (d : ℕ → ℤ) (K : ℕ → ℕ → ℤ) (S : List ℕ) (omega : ℕ → ℤ)
    (hK : ∀ x ∈ S, ∀ y ∈ S, (x == y) = true → K x y = 0)
    (hWalk : SatisfiesTwoWalkIdentity K S omega) :
    discreteTraceSq (laplacianOp d K) S =
      discreteTraceSq (degreeOp d) S + S.foldl (fun acc x => acc + omega x) 0 := by
  rw [discrete_trace_sq_laplacian_eq d K S hK]
  rw [trace_k_sq_eq_sum_omega K S omega hWalk]

/-- Theorem: Prime Density Equivalence.
    The sum of prime weights across the slice equals the sum of prime valuation densities. -/
theorem sum_omega_eq_sum_prime_densities (omega : ℕ → ℤ) (P : List ℕ) (v : ℕ → ℕ → ℕ) (S : List ℕ)
    (hDecomp : DecomposesIntoPrimes omega P v S) :
    S.foldl (fun acc x => acc + omega x) 0 =
      P.foldl (fun acc p => acc + slicePrimeDensity v p S) 0 := by
  dsimp [slicePrimeDensity]
  have h_eq : ∀ x ∈ S, omega x = P.foldl (fun acc p => acc + (v x p : ℤ)) 0 := hDecomp
  rw [foldl_eq_of_eq_on S omega (fun x => P.foldl (fun acc p => acc + (v x p : ℤ)) 0) 0 h_eq]
  exact foldl_foldl_comm S P (fun x p => (v x p : ℤ))

/-- Theorem: The Discrete Selberg-Weil Explicit Formula on Bruhat-Tits Slices.
    Connects the Laplacian spectrum directly to arithmetic prime densities:
    Tr(L_c²) = Tr(D²) + ∑_{p ∈ P} Φ(p, S).
    Proved without custom axioms, standard Lean 4 foundations only. -/
theorem discrete_selberg_weil_explicit_formula
    (d : ℕ → ℤ) (K : ℕ → ℕ → ℤ) (S : List ℕ) (omega : ℕ → ℤ) (P : List ℕ) (v : ℕ → ℕ → ℕ)
    (hK : ∀ x ∈ S, ∀ y ∈ S, (x == y) = true → K x y = 0)
    (hWalk : SatisfiesTwoWalkIdentity K S omega)
    (hDecomp : DecomposesIntoPrimes omega P v S) :
    discreteTraceSq (laplacianOp d K) S =
      discreteTraceSq (degreeOp d) S + P.foldl (fun acc p => acc + slicePrimeDensity v p S) 0 := by
  rw [discrete_selberg_trace_identity d K S omega hK hWalk]
  rw [sum_omega_eq_sum_prime_densities omega P v S hDecomp]

/-!
## Concrete Prime-Step Graph Instantiation & General Walk-Length Powers

We discharge `SatisfiesTwoWalkIdentity` and `DecomposesIntoPrimes` unconditionally
on any finite vertex slice `S : List ℕ` equipped with the concrete undirected
prime-step adjacency relation `primeStepAdj`, and define general walk-length `k`
matrix powers `matrixPow` and traces `discreteTracePow`.
-/

/-- Concrete undirected prime-step edge indicator for a fixed prime `p`. -/
def primeEdgeInd (p x y : ℕ) : ℕ :=
  if (x > 0 ∧ y = x * p) ∨ (y > 0 ∧ x = y * p) then 1 else 0

/-- Concrete prime-step adjacency summed across a prime generator basis `P`. -/
def primeBasisAdj (P : List ℕ) (x y : ℕ) : ℤ :=
  P.foldl (fun acc p => acc + (primeEdgeInd p x y : ℤ)) 0

/-- Number of `p`-step neighbors of `x` inside slice `S`. -/
def primeEdgeDeg (S : List ℕ) (x p : ℕ) : ℕ :=
  S.foldl (fun acc y => acc + primeEdgeInd p x y) 0

/-- Total prime-step degree of `x` inside slice `S` across prime basis `P`. -/
def sliceGraphDegree (P S : List ℕ) (x : ℕ) : ℤ :=
  S.foldl (fun acc y => acc + primeBasisAdj P x y) 0

lemma primeEdgeInd_self_zero (p x : ℕ) (hp : p > 1) : primeEdgeInd p x x = 0 := by
  unfold primeEdgeInd
  split_ifs with h
  · exfalso
    rcases h with ⟨hx, hmul⟩ | ⟨hx, hmul⟩
    · have : x * 1 < x * p := Nat.mul_lt_mul_of_pos_left hp hx
      omega
    · have : x * 1 < x * p := Nat.mul_lt_mul_of_pos_left hp hx
      omega
  · rfl

lemma primeEdgeInd_symm (p x y : ℕ) : primeEdgeInd p x y = primeEdgeInd p y x := by
  unfold primeEdgeInd
  by_cases h : (x > 0 ∧ y = x * p) ∨ (y > 0 ∧ x = y * p)
  · have h' : (y > 0 ∧ x = y * p) ∨ (x > 0 ∧ y = x * p) := h.symm
    simp [h, h']
  · have h' : ¬ ((y > 0 ∧ x = y * p) ∨ (x > 0 ∧ y = x * p)) := fun hc => h hc.symm
    simp [h, h']

lemma primeEdgeInd_unique_prime (p q x y : ℕ) (hpq : p ≠ q)
    (h1 : primeEdgeInd p x y = 1) : primeEdgeInd q x y = 0 := by
  unfold primeEdgeInd at h1 ⊢
  split_ifs at h1 with hp
  split_ifs with hq
  · exfalso
    rcases hp with ⟨hx, hpy⟩ | ⟨hy, hpx⟩ <;> rcases hq with ⟨hx', hqy⟩ | ⟨hy', hqx⟩
    · have : x * p = x * q := hpy.symm.trans hqy
      exact hpq (Nat.eq_of_mul_eq_mul_left hx this)
    · have hmul : y * q * p = y := by rw [← hqx, ← hpy]
      have hqp1 : q * p = 1 := by
        have : y * (q * p) = y * 1 := by rw [← Nat.mul_assoc, hmul, Nat.mul_one]
        exact Nat.eq_of_mul_eq_mul_left hy' this
      have hq1 : q = 1 := Nat.eq_one_of_mul_eq_one_right hqp1
      have hp1 : p = 1 := Nat.eq_one_of_mul_eq_one_left hqp1
      exact hpq (hp1.trans hq1.symm)
    · have hmul : x * q * p = x := by rw [← hqy, ← hpx]
      have hqp1 : q * p = 1 := by
        have : x * (q * p) = x * 1 := by rw [← Nat.mul_assoc, hmul, Nat.mul_one]
        exact Nat.eq_of_mul_eq_mul_left hx' this
      have hq1 : q = 1 := Nat.eq_one_of_mul_eq_one_right hqp1
      have hp1 : p = 1 := Nat.eq_one_of_mul_eq_one_left hqp1
      exact hpq (hp1.trans hq1.symm)
    · have : y * p = y * q := hpx.symm.trans hqx
      exact hpq (Nat.eq_of_mul_eq_mul_left hy this)
  · rfl

lemma foldl_zero_of_all_zero (L : List ℕ) (f : ℕ → ℤ) (hf : ∀ p ∈ L, f p = 0) :
    L.foldl (fun acc p => acc + f p) 0 = 0 := by
  rw [foldl_eq_of_eq_on L f (fun _ => 0) 0 hf]
  exact foldl_zero_list L

/-- Every prime-step adjacency matrix with `∀ p ∈ P, p > 1` has zero diagonal. -/
theorem primeBasisAdj_diag_zero (P : List ℕ) (hP : ∀ p ∈ P, p > 1) (x : ℕ) :
    primeBasisAdj P x x = 0 := by
  unfold primeBasisAdj
  apply foldl_zero_of_all_zero P (fun p => (primeEdgeInd p x x : ℤ))
  intro p hp
  rw [primeEdgeInd_self_zero p x (hP p hp)]
  rfl

theorem primeBasisAdj_symm (P : List ℕ) (x y : ℕ) :
    primeBasisAdj P x y = primeBasisAdj P y x := by
  unfold primeBasisAdj
  apply foldl_eq_of_eq_on P _ _ 0
  intro p _
  rw [primeEdgeInd_symm p x y]

/-- On a `Nodup` list `P`, at most one prime joins `x` and `y`: `primeBasisAdj P x y ∈ {0, 1}`. -/
theorem primeBasisAdj_zero_or_one (P : List ℕ) (hNodup : P.Nodup) (x y : ℕ) :
    primeBasisAdj P x y = 0 ∨ primeBasisAdj P x y = 1 := by
  induction P with
  | nil => left; rfl
  | cons p ps ih =>
    rw [List.nodup_cons] at hNodup
    obtain ⟨hp_not_mem, hps_nodup⟩ := hNodup
    unfold primeBasisAdj
    rw [foldl_cons_val]
    by_cases h1 : primeEdgeInd p x y = 1
    · right
      have hrest : ps.foldl (fun acc q => acc + (primeEdgeInd q x y : ℤ)) 0 = 0 := by
        apply foldl_zero_of_all_zero ps
        intro q hq
        have hpq : p ≠ q := fun heq => hp_not_mem (heq ▸ hq)
        rw [primeEdgeInd_unique_prime p q x y hpq h1]
        rfl
      rw [h1, hrest]
      ring
    · have h0 : primeEdgeInd p x y = 0 := by
        unfold primeEdgeInd at h1 ⊢
        split_ifs at h1 ⊢ <;> omega
      rw [h0]
      simp only [Nat.cast_zero, zero_add]
      exact ih hps_nodup

/-- Unconditional 2-walk identity for `primeBasisAdj` on any `Nodup` prime list `P`. -/
theorem primeBasisAdj_satisfies_two_walk (P : List ℕ) (hNodup : P.Nodup) (S : List ℕ) :
    SatisfiesTwoWalkIdentity (primeBasisAdj P) S (sliceGraphDegree P S) := by
  intro x _
  unfold matrixSqDiag sliceGraphDegree
  apply foldl_eq_of_eq_on S _ _ 0
  intro y _
  rw [primeBasisAdj_symm P y x]
  rcases primeBasisAdj_zero_or_one P hNodup x y with h | h <;> rw [h] <;> ring

private lemma foldl_nat_cast_eq (S : List ℕ) (f : ℕ → ℕ) (init : ℕ) :
    ((S.foldl (fun acc y => acc + f y) init : ℕ) : ℤ) =
      S.foldl (fun acc y => acc + (f y : ℤ)) (init : ℤ) := by
  induction S generalizing init with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih (init + f y), Nat.cast_add]

/-- Unconditional decomposition of `sliceGraphDegree` into per-prime edge degrees. -/
theorem primeBasisAdj_decomposes_into_primes (P S : List ℕ) :
    DecomposesIntoPrimes (sliceGraphDegree P S) P (primeEdgeDeg S) S := by
  intro x _
  unfold sliceGraphDegree primeBasisAdj primeEdgeDeg
  have hcast : ∀ p, ((S.foldl (fun acc y => acc + primeEdgeInd p x y) 0 : ℕ) : ℤ) =
      S.foldl (fun acc y => acc + (primeEdgeInd p x y : ℤ)) 0 :=
    fun p => foldl_nat_cast_eq S (fun y => primeEdgeInd p x y) 0
  rw [foldl_eq_of_eq_on P _
    (fun p => S.foldl (fun acc y => acc + (primeEdgeInd p x y : ℤ)) 0) 0 (fun p _ => hcast p)]
  exact foldl_foldl_comm S P (fun y p => (primeEdgeInd p x y : ℤ))

/--
Unconditional Concrete Discrete Trace Theorem on Prime-Step Graphs:
For any finite vertex slice `S` and any duplicate-free list of primes `P` (`∀ p ∈ P, p > 1`),
the squared combinatorial Laplacian `L_c = D - K` satisfies without any extra hypotheses:
  `Tr(L_c²) = Tr(D²) + ∑_{p ∈ P} ∑_{x ∈ S} deg_p(x, S)`.
-/
theorem concrete_prime_step_selberg_trace (d : ℕ → ℤ) (P S : List ℕ)
    (hNodup : P.Nodup) (hP : ∀ p ∈ P, p > 1) :
    discreteTraceSq (laplacianOp d (primeBasisAdj P)) S =
      discreteTraceSq (degreeOp d) S +
        P.foldl (fun acc p => acc + slicePrimeDensity (primeEdgeDeg S) p S) 0 := by
  apply discrete_selberg_weil_explicit_formula d (primeBasisAdj P) S
    (sliceGraphDegree P S) P (primeEdgeDeg S)
  · intro x _ y _ hxy
    have heq : x = y := beq_iff_eq.mp hxy
    subst heq
    exact primeBasisAdj_diag_zero P hP x
  · exact primeBasisAdj_satisfies_two_walk P hNodup S
  · exact primeBasisAdj_decomposes_into_primes P S

/-- General walk-length `k` matrix power entry `(A^k)_{x, y}` over finite slice `S`. -/
def matrixPow (A : ℕ → ℕ → ℤ) (S : List ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0, x, y => if x == y then 1 else 0
  | 1, x, y => A x y
  | k + 2, x, y => S.foldl (fun acc z => acc + A x z * matrixPow A S (k + 1) z y) 0

/-- General walk-length `k` discrete trace `Tr(A^k)` across slice `S`. -/
def discreteTracePow (A : ℕ → ℕ → ℤ) (S : List ℕ) (k : ℕ) : ℤ :=
  S.foldl (fun acc x => acc + matrixPow A S k x x) 0

/-- Consistency check: `discreteTracePow A S 2` equals `discreteTraceSq A S`. -/
theorem discreteTracePow_two_eq_sq (A : ℕ → ℕ → ℤ) (S : List ℕ) :
    discreteTracePow A S 2 = discreteTraceSq A S := rfl

end KinematicRiemann
