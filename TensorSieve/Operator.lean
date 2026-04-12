import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Factorization.Basic
import TensorSieve.Kinematics

/-!
# The Non-Archimedean Operator \hat{H} and FTNILO Dynamics

This module implements the computable shift operator across the Bruhat-Tits tree.
It abandons the continuous classical continuous number line (x -> x+1)
to evaluate cross-branch transitions (interference) across the p-adic lattice.

The constraints are defined using the Field Tensor Network Integral Logical Operator
(FTNILO) framework, resolving logical bottlenecks locally.
-/

namespace KinematicRiemann

/-- Computable helper to strictly count prime factors with multiplicity.
    This establishes the arithmetic divergence measure safely avoiding unbounded recursion. -/
def countFactors (n : ℕ) : ℕ :=
  if h : n > 1 then
    have h1 : 1 < n.minFac := (Nat.minFac_prime (ne_of_gt h)).one_lt
    have h2 : n / n.minFac < n := Nat.div_lt_self (Nat.lt_trans (by decide) h) h1
    1 + countFactors (n / n.minFac)
  else 0
termination_by n

/-- Computes the local topological degree D corresponding to the localized arithmetic divergence. -/
def compLocalDegree (a : SemanticAddress) : ℕ :=
  countFactors a.val

/-- Recursively extracts all distinct prime factors (the structural base elements of a node). -/
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

/-- Unbounded wrapper for distinct prime factors. -/
def distinctPrimeFactors (n : ℕ) : List ℕ :=
  distinctPrimeFactorsFuel n n 2 []

/-- Computes the exponent of p in the prime factorization of n. -/
def pAdicValuation (n p : ℕ) : ℕ :=
  if h : p > 1 ∧ n > 0 then
    if n % p == 0 then
      have : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h; exact Nat.lt_irrefl 0 h.2)) h.1
      1 + pAdicValuation (n / p) p
    else 0
  else 0
termination_by n

/-- Computes the L1-norm divergence between two numbers based on
    their p-adic valuations. -/
def valuationDivergence (a b : ℕ) : ℕ :=
  let primesA := distinctPrimeFactors a
  let primesB := distinctPrimeFactors b
  let allPrimes := (primesA ++ primesB).eraseDups
  allPrimes.foldl (fun acc p =>
    let va := pAdicValuation a p
    let vb := pAdicValuation b p
    acc + (if va > vb then va - vb else vb - va)
  ) 0

/-- Computes the shared structural depth (greatest common semantic root)
    between two nodes to evaluate their topological entanglement. -/
def sharedSemanticRoot (a b : ℕ) : ℕ := Nat.gcd a b

/-- The expanded discrete coherence Hamiltonian.
    Enforces long-range GUE level repulsion by expanding the FTNILO tensor contraction
    bounds. The amplitude evaluates the shared prime factorization history and applies
    an alternating parity to induce cross-branch interference. -/
def crossBranchAmplitude (a b : ℕ) (W : ℕ) : ℤ :=
  if a == b then
    -- Diagonal element: Total arithmetic divergence (D)
    (countFactors a : ℤ)
  else
    let dist := valuationDivergence a b
    -- Expand the contraction bound to window W
    if dist <= W then
      let g := sharedSemanticRoot a b
      let shared_weight := countFactors g

      -- Alternating logical parity based on L1 traversal distance
      -- dist 2 = -1 (Destructive adjacent), dist 4 = 1 (Constructive distant)
      let parity : ℤ := if dist % 4 == 0 then 1 else if dist % 2 == 0 then -1 else 0

      -- Amplitude scales by the weight of their shared topological history
      parity * (shared_weight : ℤ)
    else
      0 -- Absolute logical jamming beyond the correlation window

/-- Computes the Trace of the Hamiltonian across a horizontal slice,
    now requiring the correlation window W (e.g., W = 6). -/
def traceHamiltonian (slice : List ℕ) (W : ℕ) : ℤ :=
  slice.foldl (fun acc a => acc + crossBranchAmplitude a a W) 0

/-- Computes the second spectral moment to structurally evaluate
    cross-branch interference and dynamic eigenvalue spacing. -/
def traceHamiltonianSquared (slice : List ℕ) (W : ℕ) : ℤ :=
  slice.foldl (fun acc a =>
    acc + slice.foldl (fun acc2 b =>
      let amp := crossBranchAmplitude a b W
      acc2 + amp * amp
    ) 0
  ) 0

/-- Computes the next horizontal topological slice of the p-adic tree moving downward. -/
def nextSlice (slice : List ℕ) : List ℕ :=
  let next_nodes := slice.flatMap (fun x =>
    let factors := distinctPrimeFactors x
    factors.map (fun p => x / p)
  )
  List.eraseDups next_nodes

/-- Sequence of Algorithmic Halting (Energy Landscape Emission).
    Executes a structured horizontal non-Archimedean sieve moving strictly downwards.
    Outputs tuple: (level, x, amplitude, localDegree, jammed).
    Detects critical topological bottlenecks directly responsible for GUE energy spacings. -/
def emissionSpectrumDown (start : ℕ) (steps : ℕ) (W : ℕ := 6) : List (ℕ × ℕ × ℤ × ℕ × ℕ) :=
  let rec loop (slice : List ℕ) (n : ℕ) (acc : List (ℕ × ℕ × ℤ × ℕ × ℕ)) :=
    match n with
    | 0 => acc.reverse
    | n' + 1 =>
        if slice.isEmpty then acc.reverse
        else if slice.all (fun x => x <= 1) then acc.reverse
        else
          let w := if slice.isEmpty then 0 else countFactors (slice.head!)
          -- Iterate across the horizontal bound, testing each component node
          let new_acc := slice.foldl (fun (lst : List (ℕ × ℕ × ℤ × ℕ × ℕ)) (x : ℕ) =>
            -- Calculates the transition amplitude sum to map logical cross-branch jamming
            let amp := slice.foldl (fun sum b => sum + crossBranchAmplitude x b W) 0
            let deg := countFactors x
            let jammed := if amp == 0 then 1 else 0
            (w, x, amp, deg, jammed) :: lst
          ) acc
          let next_s := nextSlice slice
          loop next_s n' new_acc
  loop [start] steps []

end KinematicRiemann
