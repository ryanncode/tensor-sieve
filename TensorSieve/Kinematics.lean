import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Basic

/-!
# Non-Archimedean Kinematics and the Grammar-First Space

This module constructs the formal environment required for the "Formal Rupture."
It rejects the continuous analytic baseline (the "Archimedean Trap") in favor of
an absolute discrete topological lattice (the Bruhat-Tits tree) governed
exclusively by unique prime factorization constraints.
-/

namespace KinematicRiemann

open Finset
open Classical

/--
A `SemanticAddress` provides the static, absolute structural reality of an integer.
Instead of magnitudes passing toward infinity, it represents the exact historical
record of prime tile generation via the successor function $S(x) = x \cup \{x\}$.
The requirement `0 < val` ensures zero (the empty set base token) acts properly.
-/
structure SemanticAddress where
  val : ℕ
  pos : 0 < val

/--
Defines the divisibility metric constraint.
Two semantic addresses are topologically adjacent exclusively if they are separated
by exactly one fundamental prime generator (no additive distance or smearing).
-/
def isPrimeStep (a b : SemanticAddress) : Prop :=
  ∃ p : ℕ, p.Prime ∧ b.val = a.val * p

/--
The categorical Quiver representing the Bruhat-Tits lattice of integers.
Transitions exist purely as valid multi-factor operations, not as points in an interval.
-/
instance : Quiver SemanticAddress where
  Hom a b := PLift (isPrimeStep a b)

/--
The $p$-adic structural length, calculated via the total prime factor multiplicity.
Acts as the foundation for the well-founded relation.
-/
noncomputable def primeWeight (a : SemanticAddress) : ℕ :=
  a.val.factorization.sum (fun _ v => v)

/--
The local degree matrix component ($D$) of the combinatorial Laplacian.
In a "grammar-first" space, arithmetic divergence is strictly computed by
the finite support history of the semantic address.
-/
noncomputable def localDegree (a : SemanticAddress) : ℕ :=
  a.val.factorization.sum (fun _ v => v)

/--
The local adjacency constraint ($K$).
Used to form the discrete combinatorial Laplacian ($L_c = D - K$).
-/
noncomputable def adjacency (a b : SemanticAddress) : ℤ :=
  if isPrimeStep a b ∨ isPrimeStep b a then 1 else 0

/--
The discrete combinatorial Laplacian operator ($L_c$) governing traversal.
Evaluates the graph pointwise using solely local topology (divisibility gating).
-/
noncomputable def combinatorialLaplacian (a b : SemanticAddress) : ℤ :=
  if a.val == b.val then
    (localDegree a : ℤ)
  else
    - (adjacency a b)

/--
The primary well-founded divisibility descent.
A node `a` precedes `b` logically if it acts as a proper divisor, enforcing
the structural reality that mathematical collisions cascade downwards toward 1.
-/
def DivisibilityLT (a b : SemanticAddress) : Prop :=
  a.val ∣ b.val ∧ a.val ≠ b.val

/--
Formal verification that the sieve's descent cannot form infinite chains.
Reduces the non-Archimedean descent to the natural well-foundedness of `ℕ`.
-/
lemma wellFounded_divisibility : WellFounded DivisibilityLT :=
  Subrelation.wf (r := InvImage (· < ·) SemanticAddress.val)
    (fun {a b} (h : DivisibilityLT a b) => Nat.lt_of_le_of_ne (Nat.le_of_dvd b.pos h.1) h.2)
    (InvImage.wf SemanticAddress.val Nat.lt_wfRel.wf)

instance : WellFoundedRelation SemanticAddress where
  rel := DivisibilityLT
  wf := wellFounded_divisibility

/--
The discrete counterpart to the FTNILO amplitude contraction.
Returns a transition constraint `1` if valid within the tensor array, or `0`
if the structural state yields an irreconcilable logical jam.
-/
noncomputable def tensorGate (a b : SemanticAddress) : ℕ :=
  let fa := a.val.factorization
  let fb := b.val.factorization
  let S := fa.support ∪ fb.support
  S.sum (fun p =>
    let delta_k := if fb p == fa p + 1 then 1 else 0
    let prod_j := (S.erase p).prod (fun q => if fb q == fa q then 1 else 0)
    delta_k * prod_j
  )

/--
Extracts the maximal topological neighbor by reversing a single prime generation,
proving positivity structurally through Lean's division theorems.
-/
noncomputable def maximalProperDivisor (a : SemanticAddress) : SemanticAddress :=
  ⟨a.val / a.val.minFac, Nat.div_pos (Nat.minFac_le a.pos) (Nat.minFac_pos a.val)⟩

/--
The computable kinematic sieve acting natively over the $p$-adic graph.
Instead of evaluating continuous intervals, the machine checks strict constraint logic
between semantic nodes, relying entirely on algorithmic halting (jamming).
-/
noncomputable def kinematicSieve (a : SemanticAddress) : ℕ :=
  if h_one : a.val == 1 then
    1 -- Base token reached successfully
  else
    let prev := maximalProperDivisor a
    let amplitude := tensorGate prev a
    if amplitude == 0 then
      0 -- Logical Jamming: Deterministic constraint collision reached
    else
      -- Verify the formal descent to satisfy the termination compiler.
      have _ : DivisibilityLT prev a := by
        dsimp [DivisibilityLT, maximalProperDivisor, prev]
        constructor
        · exact Nat.div_dvd_of_dvd (Nat.minFac_dvd a.val)
        · intro contra
          have h_neq : a.val ≠ 1 := by
            intro eq1
            have : (a.val == 1) = true := beq_iff_eq.mpr eq1
            rw [this] at h_one
            contradiction
          cases Nat.div_eq_self.mp contra with
          | inl h_zero => exact ne_of_gt a.pos h_zero
          | inr h_min_one => exact h_neq (Nat.minFac_eq_one_iff.mp h_min_one)
      kinematicSieve prev
termination_by a

end KinematicRiemann
