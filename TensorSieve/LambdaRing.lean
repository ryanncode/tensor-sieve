import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Lambda Rings and Combinatorial Firewalls

This module formalizes Borger's Frobenius-lift characterization of $\Lambda$-rings
via commuting ring endomorphisms (Adams operations $\psi_p$) and instantiates the
canonical $\Lambda$-ring structure on $\mathbb{Z}$ via Fermat's Little Theorem.
-/

namespace KinematicRiemann

/--
A Lambda-structure on a commutative ring `R`, given by a commuting family of
ring endomorphisms `psi p` indexed by primes `p` satisfying the Frobenius lift
congruence `psi p x ≡ x^p (mod pR)`.
-/
class LambdaRing (R : Type*) [CommRing R] where
  /-- Adams operations: ring endomorphisms indexed by primes. -/
  psi (p : ℕ) [Fact p.Prime] : R →+* R

  /-- The family of Adams operations commutes. -/
  psi_comm (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (x : R) :
    psi p (psi q x) = psi q (psi p x)

  /-- Frobenius lift property: `psi p x = x^p + p * k` for some `k : R`. -/
  frobenius_lift (p : ℕ) [Fact p.Prime] (x : R) :
    ∃ (k : R), psi p x = x ^ p + (p : R) * k

/--
The canonical $\Lambda$-ring structure on $\mathbb{Z}$, with identity Adams operations.
The Frobenius lift property holds unconditionally by Fermat's Little Theorem.
-/
instance : LambdaRing ℤ where
  psi _ _ := RingHom.id ℤ
  psi_comm _ _ _ _ _ := rfl
  frobenius_lift p _ x := by
    have hmod : ((x - x ^ p : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.pow_card]
      exact sub_self _
    have hdvd : (p : ℤ) ∣ (x - x ^ p) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x - x ^ p) p).mp hmod
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by dsimp; linarith⟩

/--
Diagnostic filter checking whether an element `x` is fixed by the Adams operation `psi p`.
-/
def adamsFilter {R : Type*} [CommRing R] [LambdaRing R] [DecidableEq R]
    (p : ℕ) [Fact p.Prime] (x : R) : R :=
  if LambdaRing.psi p x == x then x else 0

theorem adamsFilter_int (p : ℕ) [Fact p.Prime] (x : ℤ) : adamsFilter p x = x := by
  simp [adamsFilter, LambdaRing.psi]

end KinematicRiemann
