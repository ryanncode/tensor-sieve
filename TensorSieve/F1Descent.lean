import Mathlib.Algebra.Ring.Basic
import TensorSieve.LambdaRing
import TensorSieve.Distribution

/-!
# $\Lambda$-Ring Multiplicativity and Roots-of-Unity Actions

This module records algebraic properties of Adams operations on $\Lambda$-rings
and discrete roots-of-unity actions on totally disconnected spaces.
-/

namespace KinematicRiemann

/--
A discrete roots-of-unity action on a totally disconnected space `K`.
-/
structure RootsOfUnityAction (K : Type*) [BruhatTitsSpace K] where
  /-- The degree of the roots of unity. -/
  degree : ℕ
  /-- Positivity of the degree. -/
  preserves_topology : degree > 0

/--
Adams operations preserve multiplication because each `psi p` is a ring homomorphism.
-/
theorem adams_multiplicative {R : Type*} [CommRing R] [LambdaRing R]
    (p : ℕ) [Fact p.Prime] (x y : R) :
    LambdaRing.psi p (x * y) = LambdaRing.psi p x * LambdaRing.psi p y :=
  map_mul (LambdaRing.psi p) x y

/--
Adams operations preserve addition as well as multiplication.
-/
theorem adams_additive {R : Type*} [CommRing R] [LambdaRing R]
    (p : ℕ) [Fact p.Prime] (x y : R) :
    LambdaRing.psi p (x + y) = LambdaRing.psi p x + LambdaRing.psi p y :=
  map_add (LambdaRing.psi p) x y

end KinematicRiemann
