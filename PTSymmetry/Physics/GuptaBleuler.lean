import PTSymmetry.MathlibCore.KreinSpace
import Mathlib.Analysis.RCLike.Basic

/-!
# Gupta-Bleuler Quantization

This module demonstrates a second fundamental physics application of Krein Spaces:
the Gupta-Bleuler formalism for the covariant quantization of the electromagnetic field (QED).

To maintain explicit Lorentz covariance, the photon state space is constructed
as a Krein Space containing unphysical negative-norm states (timelike photons).
Physical observable states are isolated by enforcing the Lorenz gauge condition,
which defines a positive semi-definite subspace. The true Hilbert space is
then recovered by factoring out the zero-norm longitudinal photons.
-/

namespace PTSymmetry.GuptaBleuler

open Mathlib.Analysis.InnerProductSpace.Krein
open LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [KreinSpace 𝕜 V]

/--
The physical state space $V_{phys}$.
In QED, this corresponds to states satisfying the Lorenz gauge condition.
Mathematically, it is a positive semi-definite subspace of the Krein Space.
-/
class PhysicalSubspace (V_phys : Submodule 𝕜 V) : Prop where
  semi_definite : ∀ x ∈ V_phys, 0 ≤ RCLike.re ((KreinSpace.metric (R := 𝕜) (V := V)).bilin x x)

/--
The null subspace $V_{null}$ (representing unobservable longitudinal photons).
It is defined as the intersection of the physical subspace with its own
indefinite orthogonal complement.
-/
def nullSubspace (V_phys : Submodule 𝕜 V) : Submodule 𝕜 V :=
  V_phys ⊓ indefOrthogonal V_phys

/--
By definition, any state in the null subspace is orthogonal to all physical states.
This guarantees that longitudinal photons have zero transition amplitude with
any observable physical state.
-/
theorem null_orthogonal_phys (V_phys : Submodule 𝕜 V) (n p : V)
    (hn : n ∈ nullSubspace V_phys) (hp : p ∈ V_phys) :
    (KreinSpace.metric (R := 𝕜) (V := V)).bilin n p = 0 := by
  -- `hn` implies `n` is in both `V_phys` and `indefOrthogonal V_phys`
  have h_ortho : n ∈ indefOrthogonal V_phys := hn.2
  -- By definition of `indefOrthogonal`, `n` is orthogonal to all `p ∈ V_phys`
  exact h_ortho p hp

/--
The true observable Hilbert Space of QED.
Constructed by taking the physical state space and quotienting out the
unobservable null subspace ($V_{phys} / V_{null}$).
-/
def ObservableHilbertSpace (V_phys : Submodule 𝕜 V) :=
  V_phys ⧸ (nullSubspace V_phys).comap V_phys.subtype

end PTSymmetry.GuptaBleuler
