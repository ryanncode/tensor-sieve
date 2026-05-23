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
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [UniformSpace V] [KreinSpace 𝕜 V]

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

/--
The induced inner product on the quotient space is well-defined because
shifting by a null state does not change the metric evaluation for physical states.
-/
theorem quotient_metric_well_defined (V_phys : Submodule 𝕜 V)
    (a₁ a₂ b₁ b₂ : V_phys)
    (ha : (a₁ - a₂ : V_phys).val ∈ nullSubspace V_phys)
    (hb : (b₁ - b₂ : V_phys).val ∈ nullSubspace V_phys) :
    (KreinSpace.metric (R := 𝕜) (V := V)).bilin (a₁ : V) (b₁ : V) =
    (KreinSpace.metric (R := 𝕜) (V := V)).bilin (a₂ : V) (b₂ : V) := by
  let M := KreinSpace.metric (R := 𝕜) (V := V)
  -- Algebraically decompose the equivalence class representatives a₁ and b₁
  -- into their base vectors (a₂, b₂) and their null differentials (a₁ - a₂, b₁ - b₂).
  have h_a : (a₁ : V) = (a₂ : V) + (a₁ - a₂ : V_phys).val := by
    push_cast
    abel
  have h_b : (b₁ : V) = (b₂ : V) + (b₁ - b₂ : V_phys).val := by
    push_cast
    abel
  -- Substitute these algebraic decompositions into the bilinear form.
  rw [h_a, h_b]
  -- Expand the bilinear form using its linearity properties across addition.
  -- This produces four separate cross-terms.
  rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add]
  -- Evaluate the cross-terms. Any term containing a null differential evaluates to zero
  -- because null states are orthogonal to all physical states (including themselves).
  have h1 : M.bilin (a₂ : V) (b₁ - b₂ : V_phys).val = 0 := by
    rw [M.symm.eq]
    exact hb.2 (a₂ : V) a₂.property
  have h2 : M.bilin (a₁ - a₂ : V_phys).val (b₂ : V) = 0 :=
    ha.2 (b₂ : V) b₂.property
  have h3 : M.bilin (a₁ - a₂ : V_phys).val (b₁ - b₂ : V_phys).val = 0 :=
    ha.2 (b₁ - b₂ : V_phys).val (b₁ - b₂).property
  -- Substitute the zeroed cross-terms back into the expanded equation.
  rw [h1, h2, h3]
  -- Simplify the remaining expression to show the metric evaluation is isolated
  -- to solely base vectors a₂ and b₂, proving the metric is well-defined over the quotient space.
  simp

end PTSymmetry.GuptaBleuler
