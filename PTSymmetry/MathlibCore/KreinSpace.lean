import PTSymmetry.MathlibCore.IndefiniteMetric
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Krein Spaces

This module defines Krein Spaces natively within Mathlib. A Krein Space is a vector
space equipped with an indefinite metric that natively admits a fundamental topological
decomposition into positive-definite and negative-definite sub-spaces.
-/

namespace Mathlib.Analysis.InnerProductSpace.Krein

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [UniformSpace V]

/--
The formal definition of a Krein Space.
A vector space `V` equipped with an indefinite metric that natively admits
a fundamental topological decomposition `V = V^+ \oplus V^-`, where `V^+`
is positive definite and `V^-` is negative definite.
-/
class KreinSpace (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    [UniformSpace V] where
  metric : IndefiniteMetric R V
  V_plus : Submodule R V
  V_minus : Submodule R V
  is_compl : IsCompl V_plus V_minus
  ortho : ∀ x ∈ V_plus, ∀ y ∈ V_minus, metric.bilin x y = 0
  complete : CompleteSpace V

/--
The indefinite geometric orthogonal complement of a given subspace `K`.
Unlike Hilbert space orthogonality, a subspace can be indefinitely orthogonal
to itself (i.e., neutral or isotropic cones).
-/
def indefOrthogonal [KreinSpace R V] (K : Submodule R V) : Submodule R V where
  carrier := { v : V | ∀ u ∈ K, (KreinSpace.metric (R := R) (V := V)).bilin v u = 0 }
  add_mem' h1 h2 u hu := by
    rw [LinearMap.map_add₂]
    rw [h1 u hu, h2 u hu, zero_add]
  zero_mem' u _ := by
    rw [LinearMap.map_zero₂]
  smul_mem' c v hv u hu := by
    rw [LinearMap.map_smul₂, hv u hu, smul_zero]

end Mathlib.Analysis.InnerProductSpace.Krein
