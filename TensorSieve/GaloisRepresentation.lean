import TensorSieve.KreinSpace

/-!
# Galois Representations and Indefinite Metrics

This module refactors the expected Galois representations from the formal arithmetic library,
stripping them of their standard positive-definite norms.

Instead, we apply the `MajorantTopology` and `IndefiniteMetric` mixins from our
`KreinSpace` architecture to natively absorb the negative trace evaluations of global fields.

## Shadow Evaluators

To bridge the noncomputable mathematics intrinsic to these representations with
our discrete combinatorial search, we implement "Shadow Evaluators".
-/

namespace KinematicRiemann

open LinearMap

/--
A refactored Galois representation over an indefinite Krein space.
This replaces the classical assumption of a positive-definite `InnerProductSpace`
with our `MajorantTopology` and `IndefiniteMetric` architecture.
-/
structure GaloisRepresentation (K : Type*) [Field K] (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] [HasJOperator 𝕜 E] where
  -- The representation acts on an indefinite Krein space
  action : K → (E →ₗ[𝕜] E)
  -- The representation preserves the indefinite metric via J-self-adjointness
  preserves_indefinite : ∀ k, IsJAdjoint (action k)

end KinematicRiemann
