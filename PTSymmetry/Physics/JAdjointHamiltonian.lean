import PTSymmetry.MathlibCore.KreinSpace
import PTSymmetry.Physics.MajorantTopology

/-!
# J-Adjoint Operators and Projectors

This module defines $J$-self-adjoint operators, which represent valid physical
observables (Hamiltonians) in PT-Symmetric Quantum Mechanics despite being
non-Hermitian in the standard sense. It also provides the positive and negative
cone projection operators.
-/

namespace PTSymmetry

open LinearMap
open Mathlib.Analysis.InnerProductSpace.Krein

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [UniformSpace E]
  [KreinSpace 𝕜 E] [HasJOperator 𝕜 E]

/--
Defines a linear operator `A` as $J$-self-adjoint natively within the Krein Space.
This permits an operator to be formally symmetric with respect to the indefinite
metric ($[Ax, y] = [x, Ay]$) even while breaking standard Hilbert adjoint rules.
For a PT-symmetric Hamiltonian, this implies the spectrum is real.
-/
class IsJAdjoint (A : E →ₗ[𝕜] E) : Prop where
  j_adjoint : ∀ x y : E,
    (KreinSpace.metric (R := 𝕜) (V := E)).bilin (A x) y =
      (KreinSpace.metric (R := 𝕜) (V := E)).bilin x (A y)

variable [Invertible (2 : 𝕜)] [MajorantPositiveDefinite 𝕜 E]

/--
The orthogonal projection operator onto the strictly positive-definite $V^+$ subspace.
Computed dynamically via the symmetric mean $P^+ = \frac{1}{2}(I + J)$.
-/
noncomputable def P_plus : (MajorantTopology E) →L[𝕜] (MajorantTopology E) :=
  (⅟(2 : 𝕜)) • (ContinuousLinearMap.id 𝕜 (MajorantTopology E) +
    continuousJ.toContinuousLinearMap)

/--
The orthogonal projection operator onto the strictly negative-definite $V^-$ subspace.
Computed dynamically via the symmetric mean $P^- = \frac{1}{2}(I - J)$.
-/
noncomputable def P_minus : (MajorantTopology E) →L[𝕜] (MajorantTopology E) :=
  (⅟(2 : 𝕜)) • (ContinuousLinearMap.id 𝕜 (MajorantTopology E) -
    continuousJ.toContinuousLinearMap)

/--
A structural proof that the orthogonal projection operators properly decompose the
Majorant topology, resolving back into the continuous identity map ($P^+ + P^- = I$).
-/
theorem P_plus_add_P_minus : P_plus (𝕜 := 𝕜) (E := E) + P_minus (𝕜 := 𝕜) (E := E) =
    ContinuousLinearMap.id 𝕜 (MajorantTopology E) := by
  -- Expand the definitions of the projection operators P^+ and P^-
  dsimp [P_plus, P_minus]
  -- Distribute the scalar multiplication ⅟2 across the addition and subtraction terms.
  rw [smul_add, smul_sub]
  -- Rearrange the terms using the abelian group properties of continuous linear maps
  -- so that the continuous J-operator terms cancel each other out.
  have h1 :
    (⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) :
      (MajorantTopology E) →L[𝕜] (MajorantTopology E)) +
    (⅟(2 : 𝕜) • continuousJ.toContinuousLinearMap :
      (MajorantTopology E) →L[𝕜] (MajorantTopology E)) +
    ((⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) :
      (MajorantTopology E) →L[𝕜] (MajorantTopology E)) -
    (⅟(2 : 𝕜) • continuousJ.toContinuousLinearMap :
      (MajorantTopology E) →L[𝕜] (MajorantTopology E))) =
    (⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) :
      (MajorantTopology E) →L[𝕜] (MajorantTopology E)) +
    (⅟(2 : 𝕜) • ContinuousLinearMap.id 𝕜 (MajorantTopology E) :
      (MajorantTopology E) →L[𝕜] (MajorantTopology E)) := by
    abel
  -- Apply this simplified form containing only the identity maps.
  rw [h1]
  -- Factor out the continuous identity map to sum the scalar coefficients.
  rw [← add_smul]
  -- Prove that the sum of the scalar coefficients (1/2 + 1/2) equals 1.
  have h2 : ⅟(2 : 𝕜) + ⅟(2 : 𝕜) = 1 := by
    calc
      ⅟(2 : 𝕜) + ⅟(2 : 𝕜) = (1 : 𝕜) * ⅟(2 : 𝕜) + (1 : 𝕜) * ⅟(2 : 𝕜) := by simp
      _ = (1 + 1 : 𝕜) * ⅟(2 : 𝕜) := by rw [add_mul]
      _ = (2 : 𝕜) * ⅟(2 : 𝕜) := by norm_num
      _ = 1 := mul_invOf_self 2
  -- Substitute the scalar 1 back in, completing the proof that P^+ + P^- = I.
  rw [h2, one_smul]

end PTSymmetry
