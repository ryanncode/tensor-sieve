import TensorSieve.KreinSpace

/-!
# Krein-Isometric Group Representations (`GaloisRepresentation`)

This module defines a group representation acting on a Krein space by
indefinite-metric isometries: a monoid homomorphism `ρ : G →* (E →ₗ[𝕜] E)`
preserving the indefinite bilinear form `[ρ(g) x, ρ(g) y] = [x, y]`.
-/

namespace KinematicRiemann

open LinearMap

/--
A group representation of `G` on a Krein space `E` preserving the
indefinite bilinear metric `[action g x, action g y] = [x, y]`.
-/
structure GaloisRepresentation (G : Type*) [Group G] (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] where
  /-- Multiplicative group action by `𝕜`-linear endomorphisms of `E`. -/
  action : G →* (E →ₗ[𝕜] E)
  /-- Every group element acts as an isometry of the indefinite Krein bilinear form. -/
  preserves_indefinite : ∀ (g : G) (x y : E),
    (KreinSpace.metric (R := 𝕜) (V := E)).bilin (action g x) (action g y) =
      (KreinSpace.metric (R := 𝕜) (V := E)).bilin x y

/-- The trivial representation sending every `g ∈ G` to `LinearMap.id`. -/
def trivialGaloisRepresentation (G : Type*) [Group G] (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] : GaloisRepresentation G 𝕜 E where
  action := 1
  preserves_indefinite := fun _ _ _ => rfl

/-- Applying `action (g * h)` equals composing `action g` after `action h`. -/
theorem GaloisRepresentation.action_mul_apply {G : Type*} [Group G] {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E]
    (ρ : GaloisRepresentation G 𝕜 E) (g h : G) (x : E) :
    ρ.action (g * h) x = ρ.action g (ρ.action h x) := by
  rw [map_mul]
  rfl

/-- `action 1` acts as the identity on every vector. -/
theorem GaloisRepresentation.action_one_apply {G : Type*} [Group G] {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E]
    (ρ : GaloisRepresentation G 𝕜 E) (x : E) :
    ρ.action 1 x = x := by
  rw [map_one]
  rfl

end KinematicRiemann
