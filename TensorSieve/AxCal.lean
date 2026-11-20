import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

/-!
# Division-Free Integer Metrics (`AxCal`)

This module defines `DivisionFreeMetric`, a typeclass for integer-valued
distance functions with decidable zero-testing (`Decidable (dist_sq a b = 0)`),
keeping metric comparisons strictly inside computable `ℤ` arithmetic.
-/

namespace KinematicRiemann

/--
A typeclass for integer-valued distance calculations that avoid division
and floating-point roots, with decidable equality to zero.
-/
class DivisionFreeMetric (α : Type*) where
  /-- Integer-valued distance (or squared distance) between two points. -/
  dist_sq : α → α → ℤ
  /-- Zero-distance testing is constructively decidable. -/
  dist_sq_computable : ∀ (a b : α), Decidable (dist_sq a b = 0)

/-- Standard integer Euclidean squared distance on `ℤ × ℤ`. -/
instance : DivisionFreeMetric (ℤ × ℤ) where
  dist_sq a b := (a.1 - b.1) * (a.1 - b.1) + (a.2 - b.2) * (a.2 - b.2)
  dist_sq_computable _ _ := inferInstance

end KinematicRiemann
