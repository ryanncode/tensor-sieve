import Mathlib.NumberTheory.Padics.PadicValuation
import Mathlib.CategoryTheory.Quiver.Basic

namespace KinematicSieve

/--
  The totally disconnected integer record mapping deterministically
  to a sequence of p-adic valuations. The absolute dimension is zero.
-/
inductive SemanticAddress : Type
  | root : SemanticAddress
  | step : (p : Nat) → (val : Nat) → SemanticAddress → SemanticAddress

/--
  The Quiver instance defining the incidence relation.
  An edge exists from `a` to `b` exclusively if `b` is generated
  by exactly one prime multiplication operation from `a`.
-/
instance : Quiver SemanticAddress where
  Hom a b := ∃ (p : Nat), b = SemanticAddress.step p 1 a

end KinematicSieve
