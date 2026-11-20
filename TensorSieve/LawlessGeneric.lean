import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import TensorSieve.Kinematics

/-!
# Combinatorial Successor Saturation

This module formalizes finite successor dynamics on `Finset ℕ` (`x ↦ x ∪ {x.card}`)
and proves exact monotonicity, cardinality, and saturation-threshold properties.
-/

namespace KinematicRiemann

/--
The finite set-theoretic successor step `x ↦ x ∪ {x.card}`.
-/
def grammarSuccessor (x : Finset ℕ) : Finset ℕ := x ∪ {x.card}

/--
A finite state is saturated below `bound` if applying `grammarSuccessor`
adds no new elements strictly smaller than `bound`.
-/
def IsMaximallySaturated (state : Finset ℕ) (bound : ℕ) : Prop :=
  Finset.filter (· < bound) (grammarSuccessor state) = Finset.filter (· < bound) state

theorem subset_grammarSuccessor (x : Finset ℕ) : x ⊆ grammarSuccessor x :=
  Finset.subset_union_left

theorem card_grammarSuccessor_le (x : Finset ℕ) : (grammarSuccessor x).card ≤ x.card + 1 := by
  unfold grammarSuccessor
  calc (x ∪ {x.card}).card
      ≤ x.card + ({x.card} : Finset ℕ).card := Finset.card_union_le x {x.card}
    _ = x.card + 1 := by simp

/--
Once `bound ≤ state.card`, the newly adjoined token `state.card` lies outside
the bounded window `{n | n < bound}`, so `state` is saturated below `bound`.
-/
theorem isMaximallySaturated_of_bound_le_card (state : Finset ℕ) (bound : ℕ)
    (h : bound ≤ state.card) : IsMaximallySaturated state bound := by
  unfold IsMaximallySaturated grammarSuccessor
  ext n
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hn | rfl, hlt⟩
    · exact ⟨hn, hlt⟩
    · omega
  · rintro ⟨hn, hlt⟩
    exact ⟨Or.inl hn, hlt⟩

end KinematicRiemann
