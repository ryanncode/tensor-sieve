import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Algebra.Module.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Discrete
import TensorSieve.Operator

/-!
# Phase 5: Distribution and Measure Initialization

This module establishes the topological bedrock for locally constant functions
over totally disconnected spaces. This is the first step toward implementing
Bruhat-Schwartz distributions and Adelic additive Haar measures.
-/

namespace KinematicRiemann

/--
A totally disconnected topological space serving as the basis for
our Bruhat-Tits kinematics and p-adic geometry.
-/
class BruhatTitsSpace (X : Type*) extends TopologicalSpace X, TotallyDisconnectedSpace X

/--
Bruhat-Schwartz distributions are built upon locally constant functions
with compact support, taking values in a target module.
This structure forms the bedrock for non-Archimedean integration.
-/
structure BruhatSchwartzFunction (X : Type*) [BruhatTitsSpace X]
    (Y : Type*) [TopologicalSpace Y] [Zero Y] where
  toFun : X → Y
  is_locally_constant : IsLocallyConstant toFun
  has_compact_support : HasCompactSupport toFun

namespace BruhatSchwartzFunction

variable {X : Type*} [BruhatTitsSpace X] {Y : Type*} [TopologicalSpace Y] [Zero Y]

instance : CoeFun (BruhatSchwartzFunction X Y) (fun _ => X → Y) where
  coe f := f.toFun

/-- Helper to construct from a `LocallyConstant` function with compact support -/
def mk' (f : LocallyConstant X Y) (h : HasCompactSupport (⇑f)) : BruhatSchwartzFunction X Y :=
  ⟨⇑f, f.isLocallyConstant, h⟩

end BruhatSchwartzFunction

/--
The Adelic Measure Space couples a totally disconnected Bruhat-Tits topological space
with a measure space that admits an additive Haar measure.
This is the foundational metric for adelic integration.
-/
class AdelicMeasureSpace (X : Type*) [BruhatTitsSpace X]
    [AddGroup X] [IsTopologicalAddGroup X]
    extends MeasurableSpace X, MeasureTheory.MeasureSpace X where
  is_add_haar_measure : MeasureTheory.Measure.IsAddHaarMeasure volume

/--
The integral of a Bruhat-Schwartz function with respect to the
adelic Haar measure over a totally disconnected Bruhat-Tits space.
This formally replaces continuous integration.
-/
noncomputable def bruhatIntegral {X : Type*} [BruhatTitsSpace X]
    [AddGroup X] [IsTopologicalAddGroup X] [AdelicMeasureSpace X]
    {Y : Type*} [TopologicalSpace Y] [Zero Y] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : BruhatSchwartzFunction X Y) : Y :=
  MeasureTheory.integral MeasureTheory.MeasureSpace.volume f.toFun

/-!
### Geometric Translation of Kinematics (Phase 5e)

Bridging the discrete, computable arrays from the non-Archimedean sieve
into the noncomputable, continuous measure spaces required for global
spectral density analysis.
-/

-- Instantiate ℤ as our foundational Bruhat-Tits space
-- The discrete topology intrinsically makes it totally disconnected.
instance : TopologicalSpace ℤ := ⊥
instance : DiscreteTopology ℤ := ⟨rfl⟩
instance : TotallyDisconnectedSpace ℤ := inferInstance
instance : BruhatTitsSpace ℤ := {}

/--
Translates a discrete horizontal lattice slice (from `Operator.lean`)
into a pointwise function over the Bruhat-Tits space (ℤ).
Evaluates the cross-branch amplitude strictly on the provided target node.
-/
noncomputable def sliceToFunction (target : ℕ) (slice : List ℕ) : ℤ → ℝ :=
  fun y => if y.toNat ∈ slice ∧ y ≥ 0 then (crossBranchAmplitude target y.toNat : ℝ) else 0

lemma sliceToFunction_isLocallyConstant (target : ℕ) (slice : List ℕ) :
    IsLocallyConstant (sliceToFunction target slice) := by
  apply IsLocallyConstant.of_discrete

/--
A finite discrete slice inherently has compact support, bridging the finite
computational domain into the topological distribution domain.
-/
lemma sliceToFunction_hasCompactSupport (target : ℕ) (slice : List ℕ) :
    HasCompactSupport (sliceToFunction target slice) := by
  -- The support is bounded by the finite List `slice`
  -- Formal verification requires finite -> compact in discrete spaces.
  sorry

/--
Translates a discrete array of combinatorial operator collisions
into a formal Bruhat-Schwartz distribution.
-/
noncomputable def sliceToBruhatSchwartz (target : ℕ) (slice : List ℕ) :
    BruhatSchwartzFunction ℤ ℝ :=
  ⟨sliceToFunction target slice,
   sliceToFunction_isLocallyConstant target slice,
   sliceToFunction_hasCompactSupport target slice⟩

end KinematicRiemann
