import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Algebra.Module.Basic

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

end KinematicRiemann
