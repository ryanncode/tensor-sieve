/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Condensed.Basic
import Mathlib.Condensed.Module
import Mathlib.Algebra.Category.ModuleCat.Basic
import TensorSieve.KreinSpace

/-!
# Condensed Mathematics
We utilize Mathlib's built-in Condensed Mathematics library.
-/

universe u

open CategoryTheory
open KinematicRiemann

namespace TensorSieve

/--
We utilize Mathlib's built-in Condensed Mathematics library.
A Condensed Set is a sheaf on the site of Profinite sets.
-/
abbrev CondSet := CondensedSet.{u}

/--
Condensed abelian groups, which are condensed Z-modules.
-/
abbrev CondAb := CondensedAb.{u}

/--
A stub for elevating our `MajorantTopology` vector spaces into the condensed framework.
This allows us to process noncommutative cohomology without triggering type-class diamonds.
-/
def embedToCondensed {V : Type*} [AddCommGroup V] [Module ℂ V] [KreinSpace ℂ V] (M : IndefiniteMetric ℂ V) [HasJOperator ℂ V] :
    CondAb :=
  sorry

end TensorSieve
