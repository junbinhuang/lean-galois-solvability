/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Mathlib.GroupTheory.Solvable

/-!
# Derived series of the commutator subgroup

The derived series inside the commutator is the original derived series shifted by one.
This optional identity does not introduce a second definition of solvability.
-/

public section

namespace Group

universe u

/-- The derived series inside the commutator maps to the shifted derived series. -/
theorem map_derivedSeries_commutator (G : Type u) [Group G] (n : ℕ) :
    (derivedSeries (commutator G) n).map (commutator G).subtype =
      derivedSeries G (n + 1) := by
  induction n with
  | zero => simp [Subgroup.map_top, Subgroup.range_subtype]
  | succ n ih =>
    simp only [derivedSeries_succ, Subgroup.map_commutator, ih]

end Group
