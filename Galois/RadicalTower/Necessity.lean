/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.IntermediateNecessity
public import Galois.RadicalTower.Embedding

/-!
# Reusing mathlib's existing necessary direction

The minimal-polynomial and irreducible-polynomial corollaries reuse mathlib's
Abel–Ruffini theorem. The automorphism-group corollaries also cover nonnormal
subextensions and arbitrary characteristic.
-/

public section

universe u v

namespace IntermediateField.IsRadicalTower

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {E : IntermediateField K L} {x : L}

/-- An element in a radical tower has a minimal polynomial with solvable Galois group. -/
theorem isSolvable_gal_minpoly (h : IsRadicalTower (⊥ : IntermediateField K L) E) (hx : x ∈ E) :
    Group.IsSolvable (minpoly K x).Gal :=
  _root_.isSolvable_gal_minpoly (h.le_solvableByRad bot_le hx)

/-- Reuse mathlib's necessary direction for any irreducible polynomial with a root
in a finite radical tower. No separability or characteristic restriction is needed here. -/
theorem isSolvable_gal_of_irreducible (h : IsRadicalTower (⊥ : IntermediateField K L) E)
    (hx : x ∈ E) {f : Polynomial K} (hf : Irreducible f) (hroot : Polynomial.aeval x f = 0) :
    Group.IsSolvable f.Gal :=
  _root_.isSolvable_gal_of_irreducible (h.le_solvableByRad bot_le hx) hf hroot

end IntermediateField.IsRadicalTower

open IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {R : Type*} [Field R] [Algebra K R]

/-- A subextension of a finite radical extension has solvable automorphism group,
without normality, separability, or characteristic assumptions. -/
theorem IsRadicalExtension.isSolvable_aut_of_algHom
    (hR : IsRadicalExtension K R) (ι : L →ₐ[K] R) : Group.IsSolvable Gal(L/K) := by
  have : FiniteDimensional K R := hR.finiteDimensional
  have : FiniteDimensional K L := FiniteDimensional.of_injective ι.toLinearMap ι.injective
  exact isSolvable_aut_of_range_subset_solvableByRad ι (fun x ↦
    IsRadicalTower.le_solvableByRad hR bot_le (show ι x ∈ ⊤ from IntermediateField.mem_top))

/-- A finite radical extension has solvable automorphism group. -/
theorem IsRadicalExtension.isSolvable_aut (h : IsRadicalExtension K L) :
    Group.IsSolvable Gal(L/K) :=
  h.isSolvable_aut_of_algHom (AlgHom.id K L)
