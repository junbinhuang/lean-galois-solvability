/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.AbelRuffini
public import Galois.RadicalTower.Necessity
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Solvability by radicals with finite witnesses

`Polynomial.SolvableByRadicals` means splitting in a finite radical extension.
The characteristic-free bridge to `solvableByRad` recovers finite witnesses from
finitely many roots. In characteristic zero it gives Galois's full criterion.
Neither the zero polynomial nor repeated roots require additional hypotheses.
-/

public section

open IntermediateField

universe u v

namespace Polynomial

variable {K : Type u} [Field K]

/-- A polynomial splits in a finite radical extension, represented inside the
algebraic closure of its coefficient field. The extension may be larger than its splitting field. -/
@[expose] def SolvableByRadicals (p : K[X]) : Prop :=
  ∃ R : IntermediateField K (AlgebraicClosure K), IsRadicalExtension K R ∧
    (p.map (algebraMap K R)).Splits

/-- Splitting over the radical closure has a finite radical-extension witness. -/
theorem solvableByRadicals_of_splits_solvableByRad (p : K[X])
    (hs : (p.map (algebraMap K (solvableByRad K (AlgebraicClosure K)))).Splits) :
    SolvableByRadicals p := by
  have hroots : p.rootSet (AlgebraicClosure K) ⊆ solvableByRad K (AlgebraicClosure K) := by
    rw [← hs.image_rootSet (solvableByRad K (AlgebraicClosure K)).val]
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  obtain ⟨R, hR, hroots⟩ := exists_isRadicalTower_of_finite
    (p.rootSet_finite (AlgebraicClosure K)) hroots
  exact ⟨R, isRadicalExtension_iff_isRadicalTower.mpr hR,
    splits_of_splits (IsAlgClosed.splits (p.map (algebraMap K (AlgebraicClosure K)))) hroots⟩

/-- Finite radical witnesses and splitting over the radical closure are equivalent,
without any characteristic or separability assumption. -/
theorem solvableByRadicals_iff_splits_solvableByRad (p : K[X]) :
    SolvableByRadicals p ↔
      (p.map (algebraMap K (solvableByRad K (AlgebraicClosure K)))).Splits := by
  constructor
  · rintro ⟨R, hR, hs⟩
    exact hs.of_algHom (IntermediateField.inclusion
      ((isRadicalExtension_iff_isRadicalTower.mp hR).le_solvableByRad bot_le))
  · exact solvableByRadicals_of_splits_solvableByRad p

/-- A polynomial that splits in a radical extension has solvable Galois group. -/
theorem isSolvable_gal_of_isRadicalExtension_of_splits
    {R : Type v} [Field R] [Algebra K R] (hR : IsRadicalExtension K R)
    (p : K[X]) (hs : (p.map (algebraMap K R)).Splits) : Group.IsSolvable p.Gal := by
  apply isSolvable_gal_of_splits_of_rootSet_subset p hs
  intro x _
  exact IsRadicalTower.le_solvableByRad hR bot_le IntermediateField.mem_top

/-- A polynomial with solvable Galois group has a finite radical-extension witness. -/
theorem solvableByRadicals_of_isSolvable [CharZero K] (p : K[X])
    [Group.IsSolvable p.Gal] : SolvableByRadicals p :=
  solvableByRadicals_of_splits_solvableByRad p
    (splits_solvableByRad_of_isSolvable (AlgebraicClosure K) p)

/-- Galois's solvability-by-radicals criterion for every polynomial in characteristic zero. -/
theorem solvableByRadicals_iff_isSolvable_gal [CharZero K] (p : K[X]) :
    SolvableByRadicals p ↔ Group.IsSolvable p.Gal := by
  rw [solvableByRadicals_iff_splits_solvableByRad,
    splits_solvableByRad_iff_isSolvable_gal]

end Polynomial
