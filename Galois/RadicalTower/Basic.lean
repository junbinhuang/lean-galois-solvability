/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Finite radical towers in a common ambient field

All fields use mathlib's field and intermediate-field structures. A tower is a finite
inductively generated relation: its constructors retain a
generator, an exponent at least two, and the equation placing its power in the previous field.
The supremum `E ⊔ K⟮a⟯` is the field obtained by adjoining `a` to `E` inside the ambient field.

No normality, separability, or characteristic assumption is needed here.
-/

public section

namespace IntermediateField

open IntermediateField

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- A finite radical tower from `F` to `E`, inside the fixed ambient extension `L/K`.
The zero-step tower is allowed, and every nonempty step has exponent at least two.
This asserts that `E/F` itself is radical, not merely contained in a radical extension. -/
inductive IsRadicalTower : IntermediateField K L → IntermediateField K L → Prop
  | refl (F : IntermediateField K L) : IsRadicalTower F F
  | adjoin {F E : IntermediateField K L} (tower : IsRadicalTower F E) (a : L) (n : ℕ)
      (exponent_ge_two : 2 ≤ n) (pow_mem : a ^ n ∈ E) :
      IsRadicalTower F (E ⊔ K⟮a⟯)

namespace IsRadicalTower

variable {F E M : IntermediateField K L}

/-- The starting field is contained in the endpoint. -/
theorem le (h : IsRadicalTower F E) : F ≤ E := by
  induction h with
  | refl => exact le_rfl
  | adjoin _ _ _ _ _ ih => exact le_trans ih le_sup_left

/-- Concatenate two finite radical towers. -/
theorem trans (h₁ : IsRadicalTower F E) (h₂ : IsRadicalTower E M) :
    IsRadicalTower F M := by
  induction h₂ with
  | refl => exact h₁
  | adjoin _ a n hn hp ih => exact ih.adjoin a n hn hp

/-- Adjoining an auxiliary field to every layer preserves the tower. -/
theorem sup_right (h : IsRadicalTower F E) (M : IntermediateField K L) :
    IsRadicalTower (F ⊔ M) (E ⊔ M) := by
  induction h with
  | refl => exact .refl _
  | @adjoin E _ a n hn hp ih =>
    simpa only [sup_right_comm] using
      ih.adjoin a n hn ((show E ≤ E ⊔ M from le_sup_left) hp)

/-- An intermediate field may replace the base of a radical tower. -/
theorem of_le_of_le (h : IsRadicalTower F E) (hFM : F ≤ M) (hME : M ≤ E) :
    IsRadicalTower M E := by
  simpa only [sup_eq_right.mpr hFM, sup_eq_left.mpr hME] using h.sup_right M

/-- The compositum of two radical endpoints is radical over the common base. -/
theorem sup (hE : IsRadicalTower F E) (hM : IsRadicalTower F M) :
    IsRadicalTower F (E ⊔ M) := by
  apply hE.trans
  simpa only [sup_eq_right.mpr hE.le, sup_comm M E] using hM.sup_right E

variable {L' : Type w} [Field L'] [Algebra K L']

/-- Transport every generator and power relation along a field embedding. -/
theorem map (h : IsRadicalTower F E) (f : L →ₐ[K] L') :
    IsRadicalTower (F.map f) (E.map f) := by
  induction h with
  | refl => exact .refl _
  | adjoin _ a n hn hp ih =>
    rw [IntermediateField.map_sup, IntermediateField.adjoin_map, Set.image_singleton]
    apply ih.adjoin (f a) n hn
    rw [← map_pow]
    exact ⟨a ^ n, hp, rfl⟩

/-- A radical tower over a finitely generated intermediate field has a finitely
generated endpoint. No algebraicity of the ambient field is assumed. -/
theorem fg (h : IsRadicalTower F E) (hF : F.FG) : E.FG := by
  induction h with
  | refl => exact hF
  | adjoin _ a _ _ _ ih =>
    exact IntermediateField.fg_sup ih
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton a))

end IsRadicalTower

end IntermediateField
