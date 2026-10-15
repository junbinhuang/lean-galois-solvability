/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.RadicalTower.Closure

/-!
# Intrinsic radical extensions and embeddings of endpoints

A tower contained in the range of an embedding can be pulled back. This lets us view a
radical intermediate field as a radical extension in its own right, and transport its
tower under embeddings defined only on that field, rather than on the ambient field.
-/

public section

open IntermediateField

universe u v w
variable {K : Type u} {L : Type v} {L' : Type w}
  [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- Pull back a radical tower whose endpoint lies in an embedding's range. -/
theorem IntermediateField.IsRadicalTower.comap {F E : IntermediateField K L'}
    (h : IsRadicalTower F E) (f : L →ₐ[K] L') (hRange : E ≤ f.fieldRange) :
    IsRadicalTower (F.comap f) (E.comap f) := by
  induction h with
  | refl => exact .refl _
  | @adjoin E _ a n hn ha ih =>
    have hE : E ≤ f.fieldRange := le_trans le_sup_left hRange
    have haRange : a ∈ f.fieldRange := hRange
      ((show K⟮a⟯ ≤ E ⊔ K⟮a⟯ from le_sup_right) (mem_adjoin_simple_self K a))
    obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp haRange
    subst a
    have hpow : b ^ n ∈ E.comap f := by
      change f (b ^ n) ∈ E
      simpa only [map_pow] using ha
    have hEq : E.comap f ⊔ K⟮b⟯ = (E ⊔ K⟮f b⟯).comap f := by
      apply IntermediateField.map_injective f
      rw [IntermediateField.map_sup, IntermediateField.map_comap_eq_self hE,
        IntermediateField.adjoin_map, Set.image_singleton,
        IntermediateField.map_comap_eq_self hRange]
    rw [← hEq]
    exact (ih hE).adjoin b n hn hpow

/-- An embedding both preserves and reflects the radical tower property. -/
theorem IntermediateField.IsRadicalTower.map_iff {F E : IntermediateField K L} (f : L →ₐ[K] L') :
    IsRadicalTower (F.map f) (E.map f) ↔ IsRadicalTower F E := by
  constructor
  · intro h
    have hRange : E.map f ≤ f.fieldRange := by
      rintro _ ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
    simpa only [IntermediateField.comap_map] using h.comap f hRange
  · exact fun h ↦ h.map f

/-- The extension itself is the endpoint of a finite radical tower over its base.
This is stronger than being a subfield of some radical extension. -/
@[expose] def IsRadicalExtension (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] : Prop :=
  IsRadicalTower (⊥ : IntermediateField K L) ⊤

/-- The intrinsic radical extension predicate agrees with the ambient tower predicate. -/
theorem isRadicalExtension_iff_isRadicalTower {E : IntermediateField K L} :
    IsRadicalExtension K E ↔ IsRadicalTower (⊥ : IntermediateField K L) E := by
  unfold IsRadicalExtension
  simpa only [IntermediateField.map_bot, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val] using
    (IsRadicalTower.map_iff (F := ⊥) (E := ⊤) E.val).symm

/-- Radicality of a field extension is equivalent to radicality of its image. -/
theorem isRadicalExtension_iff_isRadicalTower_fieldRange (f : L →ₐ[K] L') :
    IsRadicalExtension K L ↔ IsRadicalTower (⊥ : IntermediateField K L') f.fieldRange := by
  unfold IsRadicalExtension
  simpa only [IntermediateField.map_bot, ← AlgHom.fieldRange_eq_map] using
    (IsRadicalTower.map_iff (F := ⊥) (E := ⊤) f).symm

/-- Transport a radical endpoint along any embedding defined on that endpoint. -/
theorem IntermediateField.IsRadicalTower.fieldRange {E : IntermediateField K L}
    (h : IsRadicalTower ⊥ E) (f : E →ₐ[K] L') :
    IsRadicalTower (⊥ : IntermediateField K L') f.fieldRange :=
  (isRadicalExtension_iff_isRadicalTower_fieldRange f).mp
    (isRadicalExtension_iff_isRadicalTower.mpr h)

/-- Intrinsic radicality is invariant under a base-field algebra isomorphism. -/
theorem IsRadicalExtension.algEquiv_iff (e : L ≃ₐ[K] L') :
    IsRadicalExtension K L ↔ IsRadicalExtension K L' := by
  rw [isRadicalExtension_iff_isRadicalTower_fieldRange e.toAlgHom]
  have hRange : e.toAlgHom.fieldRange = ⊤ := by
    apply top_unique
    intro x _
    exact ⟨e.symm x, e.apply_symm_apply x⟩
  rw [hRange]
  rfl

/-- A radical field extension is finite-dimensional over its base. -/
theorem IsRadicalExtension.finiteDimensional (h : IsRadicalExtension K L) :
    FiniteDimensional K L := by
  let : FiniteDimensional K (⊤ : IntermediateField K L) :=
    IsRadicalTower.finiteDimensional h
  exact FiniteDimensional.of_surjective
    (IntermediateField.topEquiv : (⊤ : IntermediateField K L) ≃ₐ[K] L).toLinearMap
    IntermediateField.topEquiv.surjective

/-- The tower property is invariant under an isomorphism of ambient extensions. -/
theorem IntermediateField.IsRadicalTower.map_equiv_iff
    {F E : IntermediateField K L} (e : L ≃ₐ[K] L') :
    IsRadicalTower (F.map e.toAlgHom) (E.map e.toAlgHom) ↔ IsRadicalTower F E :=
  IsRadicalTower.map_iff e.toAlgHom
