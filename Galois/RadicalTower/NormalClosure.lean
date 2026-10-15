/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.RadicalTower.Closure
public import Galois.RadicalTower.Embedding
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure

/-!
# Finite composita and radical normal closures

A finite compositum of radical extensions is radical. A finite
extension has finitely many embeddings, so adjoining all its conjugate radical towers
produces a radical normal closure. Normality is asserted only in a normal ambient field.
None of these results requires separability or characteristic zero.
-/

public section

open IntermediateField

universe u v w z
variable {K : Type u} {L : Type v} {L' : Type w}
  [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- Compose finitely many radical towers over a common starting field.
The extra `F` also handles the empty family. -/
theorem IntermediateField.IsRadicalTower.finset_sup {ι : Type z} (F : IntermediateField K L)
    (s : Finset ι) (E : ι → IntermediateField K L)
    (h : ∀ i ∈ s, IsRadicalTower F (E i)) : IsRadicalTower F (F ⊔ s.sup E) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty, sup_bot_eq] using IsRadicalTower.refl F
  | @insert i s hi ih =>
    have hE := h i (by simp)
    have hS := ih (fun j hj ↦ h j (by simp [hj]))
    rw [Finset.sup_insert]
    simpa only [← sup_assoc, sup_eq_left.mpr hE.le, sup_eq_right.mpr hE.le] using hE.sup hS

/-- The compositum of a finite indexed family of radical endpoints is radical. -/
theorem IntermediateField.IsRadicalTower.iSup {ι : Type z} [Finite ι]
    (E : ι → IntermediateField K L)
    (h : ∀ i, IsRadicalTower ⊥ (E i)) : IsRadicalTower ⊥ (⨆ i, E i) := by
  classical
  let := Fintype.ofFinite ι
  simpa [Finset.sup_eq_iSup] using
    IsRadicalTower.finset_sup ⊥ Finset.univ E (fun i _ ↦ h i)

/-- The compositum of all images of a radical endpoint is radical.
In an arbitrary ambient field this object need not be a normal extension. -/
theorem IntermediateField.IsRadicalTower.normalClosure {E : IntermediateField K L}
    (h : IsRadicalTower ⊥ E) :
    IsRadicalTower (⊥ : IntermediateField K L') (IntermediateField.normalClosure K E L') := by
  let : FiniteDimensional K E := h.finiteDimensional
  exact IsRadicalTower.iSup (fun f : E →ₐ[K] L' ↦ f.fieldRange)
    (fun f ↦ h.fieldRange f)

/-- In a normal ambient extension, a radical endpoint is contained in a finite
normal radical extension which is a normal closure of that endpoint. -/
theorem IntermediateField.IsRadicalTower.exists_normalClosure {E : IntermediateField K L}
    [Normal K L] (h : IsRadicalTower ⊥ E) :
    ∃ N : IntermediateField K L, E ≤ N ∧ IsRadicalTower ⊥ N ∧
      FiniteDimensional K N ∧ Normal K N ∧ IsNormalClosure K E N := by
  let : FiniteDimensional K E := h.finiteDimensional
  let : Nonempty (E →ₐ[K] L) := ⟨E.val⟩
  exact ⟨IntermediateField.normalClosure K E L, E.le_normalClosure, h.normalClosure,
    inferInstance, inferInstance, inferInstance⟩

/-- The compositum of all embedding images of a radical extension in `L'` is radical.
This construction is named `normalClosure`; normality is not asserted for arbitrary `L'`. -/
theorem IsRadicalExtension.normalClosure (h : IsRadicalExtension K L) :
    IsRadicalExtension K (IntermediateField.normalClosure K L L') := by
  let : FiniteDimensional K L := h.finiteDimensional
  apply isRadicalExtension_iff_isRadicalTower.mpr
  exact IsRadicalTower.iSup (fun f : L →ₐ[K] L' ↦ f.fieldRange)
    (fun f ↦ (isRadicalExtension_iff_isRadicalTower_fieldRange f).mp h)

/-- Every radical extension embeds into a finite normal radical extension.
The containing field is constructed inside the algebraic closure of the base. -/
theorem IsRadicalExtension.exists_finite_normal_extension (h : IsRadicalExtension K L) :
    ∃ N : IntermediateField K (AlgebraicClosure K), Nonempty (L →ₐ[K] N) ∧
      IsRadicalExtension K N ∧ FiniteDimensional K N ∧ Normal K N ∧
      IsNormalClosure K L N := by
  let : FiniteDimensional K L := h.finiteDimensional
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let : Nonempty (L →ₐ[K] AlgebraicClosure K) := ⟨f⟩
  refine ⟨IntermediateField.normalClosure K L (AlgebraicClosure K), ?_, h.normalClosure,
    inferInstance, inferInstance, inferInstance⟩
  exact ⟨(_root_.normalClosure.algHomEquiv K L (AlgebraicClosure K)).symm f⟩
