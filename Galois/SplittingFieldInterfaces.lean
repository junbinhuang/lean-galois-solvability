/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.Main

/-!
# Splitting-field and abstract-extension interfaces

These equivalences remove the choice of algebraic closure or splitting field from
the finite-witness criterion. The extension criterion retains the Galois assumption:
solvability of the automorphism group alone does not suffice for a nonnormal extension.
-/

public section

open IntermediateField Polynomial

universe u v
variable {K : Type u} [Field K]

namespace Polynomial

/-- Any abstract radical extension in which a polynomial splits gives the
canonical finite-tower witness. The witness may initially live in any universe. -/
theorem solvableByRadicals_of_isRadicalExtension_of_splits {R : Type v} [Field R] [Algebra K R]
    (hR : IsRadicalExtension K R) (p : K[X]) (hs : (p.map (algebraMap K R)).Splits) :
    SolvableByRadicals p := by
  have : FiniteDimensional K R := hR.finiteDimensional
  let σ : R →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let σ' : R →ₐ[K] σ.fieldRange := σ.codRestrict _
    (fun x ↦ AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  exact ⟨σ.fieldRange,
    isRadicalExtension_iff_isRadicalTower.mpr
      ((isRadicalExtension_iff_isRadicalTower_fieldRange σ).mp hR),
    hs.of_algHom σ'⟩

/-- The finite-radical splitting predicate is equivalent to containment of
any chosen splitting field via a base-field embedding. -/
theorem solvableByRadicals_iff_exists_splittingField_algHom (p : K[X])
    (L : Type v) [Field L] [Algebra K L] [IsSplittingField K L p] :
    SolvableByRadicals p ↔
      ∃ R : IntermediateField K (AlgebraicClosure K), IsRadicalExtension K R ∧
        Nonempty (L →ₐ[K] R) := by
  constructor
  · rintro ⟨R, hR, hs⟩
    exact ⟨R, hR, ⟨IsSplittingField.lift L p hs⟩⟩
  · rintro ⟨R, hR, ⟨σ⟩⟩
    exact ⟨R, hR, (IsSplittingField.splits L p).of_algHom σ⟩

/-- The main equivalence for the automorphism group of any chosen splitting field. -/
theorem solvableByRadicals_iff_isSolvable_aut [CharZero K] (p : K[X])
    (L : Type v) [Field L] [Algebra K L] [IsSplittingField K L p] :
    SolvableByRadicals p ↔ Group.IsSolvable Gal(L/K) := by
  rw [solvableByRadicals_iff_isSolvable_gal p]
  let e : Gal(L/K) ≃* p.Gal := (IsSplittingField.algEquiv L p).autCongr
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · intro h
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

end Polynomial

open Polynomial

/-- Every finite solvable Galois extension in characteristic zero embeds into
a finite radical extension. -/
theorem exists_isRadicalExtension_of_isSolvable (L : Type v) [Field L] [Algebra K L]
    [CharZero K] [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable Gal(L/K)] :
    ∃ R : IntermediateField K (AlgebraicClosure K), IsRadicalExtension K R ∧
      Nonempty (L →ₐ[K] R) := by
  obtain ⟨p, _, hsplit⟩ := IsGalois.is_separable_splitting_field K L
  have : Group.IsSolvable p.Gal := Group.isSolvable_of_surjective
    (f := (IsSplittingField.algEquiv L p).autCongr.toMonoidHom)
    (IsSplittingField.algEquiv L p).autCongr.surjective
  exact (solvableByRadicals_iff_exists_splittingField_algHom p L).mp
    (solvableByRadicals_of_isSolvable p)

/-- Field-extension form of the full equivalence. The containing radical field
is allowed to be strictly larger than the original Galois extension. -/
theorem isSolvable_aut_iff_exists_isRadicalExtension (L : Type v) [Field L] [Algebra K L]
    [CharZero K] [FiniteDimensional K L] [IsGalois K L] :
    Group.IsSolvable Gal(L/K) ↔
      ∃ R : IntermediateField K (AlgebraicClosure K), IsRadicalExtension K R ∧
        Nonempty (L →ₐ[K] R) := by
  obtain ⟨p, _, hsplit⟩ := IsGalois.is_separable_splitting_field K L
  exact (solvableByRadicals_iff_isSolvable_aut p L).symm.trans
    (solvableByRadicals_iff_exists_splittingField_algHom p L)

namespace Polynomial

/-- The chosen algebraic closure does not restrict the existential definition:
solvability is exactly splitting in some abstract finite radical extension. -/
theorem solvableByRadicals_iff_exists_isRadicalExtension_splits (p : K[X]) :
    SolvableByRadicals p ↔
      ∃ (R : Type u) (_ : Field R) (_ : Algebra K R), IsRadicalExtension K R ∧
        (p.map (algebraMap K R)).Splits := by
  constructor
  · rintro ⟨R, hR, hs⟩
    exact ⟨R, inferInstance, inferInstance, hR, hs⟩
  · rintro ⟨R, _, _, hR, hs⟩
    exact solvableByRadicals_of_isRadicalExtension_of_splits hR p hs

/-- Stewart's Galois solvability theorem in its original existential-extension
form, independent of a choice of splitting field or ambient algebraic closure. -/
theorem exists_isRadicalExtension_algHom_iff_isSolvable_aut [CharZero K] (p : K[X])
    (L : Type v) [Field L] [Algebra K L] [IsSplittingField K L p] :
    (∃ (R : Type u) (_ : Field R) (_ : Algebra K R), IsRadicalExtension K R ∧
      Nonempty (L →ₐ[K] R)) ↔ Group.IsSolvable Gal(L/K) := by
  rw [← solvableByRadicals_iff_isSolvable_aut p L,
    solvableByRadicals_iff_exists_isRadicalExtension_splits]
  constructor
  · rintro ⟨R, _, _, hR, ⟨σ⟩⟩
    exact ⟨R, inferInstance, inferInstance, hR, (IsSplittingField.splits L p).of_algHom σ⟩
  · rintro ⟨R, _, _, hR, hs⟩
    exact ⟨R, inferInstance, inferInstance, hR, ⟨IsSplittingField.lift L p hs⟩⟩

end Polynomial
