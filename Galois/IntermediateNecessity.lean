/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.RadicalClosure

/-!
# The stronger necessary direction for nonnormal subextensions

The argument passes to the fixed field of the full automorphism group. This module
keeps that step and proves solvability even when the subextension itself is not normal.
-/

public section

open IntermediateField Polynomial

universe u v w z

variable {K : Type u} {L : Type v} {Ω : Type w}
  [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]

/-- A finite Galois extension whose image consists of radical-closure elements
has solvable Galois group; the extension need not itself be a radical extension. -/
theorem isSolvable_aut_of_isGalois_of_range_subset_solvableByRad [FiniteDimensional K L]
    [IsGalois K L] (ι : L →ₐ[K] Ω) (hι : ∀ x, ι x ∈ solvableByRad K Ω) :
    Group.IsSolvable Gal(L/K) := by
  obtain ⟨p, _, hp⟩ := IsGalois.is_separable_splitting_field K L
  have hs : (p.map (algebraMap K Ω)).Splits := (IsSplittingField.splits L p).of_algHom ι
  have hroots : p.rootSet Ω ⊆ solvableByRad K Ω := by
    rw [← (IsSplittingField.splits L p).image_rootSet ι]
    rintro _ ⟨x, _, rfl⟩
    exact hι x
  have : Group.IsSolvable p.Gal :=
    isSolvable_gal_of_splits_of_rootSet_subset p hs hroots
  let e : Gal(L/K) ≃* p.Gal := (IsSplittingField.algEquiv L p).autCongr
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- Normality is unnecessary for the automorphism-group conclusion. Pass to the
fixed field of all automorphisms. -/
theorem isSolvable_aut_of_range_subset_solvableByRad [FiniteDimensional K L]
    (ι : L →ₐ[K] Ω) (hι : ∀ x, ι x ∈ solvableByRad K Ω) :
    Group.IsSolvable Gal(L/K) := by
  let F := fixedField (⊤ : Subgroup Gal(L/K))
  let : Algebra F Ω := (ι.comp F.val).toRingHom.toAlgebra
  have : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap K Ω x = ι (algebraMap K L x)
    exact (ι.commutes x).symm
  let τ : L →ₐ[F] Ω := { ι.toRingHom with commutes' := fun _ ↦ rfl }
  have : IsGalois F L := IsGalois.of_fixed_field L (⊤ : Subgroup Gal(L/K))
  have : Group.IsSolvable Gal(L/F) := isSolvable_aut_of_isGalois_of_range_subset_solvableByRad τ
    (fun x ↦ solvableByRad_le_restrictScalars K F Ω (hι x))
  apply Group.isSolvable_of_surjective
    (f := (AlgEquiv.restrictScalarsHom K : Gal(L/F) →* Gal(L/K)))
  intro σ
  refine ⟨{ σ.toRingEquiv with commutes' := ?_ }, ?_⟩
  · intro x
    exact (mem_fixedField_iff _ _).mp x.property σ (Subgroup.mem_top σ)
  · exact AlgEquiv.ext (fun _ ↦ rfl)
