/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Mathlib.FieldTheory.AbelRuffini

/-!
# Galois groups under extension of the coefficient field

`Polynomial.Gal.restrictMap` embeds the Galois group after base change into the
original Galois group. Solvability is a corollary of this injective homomorphism.
-/

public section

namespace Polynomial

open Polynomial IntermediateField

universe u v
variable {K : Type u} [Field K] (F : Type v) [Field F] [Algebra K F]

namespace Gal

/-- Restrict an automorphism of the splitting field after extending the coefficient field.
The chosen splitting-field embedding is the one used by `Polynomial.Gal.restrict`. -/
noncomputable def restrictMap (p : K[X]) : (p.map (algebraMap K F)).Gal →* p.Gal := by
  let q := p.map (algebraMap K F)
  let M := q.SplittingField
  have : Fact ((p.map (algebraMap K M)).Splits) := ⟨by
    rw [IsScalarTower.algebraMap_eq K F M, ← Polynomial.map_map]
    exact SplittingField.splits q⟩
  exact (Polynomial.Gal.restrict p M).comp (AlgEquiv.restrictScalarsHom K)

/-- Restriction after coefficient-field extension is injective, since roots generate
its splitting field over the larger coefficient field. -/
theorem restrictMap_injective (p : K[X]) : Function.Injective (restrictMap F p) := by
  let q := p.map (algebraMap K F)
  let M := q.SplittingField
  have : Fact ((p.map (algebraMap K M)).Splits) := ⟨by
    rw [IsScalarTower.algebraMap_eq K F M, ← Polynomial.map_map]
    exact SplittingField.splits q⟩
  apply (injective_iff_map_eq_one (restrictMap F p)).mpr
  intro σ hσ
  suffices heq : σ.toAlgHom = (1 : Gal(M/F)).toAlgHom by
    exact AlgEquiv.ext (fun x ↦ DFunLike.congr_fun heq x)
  apply AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet M q)
  intro x hx
  have hx' : x ∈ p.rootSet M := by simpa [q] using hx
  rw [← (SplittingField.splits p).image_rootSet
    (IsScalarTower.toAlgHom K p.SplittingField M)] at hx'
  obtain ⟨y, _, rfl⟩ := hx'
  have hy := congrArg (fun τ : p.Gal ↦ τ y) hσ
  have hc := (σ.restrictScalars K).restrictNormal_commutes p.SplittingField y
  change σ (algebraMap p.SplittingField M y) = algebraMap p.SplittingField M y
  change (σ.restrictScalars K).restrictNormal p.SplittingField y = y at hy
  change algebraMap p.SplittingField M
    ((σ.restrictScalars K).restrictNormal p.SplittingField y) =
      σ (algebraMap p.SplittingField M y) at hc
  rw [hy] at hc
  exact hc.symm

end Gal

/-- Extending the coefficient field preserves solvability of a polynomial's Galois group. -/
theorem isSolvable_gal_map (p : K[X]) [Group.IsSolvable p.Gal] :
    Group.IsSolvable (p.map (algebraMap K F)).Gal :=
  Group.isSolvable_of_isSolvable_injective (Gal.restrictMap_injective F p)

end Polynomial
