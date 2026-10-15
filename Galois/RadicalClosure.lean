/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Mathlib.FieldTheory.AbelRuffini

/-!
# Radical closure and the necessary direction of Galois's theorem

This module uses only mathlib's existing radical closure. It proves monotonicity in
its base field and the necessary direction for arbitrary polynomials, without
irreducibility, separability, or characteristic assumptions.
-/

public section

open IntermediateField Polynomial

universe u v w

/-- Enlarging the base field enlarges its radical closure in a common ambient field. -/
theorem solvableByRad_le_restrictScalars (K : Type u) (F : Type v) (Ω : Type w)
    [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω] [Algebra F Ω]
    [IsScalarTower K F Ω] :
    solvableByRad K Ω ≤ (solvableByRad F Ω).restrictScalars K := by
  apply solvableByRad_le
  intro x n hn hx
  exact solvableByRad.rad_mem hn hx

namespace Polynomial

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- A polynomial that splits with all roots in the radical closure has solvable Galois group.
The zero polynomial is included, since its Galois group is trivial. -/
theorem isSolvable_gal_of_splits_of_rootSet_subset (p : K[X])
    (hs : (p.map (algebraMap K L)).Splits) (hroots : p.rootSet L ⊆ solvableByRad K L) :
    Group.IsSolvable p.Gal := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact gal_zero_isSolvable
  | unit p hp =>
    let := Polynomial.Gal.uniqueGalOfSplits p hp.splits
    infer_instance
  | mul a p ha hp ih =>
    rw [Polynomial.map_mul] at hs
    obtain ⟨hps, has⟩ := (Polynomial.splits_mul (map_ne_zero hp.ne_zero)
      (map_ne_zero ha)).mp hs
    have hsub : p.rootSet L ∪ a.rootSet L ⊆ (p * a).rootSet L := by
      intro x hx
      apply (mem_rootSet_of_ne (mul_ne_zero hp.ne_zero ha)).mpr
      rcases hx with hx | hx
      · simp [map_mul, aeval_eq_zero_of_mem_rootSet hx]
      · simp [map_mul, aeval_eq_zero_of_mem_rootSet hx]
    obtain ⟨x, hx⟩ := hps.exists_eval_eq_zero (by
      rw [degree_map]
      exact hp.degree_pos.ne')
    have hx' : aeval x p = 0 := by simpa only [eval_map_algebraMap] using hx
    have hpg : Group.IsSolvable p.Gal := _root_.isSolvable_gal_of_irreducible
      (hroots (hsub (Or.inl ((mem_rootSet_of_ne hp.ne_zero).mpr hx')))) hp hx'
    exact gal_mul_isSolvable hpg (ih has (fun _ hx ↦ hroots (hsub (Or.inr hx))))

/-- Splitting over the radical closure implies solvability of the Galois group. -/
theorem isSolvable_gal_of_splits_solvableByRad (p : K[X])
    (hs : (p.map (algebraMap K (solvableByRad K L))).Splits) :
    Group.IsSolvable p.Gal := by
  apply isSolvable_gal_of_splits_of_rootSet_subset p (hs.of_algHom (solvableByRad K L).val)
  rw [← hs.image_rootSet (solvableByRad K L).val]
  rintro _ ⟨x, _, rfl⟩
  exact x.property

end Polynomial
