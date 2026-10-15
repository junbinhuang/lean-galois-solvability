/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.PolynomialBaseChange
public import Galois.RadicalClosed

/-!
# Galois's criterion in terms of the radical closure

In characteristic zero, a polynomial has solvable Galois group if and only if it
splits over the radical closure in an algebraically closed ambient extension.
The proof uses cyclic Kummer extensions and a prime cyclic quotient of a finite
solvable group. No finite-tower definition is needed in this module.
-/

public section

open IntermediateField Polynomial

universe u v
variable {K : Type u} [Field K]

namespace Polynomial

/-- Over a characteristic-zero base radical-closed in an algebraically closed
ambient field, every polynomial with solvable Galois group splits over the base. -/
theorem _root_.IsRadicalClosedIn.splits {Ω : Type v} [Field Ω] [Algebra K Ω]
    [CharZero K] [IsAlgClosed Ω] (h : IsRadicalClosedIn K Ω)
    (p : K[X]) [Group.IsSolvable p.Gal] : p.Splits := by
  let : CharZero Ω := Algebra.charZero_of_charZero K Ω
  have : IsGalois K p.SplittingField := {}
  have : Group.IsSolvable Gal(p.SplittingField/K) := ‹Group.IsSolvable p.Gal›
  have hd := h.finrank_eq_one_of_isSolvable (IsAlgClosed.lift : p.SplittingField →ₐ[K] Ω)
  apply (IsSplittingField.splits_iff p.SplittingField p).mpr
  exact congrArg IntermediateField.toSubalgebra
    (IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr hd).symm

/-- In characteristic zero, a polynomial with solvable Galois group splits
over the radical closure in any algebraically closed ambient extension. -/
theorem splits_solvableByRad_of_isSolvable
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CharZero K]
    (p : K[X]) [Group.IsSolvable p.Gal] :
    (p.map (algebraMap K (solvableByRad K Ω))).Splits := by
  let : CharZero Ω := Algebra.charZero_of_charZero K Ω
  have := isSolvable_gal_map (solvableByRad K Ω) p
  exact (isRadicalClosedIn_solvableByRad K Ω).splits _

/-- All roots of a nonzero polynomial with solvable group are in the radical closure. -/
theorem mem_solvableByRad_of_aeval_eq_zero
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CharZero K] (p : K[X]) (hp : p ≠ 0)
    [Group.IsSolvable p.Gal] {x : Ω} (hx : aeval x p = 0) :
    x ∈ solvableByRad K Ω := by
  have hr : x ∈ p.rootSet Ω := (mem_rootSet_of_ne hp).mpr hx
  rw [← (splits_solvableByRad_of_isSolvable Ω p).image_rootSet
    (solvableByRad K Ω).val] at hr
  obtain ⟨y, _, rfl⟩ := hr
  exact y.property

/-- Galois's criterion over any algebraically closed ambient extension, including
zero polynomials and polynomials with repeated roots. -/
theorem splits_solvableByRad_iff_isSolvable_gal
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CharZero K] (p : K[X]) :
    (p.map (algebraMap K (solvableByRad K Ω))).Splits ↔ Group.IsSolvable p.Gal := by
  constructor
  · exact isSolvable_gal_of_splits_solvableByRad p
  · intro h
    exact splits_solvableByRad_of_isSolvable Ω p

end Polynomial
