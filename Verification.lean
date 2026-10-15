/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.All

/-!
# Verification of public statements and axiom dependencies

Run with `lake env lean Verification.lean`. The examples exercise the generalized
interfaces, including zero polynomials and arbitrary-characteristic necessity.
The commands print recursive axiom dependencies of every public declaration.
-/

open IntermediateField Polynomial

universe u v w

section Interfaces

variable {K : Type u} {L : Type v} {Ω : Type w}
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]

example [CharZero K] (p : K[X]) :
    p.SolvableByRadicals ↔ Group.IsSolvable p.Gal :=
  Polynomial.solvableByRadicals_iff_isSolvable_gal p

example [CharZero K] : (0 : K[X]).SolvableByRadicals :=
  Polynomial.solvableByRadicals_of_isSolvable 0

example [CharZero K] [IsAlgClosed Ω] (p : K[X]) :
    (p.map (algebraMap K (solvableByRad K Ω))).Splits ↔ Group.IsSolvable p.Gal :=
  Polynomial.splits_solvableByRad_iff_isSolvable_gal Ω p

example (h : IsRadicalExtension K L) : Group.IsSolvable Gal(L/K) :=
  h.isSolvable_aut

example [FiniteDimensional K L] (ι : L →ₐ[K] Ω)
    (hι : ∀ x, ι x ∈ solvableByRad K Ω) : Group.IsSolvable Gal(L/K) :=
  isSolvable_aut_of_range_subset_solvableByRad ι hι

example [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (h : IsRadicalClosedIn K Ω)
    (hroots : (primitiveRoots (Module.finrank K L) K).Nonempty) (ι : L →ₐ[K] Ω) :
    Module.finrank K L = 1 :=
  h.finrank_eq_one_of_isCyclic hroots ι

end Interfaces

#print axioms IsRadicalClosedIn.splits
#print axioms Polynomial.splits_solvableByRad_of_isSolvable
#print axioms Polynomial.mem_solvableByRad_of_aeval_eq_zero
#print axioms Polynomial.splits_solvableByRad_iff_isSolvable_gal
#print axioms Group.map_derivedSeries_commutator
#print axioms isSolvable_aut_of_isGalois_of_range_subset_solvableByRad
#print axioms isSolvable_aut_of_range_subset_solvableByRad
#print axioms Polynomial.SolvableByRadicals
#print axioms Polynomial.solvableByRadicals_of_splits_solvableByRad
#print axioms Polynomial.solvableByRadicals_iff_splits_solvableByRad
#print axioms Polynomial.isSolvable_gal_of_isRadicalExtension_of_splits
#print axioms Polynomial.solvableByRadicals_of_isSolvable
#print axioms Polynomial.solvableByRadicals_iff_isSolvable_gal
#print axioms Polynomial.Gal.restrictMap
#print axioms Polynomial.Gal.restrictMap_injective
#print axioms Polynomial.isSolvable_gal_map
#print axioms IsRadicalClosedIn
#print axioms isRadicalClosedIn_solvableByRad
#print axioms isRadicalClosedIn_iff_solvableByRad_eq_bot
#print axioms IsRadicalClosedIn.primitiveRoots_nonempty
#print axioms IsRadicalClosedIn.finrank_eq_one_of_isCyclic
#print axioms IsRadicalClosedIn.finrank_eq_one_of_isSolvable
#print axioms solvableByRad_le_restrictScalars
#print axioms Polynomial.isSolvable_gal_of_splits_of_rootSet_subset
#print axioms Polynomial.isSolvable_gal_of_splits_solvableByRad
#print axioms IntermediateField.IsRadicalTower
#print axioms IntermediateField.IsRadicalTower.le
#print axioms IntermediateField.IsRadicalTower.trans
#print axioms IntermediateField.IsRadicalTower.sup_right
#print axioms IntermediateField.IsRadicalTower.of_le_of_le
#print axioms IntermediateField.IsRadicalTower.sup
#print axioms IntermediateField.IsRadicalTower.map
#print axioms IntermediateField.IsRadicalTower.fg
#print axioms IntermediateField.IsRadicalTower.le_solvableByRad
#print axioms IntermediateField.IsRadicalTower.isIntegral
#print axioms IntermediateField.IsRadicalTower.finiteDimensional
#print axioms exists_isRadicalTower_of_mem_solvableByRad
#print axioms mem_solvableByRad_iff_exists_isRadicalTower
#print axioms exists_isRadicalTower_of_finset
#print axioms exists_isRadicalTower_of_finite
#print axioms exists_isRadicalTower_of_fg
#print axioms exists_isRadicalTower_of_finiteDimensional
#print axioms solvableByRad_eq_iSup_isRadicalTower
#print axioms IntermediateField.IsRadicalTower.comap
#print axioms IntermediateField.IsRadicalTower.map_iff
#print axioms IsRadicalExtension
#print axioms isRadicalExtension_iff_isRadicalTower
#print axioms isRadicalExtension_iff_isRadicalTower_fieldRange
#print axioms IntermediateField.IsRadicalTower.fieldRange
#print axioms IsRadicalExtension.algEquiv_iff
#print axioms IsRadicalExtension.finiteDimensional
#print axioms IntermediateField.IsRadicalTower.map_equiv_iff
#print axioms IntermediateField.IsRadicalTower.isSolvable_gal_minpoly
#print axioms IntermediateField.IsRadicalTower.isSolvable_gal_of_irreducible
#print axioms IsRadicalExtension.isSolvable_aut_of_algHom
#print axioms IsRadicalExtension.isSolvable_aut
#print axioms IntermediateField.IsRadicalTower.finset_sup
#print axioms IntermediateField.IsRadicalTower.iSup
#print axioms IntermediateField.IsRadicalTower.normalClosure
#print axioms IntermediateField.IsRadicalTower.exists_normalClosure
#print axioms IsRadicalExtension.normalClosure
#print axioms IsRadicalExtension.exists_finite_normal_extension
#print axioms IntermediateField.IsRadicalTower.prime_induction_on
#print axioms Group.exists_normal_isCyclic_quotient_prime
#print axioms Polynomial.solvableByRadicals_of_isRadicalExtension_of_splits
#print axioms Polynomial.solvableByRadicals_iff_exists_splittingField_algHom
#print axioms Polynomial.solvableByRadicals_iff_isSolvable_aut
#print axioms exists_isRadicalExtension_of_isSolvable
#print axioms isSolvable_aut_iff_exists_isRadicalExtension
#print axioms Polynomial.solvableByRadicals_iff_exists_isRadicalExtension_splits
#print axioms Polynomial.exists_isRadicalExtension_algHom_iff_isSolvable_aut
