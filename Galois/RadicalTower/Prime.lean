/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.RadicalTower.Basic
public import Mathlib.Data.Nat.Factors

/-!
# Induction on radical towers using prime exponents

Factor each nonzero exponent and adjoin successive powers of the original generator.
This yields a prime-step induction principle without a second tower predicate.
A radical exponent is not identified with an extension degree.
-/

public section

namespace IntermediateField.IsRadicalTower

universe u v
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- To prove a property of radical endpoints it suffices to check prime-exponent steps.
No characteristic or separability assumption is needed. -/
@[elab_as_elim]
theorem prime_induction_on {F E : IntermediateField K L} (h : IsRadicalTower F E)
    (motive : IntermediateField K L → Prop) (start : motive F)
    (step : ∀ (M : IntermediateField K L) (a : L) (p : ℕ),
      p.Prime → a ^ p ∈ M → motive M → motive (M ⊔ K⟮a⟯)) : motive E := by
  have adjoin_factors (s : List ℕ) (hs : ∀ p ∈ s, p.Prime)
      (M : IntermediateField K L) (a : L) (ha : a ^ s.prod ∈ M)
      (hM : motive M) : motive (M ⊔ K⟮a⟯) := by
    induction s generalizing M with
    | nil =>
      have haM : a ∈ M := by simpa using ha
      have hsub : K⟮a⟯ ≤ M := adjoin_le_iff.mpr (by simpa using haM)
      simpa only [sup_eq_left.mpr hsub] using hM
    | cons p s ih =>
      have hp : p.Prime := hs p (by simp)
      have htail : ∀ q ∈ s, q.Prime := fun q hq ↦ hs q (by simp [hq])
      have hpow : (a ^ s.prod) ^ p ∈ M := by
        simpa only [List.prod_cons, ← pow_mul, Nat.mul_comm] using ha
      have hfirst : motive (M ⊔ K⟮a ^ s.prod⟯) := step M (a ^ s.prod) p hp hpow hM
      have hrest := ih htail (M ⊔ K⟮a ^ s.prod⟯)
        ((show K⟮a ^ s.prod⟯ ≤ M ⊔ K⟮a ^ s.prod⟯ from le_sup_right)
          (mem_adjoin_simple_self K (a ^ s.prod))) hfirst
      have hsub : K⟮a ^ s.prod⟯ ≤ K⟮a⟯ := by
        refine adjoin_le_iff.mpr ?_
        rw [Set.singleton_subset_iff]
        exact pow_mem (mem_adjoin_simple_self K a) s.prod
      simpa only [sup_assoc, sup_eq_right.mpr hsub] using hrest
  induction h with
  | refl => exact start
  | @adjoin M _ a n hn ha ih =>
    apply adjoin_factors n.primeFactorsList
      (fun _ hp ↦ Nat.prime_of_mem_primeFactorsList hp) M a _ ih
    simpa only [Nat.prod_primeFactorsList (by omega : n ≠ 0)] using ha

end IntermediateField.IsRadicalTower
