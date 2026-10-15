/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Galois.RadicalClosure
public import Galois.SolvableGroups
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Radical-closed intermediate fields and solvable Galois extensions

The root closure packages auxiliary radicals in one ambient algebraically closed field.
The finite-tower results later recover a finite witness. The algebraic core uses a prime
cyclic quotient, Galois correspondence, and mathlib's cyclic Kummer lemma. That lemma
uses an eigenvector proof in mathlib, replacing Stewart's Hilbert 90 step.
-/

public section

open IntermediateField Polynomial

universe u v w
variable (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]

/-- All nonzero-index radicals of elements of the base, taken in the specified ambient
field, already belong to the image of the base. -/
@[expose] def IsRadicalClosedIn : Prop :=
  ∀ (x : Ω) (n : ℕ), n ≠ 0 → x ^ n ∈ Set.range (algebraMap F Ω) →
    x ∈ Set.range (algebraMap F Ω)

/-- Mathlib's radical closure is closed under radicals in its ambient field. -/
theorem isRadicalClosedIn_solvableByRad :
    IsRadicalClosedIn (solvableByRad F Ω) Ω := by
  intro x n hn hx
  obtain ⟨a, ha⟩ := hx
  have hp : x ^ n ∈ solvableByRad F Ω := by
    rw [← ha]
    exact a.property
  exact ⟨⟨x, solvableByRad.rad_mem hn hp⟩, rfl⟩

/-- Relative radical closedness is equivalent to triviality of the radical closure. -/
theorem isRadicalClosedIn_iff_solvableByRad_eq_bot :
    IsRadicalClosedIn F Ω ↔ solvableByRad F Ω = ⊥ := by
  constructor
  · intro h
    exact le_bot_iff.mp (solvableByRad_le h)
  · intro h x n hn hx
    have hp : x ^ n ∈ solvableByRad F Ω := by
      rw [h]
      exact hx
    have hx' := solvableByRad.rad_mem hn hp
    rw [h] at hx'
    exact hx'

variable {F Ω}

/-- If `F` is radical-closed in a characteristic-zero algebraically closed `Ω`,
then `F` contains a primitive `n`-th root of unity for each nonzero natural number `n`. -/
theorem IsRadicalClosedIn.primitiveRoots_nonempty [CharZero Ω] [IsAlgClosed Ω]
    (h : IsRadicalClosedIn F Ω) {n : ℕ} (hn : n ≠ 0) :
    (primitiveRoots n F).Nonempty := by
  let : NeZero n := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω n
  obtain ⟨z, hz⟩ := h ζ n hn (by rw [hζ.pow_eq_one]; exact ⟨1, map_one _⟩)
  refine ⟨z, (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).mpr ?_⟩
  exact (hz.symm ▸ hζ).of_map_of_injective (algebraMap F Ω).injective

variable {E : Type w} [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- A finite cyclic Galois extension of a relatively radical-closed field has degree one
when the base contains a primitive root of unity of the extension degree. -/
theorem IsRadicalClosedIn.finrank_eq_one_of_isCyclic
    (h : IsRadicalClosedIn F Ω) [IsCyclic Gal(E/F)]
    (hroots : (primitiveRoots (Module.finrank F E) F).Nonempty) (ι : E →ₐ[F] Ω) :
    Module.finrank F E = 1 := by
  obtain ⟨a, ha, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hroots
  obtain ⟨b, hb⟩ := ha
  have haΩ : ι a ∈ Set.range (algebraMap F Ω) := h (ι a) (Module.finrank F E)
    Module.finrank_pos.ne' (by
      refine ⟨b, ?_⟩
      rw [← map_pow, ← hb, ι.commutes])
  obtain ⟨c, hc⟩ := haΩ
  have habot : a ∈ (⊥ : IntermediateField F E) := by
    rw [IntermediateField.mem_bot]
    refine ⟨c, ι.injective ?_⟩
    change ι (algebraMap F E c) = ι a
    rw [ι.commutes, hc]
  apply IntermediateField.bot_eq_top_iff_finrank_eq_one.mp
  apply top_unique
  rw [← hgen]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact habot

/-- A finite solvable Galois extension of `F` embedded in a characteristic-zero
algebraically closed `Ω` has degree one if `F` is radical-closed in `Ω`.
A hypothetical nontrivial group has a prime cyclic quotient; its fixed field
contradicts the cyclic case. -/
theorem IsRadicalClosedIn.finrank_eq_one_of_isSolvable [CharZero Ω] [IsAlgClosed Ω]
    (h : IsRadicalClosedIn F Ω) [Group.IsSolvable Gal(E/F)] (ι : E →ₐ[F] Ω) :
    Module.finrank F E = 1 := by
  classical
  by_cases ht : Subsingleton Gal(E/F)
  · let := ht
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_unique
  · have : Nontrivial Gal(E/F) := not_subsingleton_iff_nontrivial.mp ht
    obtain ⟨N, hN, hcyc, hp⟩ := Group.exists_normal_isCyclic_quotient_prime Gal(E/F)
    let := hN
    let := hcyc
    have : IsCyclic Gal(fixedField N/F) :=
      isCyclic_of_surjective (IsGalois.normalAutEquivQuotient N)
        (IsGalois.normalAutEquivQuotient N).surjective
    have hm := h.finrank_eq_one_of_isCyclic
      (h.primitiveRoots_nonempty Module.finrank_pos.ne') (ι.comp (fixedField N).val)
    have hc : Nat.card (Gal(E/F) ⧸ N) = 1 := by
      rw [Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv,
        IsGalois.card_aut_eq_finrank, hm]
    exact False.elim (hp.ne_one hc)
