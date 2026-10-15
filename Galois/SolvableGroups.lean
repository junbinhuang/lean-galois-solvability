/-
Copyright (c) 2026 Junbin Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junbin Huang, Codex
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.QuotientGroup.Simple
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Order.Atoms.Finite

/-!
# Prime cyclic quotients of finite solvable groups

A maximal subgroup containing the commutator gives a simple abelian quotient,
which is cyclic of prime order. This is the only group-theoretic input to the
radical-closed-field proof of Galois's criterion.
-/

public section

namespace Group

open scoped IsMulCommutative

universe u

/-- A nontrivial finite solvable group has a normal subgroup with cyclic
quotient of prime order. -/
theorem exists_normal_isCyclic_quotient_prime (G : Type u) [Group G] [Finite G]
    [Nontrivial G] [Group.IsSolvable G] :
    ∃ (N : Subgroup G) (_ : N.Normal),
      IsCyclic (G ⧸ N) ∧ (Nat.card (G ⧸ N)).Prime := by
  classical
  let := Fintype.ofFinite G
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective
  obtain ⟨N, hN, hc⟩ := (eq_top_or_exists_le_coatom (commutator G)).resolve_left
    (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)))
  have hnormal : N.Normal := Subgroup.Normal.of_commutator_le G hc
  have : IsSimpleGroup (G ⧸ N) := Group.isSimpleGroup_of_isCoatom hN
  have : IsMulCommutative (G ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
  exact ⟨N, hnormal, inferInstance, IsSimpleGroup.prime_card⟩

end Group
