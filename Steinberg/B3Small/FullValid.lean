/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.B3Small.Defs
import Steinberg.Defs.PartialChevalleyGroup
import Steinberg.Upstream.Chevalley.TypeB.TypeB

import Steinberg.Defs.Commutator

namespace Steinberg

variable {F : Type TR} [CommRing F]

open PartialChevalleySystem B3Small
  B3SmallPosRoot PartialChevalley ChevalleyGenerator
  PartialChevalleyGroup Chevalley.TypeB

namespace B3SmallPosRoot

def toB3Root (ζ : B3SmallPosRoot) : BRoot (Fin 3) :=
  match ζ with
  | β =>   Sum.inl (BLongRoot.mk true false 1 2 (by tauto))
  | ψ =>   Sum.inr (BShortRoot.mk true 2)
  | ω =>   Sum.inr (BShortRoot.mk false 0)
  | βψ =>  Sum.inr (BShortRoot.mk true 1)
  | ψω =>  Sum.inl (BLongRoot.mk false true 0 2 (by tauto))
  | β2ψ => Sum.inl (BLongRoot.mk true true 1 2 (by tauto))
  | βψω => Sum.inl (BLongRoot.mk false true 0 1 (by tauto))


abbrev toB3Mat (g : ChevalleyGenerator B3SmallPosRoot F) := (toB3Root g.ζ).M g.t

end B3SmallPosRoot

open B3SmallPosRoot

theorem b3small_valid :
  ∀ r ∈ (fullB3Small F).allRelations, (FreeGroup.lift toB3Mat r) = 1 := by
  intro r h
  simp only [allRelations, Set.mem_iUnion] at h
  rcases h with ⟨ K, h ⟩
  rcases K
  all_goals simp only at h
  · simp only [fullB3Small, fullMk, fullB3SmallSystem, mkFull,
      fullTrivialSpanPairs, weakTrivialSpanPairs, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [trivialSpanRelationsOfRootPair, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals (
      subst p
      simp only [toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M]
    )
    any_goals (
      rw [MLong_MShort_comm_disjoint]
      all_goals tauto
    )
    any_goals ( -- handle the goals where we have ⁅ MShort, MLong ⁆
      rw [triv_comm_symm, MLong_MShort_comm_disjoint]
      all_goals tauto
    )
    any_goals (
      rw [MLong_comm_disjoint]
      all_goals tauto
    )
    apply MLong_comm_disjoint'
  · simp only [fullB3Small, fullMk, fullB3SmallSystem, mkFull,
      fullSingleSpanRootPairs, weakSingleSpanRootPairs, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [singleSpanRelationsOfRootPair, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h
    all_goals (
      subst p
      apply mul_inv_eq_of_eq_mul
      simp only [toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M,
        Fin.isValue, Int.cast_one, Int.cast_two, Int.cast_neg, one_mul]
    )
    any_goals (
      rw [MShort_comm, MLong_swap]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )
    · nth_rewrite 2 [MLong_swap]
      rw [←Bool.not_false, MLong_comm_overlap]
      nth_rewrite 2 [MLong_swap]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
  · simp only [fullB3Small, fullMk, fullB3SmallSystem, mkFull,
      fullSingleSpanRootPairs, singleSpanRootPairs, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [doubleSpanRelationsOfRootPair, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    subst p
    apply mul_inv_eq_of_eq_mul
    simp only [toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M,
      Fin.isValue, Int.cast_one, one_mul]
    · rw [MLong_swap, ←Bool.not_false, MLong_MShort_comm_overlap, MLong_swap]
      simp only [Bool.not_false, true_toRing, false_toRing]
      ring_nf
  · simp only [fullB3Small, fullMk, fullB3SmallSystem, mkFull,
      fullPresentRoots, B3Small.weakPresentRoots, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [linearityRelationsOfRoot, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of, toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h
    all_goals (
      subst p
      simp only
      apply mul_inv_eq_of_eq_mul
      simp only [one_mul]
    )
    any_goals rw [MShort_mul_add]
    all_goals rw [MLong_mul_add]
  · simp only [definitionRelations, fullB3Small, fullMk, fullB3SmallSystem, mkFull,
      Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    subst r
    simp only [inv_mul_cancel, map_one]

end Steinberg
