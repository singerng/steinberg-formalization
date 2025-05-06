/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.B3Large.Defs
import Steinberg.Defs.PartialChevalleyGroup
import Steinberg.Upstream.Chevalley.TypeB.SteinbergRelations

import Steinberg.Defs.Commutator

import Steinberg.Upstream.Commutator

namespace Steinberg

variable {F : Type TR} [Field F]

open PartialChevalleySystem B3Large B3LargePosRoot PartialChevalley
  ChevalleyGenerator PartialChevalleyGroup
  Chevalley Chevalley.TypeB Chevalley.ChevalleyRealization

def toB3Root (ζ : B3LargePosRoot) : BRoot (Fin 3) :=
  match ζ with
  | α =>     Sum.inl (TwoSignVector.mk true false 0 1 (by tauto))
  | β =>     Sum.inl (TwoSignVector.mk true false 1 2 (by tauto))
  | ψ =>     Sum.inr (OneSignVector.mk true 2)
  | αβ =>    Sum.inl (TwoSignVector.mk true false 0 2 (by tauto))
  | βψ =>    Sum.inr (OneSignVector.mk true 1)
  | β2ψ =>   Sum.inl (TwoSignVector.mk true true 1 2 (by tauto))
  | αβψ =>   Sum.inr (OneSignVector.mk true 0)
  | αβ2ψ =>  Sum.inl (TwoSignVector.mk true true 0 2 (by tauto))
  | α2β2ψ => Sum.inl (TwoSignVector.mk true true 0 1 (by tauto))

abbrev toB3Mat (g : ChevalleyGenerator B3LargePosRoot F) :
  Matrix.GeneralLinearGroup (ZSigned (Fin 3)) F := M (toB3Root g.ζ) g.t

theorem valid :
  ∀ r ∈ (fullB3Large F).allRelations, (FreeGroup.lift toB3Mat r) = 1 := by
  intro r h
  simp only [allRelations, Set.mem_iUnion] at h
  rcases h with ⟨ K, h ⟩
  rcases K
  all_goals simp only at h
  · simp only [fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullTrivialSpanPairs, weakTrivialSpanPairs, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [trivialSpanRelationsOfRootPair, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals (
      subst p
      simp only [toB3Mat, toB3Root, M]
    )
    any_goals (rw [B_MLong_MShort_comm_disjoint]; all_goals tauto)
    any_goals (rw [triv_comm_symm, B_MLong_MShort_comm_disjoint]; all_goals tauto) -- handle the goals where we have ⁅ B_MShort, B_MLong ⁆
    any_goals (rw [B_MLong_comm_disjoint]; all_goals tauto)
    any_goals (apply B_MLong_comm_disjoint')
  · simp only [fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullSingleSpanRootPairs, weakSingleSpanRootPairs, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [singleSpanRelationsOfRootPair, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h
    all_goals (
      subst p
      apply mul_inv_eq_of_eq_mul
      simp only [toB3Mat, toB3Root, M,
        Fin.isValue, Int.cast_one, Int.cast_two, Int.cast_neg, one_mul]
    )
    any_goals (
      rw [B_MShort_comm]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )
    any_goals (
      rw [B_MShort_comm, B_MLong_swap]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )
    any_goals (
      rw [←Bool.not_false, B_MLong_comm_overlap]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )
    -- rearranging required, TODO: automate this
    · nth_rewrite 2 [B_MLong_swap]
      rw [←Bool.not_false, B_MLong_comm_overlap]
      ring_nf
      simp only [true_toRing, false_toRing, square_eq_one]
      ring_nf
      tauto
    · nth_rewrite 2 [B_MLong_swap]
      rw [←Bool.not_true, B_MLong_comm_overlap]
      simp only [true_toRing, false_toRing, Bool.not_true]
      ring_nf
      tauto
  · simp only [fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullSingleSpanRootPairs, singleSpanRootPairs, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [doubleSpanRelationsOfRootPair, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h
    all_goals (
      subst p
      apply mul_inv_eq_of_eq_mul
      simp only [toB3Mat, toB3Root, M,
        Fin.isValue, Int.cast_one, one_mul]
    )
    all_goals (
      rw [B_MLong_swap, ←Bool.not_false, B_MLong_MShort_comm_overlap, B_MLong_swap]
      simp only [Bool.not_false, true_toRing, false_toRing]
      ring_nf
    )
  · simp only [fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullPresentRoots, B3Large.weakPresentRoots, Set.mem_union, Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    simp only [linearityRelationsOfRoot, Set.mem_setOf_eq] at h
    rcases h with ⟨ t, u, h ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h|h|h
    all_goals (
      subst p
      simp only [toB3Mat, toB3Root, M]
      apply mul_inv_eq_of_eq_mul
      simp only [one_mul]
    )
    any_goals rw [B_MShort_mul_add]
    all_goals rw [B_MLong_mul_add]
  · simp only [definitionRelations, fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      Set.mem_iUnion] at h
    rcases h with ⟨ p, h_p, h ⟩
    subst r
    simp only [inv_mul_cancel, map_one]

end Steinberg
