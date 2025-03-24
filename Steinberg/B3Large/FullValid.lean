/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.B3Large.Defs
import Steinberg.Defs.PartialChevalleyGroup
import Steinberg.Upstream.Chevalley.TypeB.TypeB

import Steinberg.Defs.Commutator

import Steinberg.Upstream.Commutator

namespace Steinberg

variable {F : Type TR} [Field F]

open PartialChevalleySystem B3Large B3LargePosRoot PartialChevalley
  ChevalleyGenerator PartialChevalleyGroup Chevalley.TypeB

def toB3Root (ζ : B3LargePosRoot) : BRoot (Fin 3) :=
  match ζ with
  | α =>     Sum.inl (BLongRoot.mk true false 0 1 (by tauto))
  | β =>     Sum.inl (BLongRoot.mk true false 1 2 (by tauto))
  | ψ =>     Sum.inr (BShortRoot.mk true 2)
  | αβ =>    Sum.inl (BLongRoot.mk true false 0 2 (by tauto))
  | βψ =>    Sum.inr (BShortRoot.mk true 1)
  | β2ψ =>   Sum.inl (BLongRoot.mk true true 1 2 (by tauto))
  | αβψ =>   Sum.inr (BShortRoot.mk true 0)
  | αβ2ψ =>  Sum.inl (BLongRoot.mk true true 0 2 (by tauto))
  | α2β2ψ => Sum.inl (BLongRoot.mk true true 0 1 (by tauto))

abbrev toB3Mat (g : ChevalleyGenerator B3LargePosRoot F) := (toB3Root g.ζ).M g.t

theorem valid :
  ∀ r ∈ (fullB3Large F).allRelations, (FreeGroup.lift toB3Mat r) = 1 := by
  intro r h
  simp only [allRelations, Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union] at h
  rcases h with h_triv|h_sing|h_doub|h_lin|h_def
  · simp only [trivialSpanRelations, fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullTrivialSpanPairs, weakTrivialSpanPairs, Set.mem_union, Set.mem_iUnion] at h_triv
    rcases h_triv with ⟨ p, h_p, h_triv ⟩
    simp only [trivialSpanRelationsOfRootPair, Set.mem_setOf_eq] at h_triv
    rcases h_triv with ⟨ t, u, h_triv ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals (
      subst p
      simp only [toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M]
    )
    any_goals (rw [MLong_MShort_comm_disjoint]; all_goals tauto)
    any_goals (rw [triv_comm_symm, MLong_MShort_comm_disjoint]; all_goals tauto) -- handle the goals where we have ⁅ MShort, MLong ⁆
    any_goals (rw [MLong_comm_disjoint]; all_goals tauto)
    any_goals (apply MLong_comm_disjoint')
  · simp only [singleSpanRelations, fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullSingleSpanRootPairs, weakSingleSpanRootPairs, Set.mem_union, Set.mem_iUnion] at h_sing
    rcases h_sing with ⟨ p, h_p, h_sing ⟩
    simp only [singleSpanRelationsOfRootPair, Set.mem_setOf_eq] at h_sing
    rcases h_sing with ⟨ t, u, h_sing ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h
    all_goals (
      subst p
      apply mul_inv_eq_of_eq_mul
      simp only [toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M,
        Fin.isValue, Int.cast_one, Int.cast_two, Int.cast_neg, one_mul]
    )
    any_goals (
      rw [MShort_comm]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )
    any_goals (
      rw [MShort_comm, MLong_swap]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )
    any_goals (
      rw [←Bool.not_false, MLong_comm_overlap]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )
    -- rearranging required, TODO: automate this
    · nth_rewrite 2 [MLong_swap]
      rw [←Bool.not_false, MLong_comm_overlap]
      ring_nf
      simp only [true_toRing, false_toRing, square_eq_one]
      ring_nf
      tauto
    · nth_rewrite 2 [MLong_swap]
      rw [←Bool.not_true, MLong_comm_overlap]
      simp only [true_toRing, false_toRing, Bool.not_true]
      ring_nf
      tauto
  · simp only [doubleSpanRelations, fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullSingleSpanRootPairs, singleSpanRootPairs, Set.mem_union, Set.mem_iUnion] at h_doub
    rcases h_doub with ⟨ p, h_p, h_doub ⟩
    simp only [doubleSpanRelationsOfRootPair, Set.mem_setOf_eq] at h_doub
    rcases h_doub with ⟨ t, u, h_doub ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h
    all_goals (
      subst p
      apply mul_inv_eq_of_eq_mul
      simp only [toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M,
        Fin.isValue, Int.cast_one, one_mul]
    )
    all_goals (
      rw [MLong_swap, ←Bool.not_false, MLong_MShort_comm_overlap, MLong_swap]
      simp only [Bool.not_false, true_toRing, false_toRing]
      ring_nf
    )
  · simp only [linearityRelations, fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      fullPresentRoots, B3Large.weakPresentRoots, Set.mem_union, Set.mem_iUnion] at h_lin
    rcases h_lin with ⟨ p, h_p, h_lin ⟩
    simp only [linearityRelationsOfRoot, Set.mem_setOf_eq] at h_lin
    rcases h_lin with ⟨ t, u, h_lin ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h|h|h
    all_goals (
      subst p
      simp only [toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M]
      apply mul_inv_eq_of_eq_mul
      simp only [one_mul]
    )
    any_goals rw [MShort_mul_add]
    all_goals rw [MLong_mul_add]
  · simp only [definitionRelations, fullB3Large, fullMk, fullB3LargeSystem, mkFull,
      Set.mem_iUnion] at h_def
    rcases h_def with ⟨ p, h_p, h_def ⟩
    subst r
    simp only [inv_mul_cancel, map_one]

end Steinberg
