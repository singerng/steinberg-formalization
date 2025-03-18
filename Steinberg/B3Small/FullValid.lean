import Steinberg.B3Small.Defs
import Steinberg.Defs.PartialChevalleyGroup
import Steinberg.Upstream.Chevalley.TypeB.TypeB

import Steinberg.Defs.Commutator

namespace Steinberg

variable {F : Type TR} [CommRing F]

open PartialChevalleySystem B3Small B3SmallPosRoot PartialChevalley ChevalleyGenerator PartialChevalleyGroup

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

theorem valid :
  ∀ r ∈ (fullB3Small F).all_rels, (FreeGroup.lift toB3Mat r) = 1 := by
  intro r h
  simp only [all_rels, Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union] at h
  rcases h with h_triv|h_sing|h_doub|h_lin
  · simp only [trivial_comm_rels, fullB3Small, fullB3SmallSystem, mk_full,
      full_trivial_commutator_pairs, trivial_commutator_pairs, Set.mem_union, Set.mem_iUnion] at h_triv
    rcases h_triv with ⟨ p, h_p, h_triv ⟩
    simp only [rels_of_trivial_commutator_of_root_pair, Set.mem_setOf_eq] at h_triv
    rcases h_triv with ⟨ t, u, h_triv ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
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
  · simp only [single_comm_rels, fullB3Small, fullB3SmallSystem, mk_full,
      full_single_commutator_pairs, single_commutator_pairs, Set.mem_union, Set.mem_iUnion] at h_sing
    rcases h_sing with ⟨ p, h_p, h_sing ⟩
    simp only [rels_of_single_commutator_of_root_pair, Set.mem_setOf_eq] at h_sing
    rcases h_sing with ⟨ t, u, h_sing ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    apply mul_inv_eq_of_eq_mul
    simp only [one_mul, toB3Mat, toB3Root, BRoot.M, BShortRoot.M, BLongRoot.M]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h|h|h|h
    all_goals (
      subst p
      simp only
    )
    any_goals (
      rw [MShort_comm, MLong_swap]
      simp only [true_toRing, false_toRing]
      ring_nf
      tauto
    )

    sorry
  · simp only [double_comm_rels, fullB3Small, fullB3SmallSystem, mk_full,
      full_double_commutator_pairs, double_commutator_pairs, Set.mem_union, Set.mem_iUnion] at h_doub
    rcases h_doub with ⟨ p, h_p, h_doub ⟩
    simp only [rels_of_double_commutator_of_root_pair, Set.mem_setOf_eq] at h_doub
    rcases h_doub with ⟨ t, u, h_doub ⟩
    subst r
    simp only [map_commutatorElement, map_inv, map_mul, FreeGroup.lift.of]
    apply mul_inv_eq_of_eq_mul
    simp only [one_mul]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h_p
    rcases h_p with h
    let ζ := toB3Root p.fst

    let Sum.inl ζ' := ζ
    subst p
    have h_ζ : ζ = p.fst := by rfl
    subst p
    have h : x := p.fst

    subst p





-- , BRoot.M, BShortRoot.M, BLongRoot.M

    -- let ζ := p.1
    -- let η := p.2.1
    -- subst p
    -- simp_all only

    sorry


    -- rw [symm_MLong_MShort_comm_overlap false]
    -- simp only [cond_false, Fin.isValue, Bool.bne_false, Bool.not_false, Bool.bne_true, neg_mul,
    --   Int.cast_one, one_mul, false_toRing, true_toRing, neg_neg]
    -- ring_nf

    -- all_goals simp only [cond_false, Bool.not_false]
  · simp only [lin_rels, fullB3Small, fullB3SmallSystem, mk_full,
      full_present_roots, B3Small.present_roots, Set.mem_union, Set.mem_iUnion] at h_lin
    rcases h_lin with ⟨ p, h_p, h_lin ⟩
    simp only [rels_of_lin_of_root, Set.mem_setOf_eq] at h_lin
    rcases h_lin with ⟨ t, u, h_lin ⟩
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
    any_goals rw [MLong_mul_add]

end Steinberg
