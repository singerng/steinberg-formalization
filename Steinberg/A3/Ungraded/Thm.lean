/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.A3.Ungraded.Basic

import Mathlib.Algebra.Group.Basic

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

import Steinberg.Defs.Lattice
import Mathlib.Tactic.FieldSimp

import Steinberg.Upstream.FreeGroup

/-!

  File dox.

-/

namespace Steinberg.A3.Ungraded

open Steinberg A3PosRoot PartialChevalley ChevalleyGenerator PartialChevalleyGroup

variable {R : Type TR} [Field R] (Rchar : (2 : R) ≠ 0)

/-! ### Definition of missing root -/
theorem def_of_αβγ : ∀ (t : R),
    ⁅ ⸨α, t⸩, ⸨βγ, 1⸩ ⁆ = ⸨αβγ, t⸩ := by
  intro t
  symm
  apply (weakA3GradedUngraded R).definitionProp_of_define

/-! ### Derive full commutator for αβ and βγ from nonhomogeneous lift -/

theorem reorder_α_β_α (t u v : R) (h : t + v ≠ 0) : ⸨α, t⸩ * ⸨β, u⸩ * ⸨α, v⸩ = ⸨β, u * v/(t + v)⸩ * ⸨α, t + v⸩ * ⸨β, t * u/(t + v)⸩ := by
  have : u * v / (t + v) + t * u / (t + v) = u := by
    nth_rw 2 [mul_comm]
    rw [mul_div_assoc, mul_div_assoc, ← left_distrib, div_add_div_same, add_comm]
    have : ((t + v) / (t + v)) = 1 := by
      rw [div_eq_one_iff_eq]
      exact h
    rw [this]
    exact mul_one u
  have : ⸨β, u * v / (t + v)⸩ * ⸨β, t * u / (t + v)⸩ = ⸨β, u⸩ := by
    rw [lin_of_β, this]
  rw [← this, ← mul_assoc]
  have : ⸨α, t⸩ * ⸨β, u * v / (t + v)⸩ = ⸨β, u * v / (t + v)⸩ * ⸨α, t⸩ * ⁅⸨α, -t⸩, ⸨β, -(u * v / (t + v))⸩⁆ := by
    grw [comm_right]
  rw [this]
  have : ⸨β, t * u / (t + v)⸩ * ⸨α, v⸩ = ⁅⸨α, v⸩, ⸨β, t * u / (t + v)⸩⁆⁻¹ * ⸨α, v⸩ * ⸨β, t * u / (t + v)⸩ := by
    grw [comm_left_rev]
  grw [this, comm_of_α_β]
  rw [← comm_swap, comm_of_α_β]
  chev_simp; group
  grw [id_of_αβ]

theorem reorder_β_γ_β (t u v : R) (h : t + v ≠ 0) : ⸨β, t⸩ * ⸨γ, u⸩ * ⸨β, v⸩ = ⸨γ, u * v/(t + v)⸩ * ⸨β, t + v⸩ * ⸨γ, t * u/(t + v)⸩ := by
  have : u * v / (t + v) + t * u / (t + v) = u := by
    nth_rw 2 [mul_comm]
    rw [mul_div_assoc, mul_div_assoc, ← left_distrib, div_add_div_same, add_comm]
    have : ((t + v) / (t + v)) = 1 := by
      rw [div_eq_one_iff_eq]
      exact h
    rw [this]
    exact mul_one u
  have : ⸨γ, u * v / (t + v)⸩ * ⸨γ, t * u / (t + v)⸩ = ⸨γ, u⸩ := by
    rw [lin_of_γ, this]
  rw [← this, ← mul_assoc]
  have : ⸨β, t⸩ * ⸨γ, u * v / (t + v)⸩ = ⸨γ, u * v / (t + v)⸩ * ⸨β, t⸩ * ⁅⸨β, -t⸩, ⸨γ, -(u * v / (t + v))⸩⁆ := by
    grw [comm_right]
  rw [this]
  have : ⸨γ, t * u / (t + v)⸩ * ⸨β, v⸩ = ⁅⸨β, v⸩, ⸨γ, t * u / (t + v)⸩⁆⁻¹ * ⸨β, v⸩ * ⸨γ, t * u / (t + v)⸩ := by
    grw [comm_left_rev]
  grw [this, comm_of_β_γ]
  rw [← comm_swap, comm_of_β_γ]
  chev_simp; group
  grw [id_of_βγ]

include Rchar in
theorem comm_of_αβ_βγ : trivialSpanPropOfRootPair (weakA3GradedUngraded R).project (αβ, βγ) := by
  intro t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_αβ]
    group
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, id_of_βγ]
    group
  have h59 : ⸨αβ, t⸩ = ⸨β, -1⸩ * ⸨α, t⸩ * ⸨β, 1⸩ * ⸨α, -t⸩ := by
    have : ⸨β, 1⸩ = ⸨β, -1⸩⁻¹ := by rw [inv_of_β, neg_neg]
    rw [this, ← inv_of_α, ← commutatorElement_def, ← comm_swap, comm_of_α_β, inv_of_αβ]
    chev_simp
  have h60 : ⸨βγ, u⸩ = ⸨γ, -(2*u)⸩ * ⸨β, 1/2⸩ * ⸨γ, 2*u⸩ * ⸨β, -(1/2)⸩ := by
    have : ⸨γ, 2*u⸩ = ⸨γ, -(2*u)⸩⁻¹ := by rw [inv_of_γ, neg_neg]
    rw [this, ← inv_of_β, ← commutatorElement_def, ← comm_swap, comm_of_β_γ, inv_of_βγ]
    field_simp
  have h61 : ⸨αβ, -t⸩ = ⸨β, 1/2⸩ * ⸨α, 2*t⸩ * ⸨β, -(1/2)⸩ * ⸨α, -(2*t)⸩ := by
    rw [← inv_of_α, ← inv_of_β, ← commutatorElement_def, ← comm_swap, comm_of_α_β, inv_of_αβ]
    field_simp
  have h62 : ⸨βγ, -u⸩ = ⸨γ, -u⸩ * ⸨β, -1⸩ * ⸨γ, u⸩ * ⸨β, 1⸩ := by
    have aux1 : ⸨γ, u⸩ = ⸨γ, -u⸩⁻¹ := by rw [inv_of_γ, neg_neg]
    have aux2 : ⸨β, 1⸩ = ⸨β, -1⸩⁻¹ := by rw [inv_of_β, neg_neg]
    rw [aux1, aux2, ← commutatorElement_def, ← comm_swap, comm_of_β_γ, inv_of_βγ]
    chev_simp
  have h63 : ⸨α, -t⸩ * ⸨β, 1/2⸩ * ⸨α, 2*t⸩ = ⸨β, 1⸩ * ⸨α, t⸩ * ⸨β, -(1/2)⸩ := by
    rw [reorder_α_β_α]
    ring_nf; field_simp
    have aux1 : t * 2 / (2 * t) = 1 := by
      rw [div_eq_one_iff_eq]
      · exact mul_comm t 2
      · rw [mul_ne_zero_iff]
        exact ⟨Rchar, ht⟩
    have aux2 : -t / (2 * t) = -1/2 := by
      field_simp; exact mul_comm t 2
    rw [aux1, aux2]
    simp only [two_mul, neg_add_cancel_left]; exact ht
  have h64 : ⸨γ, 2*u⸩ * ⸨β, -(1/2)⸩ * ⸨γ, -u⸩ = ⸨β, 1/2⸩ * ⸨γ, u⸩ * ⸨β, -1⸩ := by
    rw [reorder_β_γ_β]
    ring_nf; field_simp
    have aux1 : -(u * 2) / (-2 + 1) = u * 2 := by
      apply div_eq_of_eq_mul
      group
      simp only [neg_ne_zero, neg_neg, ne_eq, one_ne_zero, not_false_eq_true]
      group
    have aux2 : u / (-2 + 1) = -u := by group
    rw [aux1, aux2]
    group
    field_simp
    group
    simp only [neg_eq_zero, one_ne_zero, not_false_eq_true]
  have h65 : ⸨β, 1⸩ * ⸨γ, -(2*u)⸩ * ⸨β, 1⸩ = ⸨γ, -u⸩ * ⸨β, 2⸩ * ⸨γ, -u⸩ := by
    rw [reorder_β_γ_β]
    ring_nf; field_simp; rw [one_add_one_eq_two]; exact Rchar
  have h66 : ⸨β, -1⸩ * ⸨α, -(2*t)⸩ * ⸨β, -1⸩ = ⸨α, -t⸩ * ⸨β, -2⸩ * ⸨α, -t⸩ := by
    rw [reorder_α_β_α]
    ring_nf; field_simp; group; field_simp
  grw [commutatorElement_def, inv_of_αβ, inv_of_βγ, h60, h61]
  grw [h59, h62]
  have α_γ_commute := fun t u => triv_comm_iff_commutes.1 (comm_of_α_γ (R := R) t u)
  have aux1 := α_γ_commute (-t) (-(2 * u))
  have aux2 := α_γ_commute (2 * t) (2 * u)
  have aux3 := α_γ_commute (-(2 * t)) (-u)
  have aux4 := α_γ_commute t (-u)
  have aux5 := α_γ_commute (-t) u
  grw [aux1, ← aux2, aux3, h63, h64, h65, h66, ← aux4, ← aux5, aux4, aux5]

include Rchar in
declare_A3_ungraded_trivial_span_expr_thm R αβ βγ

/-! ### Further useful identities (roughly GENERIC) -/

/- Rewrite β⬝γ as γ⬝βγ⬝β. -/
@[group_reassoc]
theorem expr_β_γ_as_γ_βγ_β : ∀ (t u : R),
    reorder_mid(⸨β, t⸩, ⸨γ, u⸩, ⸨βγ, t * u⸩) := by
  intro t u
  have := comm_of_β_γ t u
  chev_simp at this
  rw [← this, comm_mid, inv_of_γ, comm_of_β_γ]
  grw [comm_of_β_γ]

/-! ### Interchange theorems between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms -/

/- Interchange between ⁅α, βγ⁆ and ⁅αβ, γ⁆, "trading" a single degree : Deg 1 and scalar u : R. -/
include Rchar in
theorem Interchange : ∀ (t u v : R),
     ⁅ ⸨α, t⸩, ⸨βγ, u * v⸩ ⁆ = ⁅ ⸨αβ, t * u⸩, ⸨γ, v⸩ ⁆ := by
  intro t u v
  apply eq_comm_of_reorder_left
  grw [expr_βγ_as_β_γ_β_γ,
    expr_α_β_as_αβ_β_α, expr_α_γ_as_γ_α,
    expr_α_β_as_αβ_β_α, expr_α_γ_as_γ_α,
    expr_β_γ_as_βγ_γ_β,
    expr_β_αβ_as_αβ_β,
    ← expr_γ_βγ_as_βγ_γ,
    ← expr_αβ_βγ_as_βγ_αβ,
    commutatorElement_def,
    expr_β_γ_as_βγ_γ_β,
    ← expr_γ_βγ_as_βγ_γ]
  exact Rchar

/- Pass between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms (specializes `Interchange` to the case `u=1`). -/
include Rchar in
theorem InterchangeTrans : ∀ (t u : R),
    ⁅ ⸨α, t⸩, ⸨βγ, u⸩ ⁆ = ⁅ ⸨αβ, t⸩, ⸨γ, u⸩ ⁆ := by
  intro t u
  have := Interchange Rchar t 1 u
  rwa [one_mul, mul_one] at this

/- ⁅α,βγ⁆ forms depend only on product of coefficients. Applies `Interchange` twice. -/
include Rchar in
theorem InterchangeRefl : ∀ (t u : R),
    ⁅ ⸨α, t * u⸩, ⸨βγ, 1⸩ ⁆ = ⁅ ⸨α, t⸩, ⸨βγ, u⸩ ⁆ := by
  intro t u
  nth_rewrite 2 [← mul_one u]
  rw [Interchange, InterchangeTrans]
  repeat assumption

/-! ### Commutator relations for (α,βγ) and (αβ,γ) via interchange relations -/

/- Commutator relation for α and βγ. -/
include Rchar in
theorem comm_of_α_βγ : singleCommutatorPropOfRootPair (weakA3GradedUngraded R).project ⟨α, βγ, αβγ, 1, (by ht)⟩ := by
  intro t u
  simp only [Int.cast_one, one_mul]
  rw [← InterchangeRefl, ← def_of_αβγ (t * u)]
  assumption

include Rchar in
declare_A3_ungraded_single_span_expr_thms R α βγ αβγ 0 1

/- Commutator relation for αβ and γ. -/
include Rchar in
theorem comm_of_αβ_γ : singleCommutatorPropOfRootPair (weakA3GradedUngraded R).project ⟨αβ, γ, αβγ, 1, (by ht)⟩ := by
  intro t u
  rw [← InterchangeTrans, comm_of_α_βγ]
  repeat assumption

include Rchar in
declare_A3_ungraded_single_span_expr_thms R αβ γ αβγ 0 1

/-! ### More rewriting theorems -/

include Rchar in
theorem expr_αβγ_as_α_βγ_α_βγ_one_mul : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨α, 1⸩ * ⸨βγ, t⸩ * ⸨α, -1⸩ * ⸨βγ, -t⸩ := by
  intro u
  have := expr_αβγ_as_α_βγ_α_βγ Rchar 1 u
  rwa [one_mul] at this

include Rchar in
theorem expr_αβγ_as_α_βγ_α_βγ_mul_one : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨α, t⸩ * ⸨βγ, 1⸩ * ⸨α, -t⸩ * ⸨βγ, -1⸩ := by
  intro t
  have := expr_αβγ_as_α_βγ_α_βγ Rchar t 1
  rwa [mul_one] at this

include Rchar in
theorem expr_αβγ_as_αβ_γ_αβ_γ_one_mul : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨αβ, 1⸩ * ⸨γ, t⸩ * ⸨αβ, -1⸩ * ⸨γ, -t⸩ := by
  intro u
  have := expr_αβγ_as_αβ_γ_αβ_γ Rchar 1 u
  rwa [one_mul] at this

include Rchar in
theorem expand_αβγ_as_αβ_γ_αβ_γ_mul_one : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨αβ, t⸩ * ⸨γ, 1⸩ * ⸨αβ, -t⸩ * ⸨γ, -1⸩ := by
  intro t
  have := expr_αβγ_as_αβ_γ_αβ_γ Rchar t 1
  rwa [mul_one] at this

/-! ### Commutators of αβγ with other roots -/

/- α and αβγ commute. -/
include Rchar in
theorem comm_of_α_αβγ : trivialSpanPropOfRootPair (weakA3GradedUngraded R).project (α, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul,
      expr_α_αβ_as_αβ_α, expr_α_γ_as_γ_α,
      expr_α_αβ_as_αβ_α, expr_α_γ_as_γ_α]
  assumption

/- β and αβγ commute. -/
-- the only commutator proof where we have to do something 'interesting'
include Rchar in
theorem comm_of_β_αβγ : trivialSpanPropOfRootPair (weakA3GradedUngraded R).project (β, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul,
      expr_β_αβ_as_αβ_β, expr_β_γ_as_γ_βγ_β,
      expr_β_αβ_as_αβ_β, expr_β_γ_as_βγ_γ_β,
      ← expr_αβ_βγ_as_βγ_αβ]
  repeat assumption

/- γ and αβγ commute. -/
include Rchar in
theorem comm_of_γ_αβγ : trivialSpanPropOfRootPair (weakA3GradedUngraded R).project (γ, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_α_βγ_α_βγ_one_mul,
    ← expr_α_γ_as_γ_α, expr_γ_βγ_as_βγ_γ,
    ← expr_α_γ_as_γ_α, expr_γ_βγ_as_βγ_γ]
  repeat assumption

/- αβ and αβγ commute. -/
include Rchar in
theorem comm_of_αβ_αβγ : trivialSpanPropOfRootPair (weakA3GradedUngraded R).project (αβ, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_α_βγ_α_βγ_one_mul,
    ← expr_α_αβ_as_αβ_α, expr_αβ_βγ_as_βγ_αβ,
    ← expr_α_αβ_as_αβ_α, expr_αβ_βγ_as_βγ_αβ]
  repeat assumption

/- βγ and αβγ commute. -/
include Rchar in
theorem comm_of_βγ_αβγ : trivialSpanPropOfRootPair (weakA3GradedUngraded R).project (βγ, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul,
    ← expr_αβ_βγ_as_βγ_αβ, h, ← expr_γ_βγ_as_βγ_γ,
    ← expr_αβ_βγ_as_βγ_αβ, h, ← expr_γ_βγ_as_βγ_γ]
  repeat assumption

include Rchar
declare_A3_ungraded_trivial_span_expr_thm R α αβγ
declare_A3_ungraded_trivial_span_expr_thm R β αβγ
declare_A3_ungraded_trivial_span_expr_thm R γ αβγ
declare_A3_ungraded_trivial_span_expr_thm R αβ αβγ
declare_A3_ungraded_trivial_span_expr_thm R βγ αβγ
omit Rchar

/- Linearity for αβγ. -/
include Rchar in
@[group_reassoc (attr := simp, chev_simps)]
theorem lin_of_αβγ : lin_of_root((weakA3GradedUngraded R).project, αβγ) := by
  intro t u
  grw [expr_αβγ_as_α_βγ_α_βγ_mul_one,
    expr_βγ_αβγ_as_αβγ_βγ,
    expr_α_αβγ_as_αβγ_α,
    expr_βγ_αβγ_as_αβγ_βγ,
    expr_αβγ_as_α_βγ_α_βγ_mul_one,
    ← neg_add, add_comm u t,
    ← expr_αβγ_as_α_βγ_α_βγ]
  repeat assumption

include Rchar in
theorem full_rels_satisfied_in_weak_group :
  ∀ r ∈ (fullA3 R).allRelations, (weakA3GradedUngraded R).project r = 1 := by
  simp only [fullA3, weakA3GradedUngraded]
  apply PartialChevalleyGroup.injection
  all_goals (
    intro p h
    simp only at h
  )
  · rcases h with h_old|h_new
    · tauto
    · right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_new
      intro r h_r
      simp only [trivialSpanRelationsOfRootPair] at h_r
      rcases h_r with ⟨ t, u, goal ⟩
      rcases h_new with h_αβ_βγ|h_α_αβγ|h_β_αβγ|h_γ_αβγ|h_αβ_αβγ|h_βγ_αβγ
      all_goals subst p r
      · exact comm_of_αβ_βγ Rchar t u
      · exact comm_of_α_αβγ Rchar t u
      · exact comm_of_β_αβγ Rchar t u
      · exact comm_of_γ_αβγ Rchar t u
      · exact comm_of_αβ_αβγ Rchar t u
      · exact comm_of_βγ_αβγ Rchar t u
  · rcases h with h_old|h_new
    · tauto
    · right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_new
      intro r h_r
      simp only [singleSpanRelationsOfRootPair] at h_r
      rcases h_r with ⟨ t, u, goal ⟩
      rcases h_new with h_α_βγ|h_αβ_γ
      all_goals (
        subst p r
        simp only [map_mul, map_inv, mul_inv_eq_one]
      )
      · exact comm_of_α_βγ Rchar t u
      · exact comm_of_αβ_γ Rchar t u
  · tauto
  · rcases h with h_old|h_new
    · tauto
    · right
      simp_all only [Set.mem_singleton_iff]
      intro r h_r
      simp only [linearityRelationsOfRoot] at h_r
      rcases h_r with ⟨ t, u, goal ⟩
      subst r
      simp only [map_mul, map_inv, mul_inv_eq_one]
      exact lin_of_αβγ Rchar t u
  · simp only [definitionRelations, Set.mem_iUnion, Set.mem_setOf_eq] at h
    rcases h with ⟨ζ, ht, h⟩
    subst p
    simp only [fullA3, fullMk, inv_mul_cancel, map_one]

end Steinberg.A3.Ungraded
