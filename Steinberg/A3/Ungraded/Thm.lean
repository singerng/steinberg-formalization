/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.A3.Ungraded.Basic

import Mathlib.Algebra.Group.Basic

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

import Steinberg.Defs.Lattice

import Steinberg.Upstream.FreeGroup

/-!

  File dox.

-/

namespace Steinberg.A3.Ungraded

open Steinberg A3PosRoot PartialChevalley ChevalleyGenerator PartialChevalleyGroup

variable {R : Type TR} [Ring R]

/-! ### Definition of missing root -/
theorem def_of_αβγ : ∀ (t : R),
    ⁅ ⸨α, t⸩, ⸨βγ, 1⸩ ⁆ = ⸨αβγ, t⸩ := by
  intro t
  symm
  apply (weakA3Ungraded R).def_helper

/-! ### Derive full commutator for αβ and βγ from nonhomogeneous lift -/

theorem comm_of_αβ_βγ : trivial_commutator_of_root_pair (weakA3Ungraded R).pres_mk (αβ, βγ) := by
  sorry

declare_A3_ungraded_triv_expr_thm R αβ βγ

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

/- Pass between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms (specializes `Interchange` to the case `u=1`). -/
theorem InterchangeTrans : ∀ (t u : R),
    ⁅ ⸨α, t⸩, ⸨βγ, u⸩ ⁆ = ⁅ ⸨αβ, t⸩, ⸨γ, u⸩ ⁆ := by
  intro t u
  have := Interchange t 1 u
  rwa [one_mul, mul_one] at this

/- ⁅α,βγ⁆ forms depend only on product of coefficients. Applies `Interchange` twice. -/
theorem InterchangeRefl : ∀ (t u : R),
    ⁅ ⸨α, t * u⸩, ⸨βγ, 1⸩ ⁆ = ⁅ ⸨α, t⸩, ⸨βγ, u⸩ ⁆ := by
  intro t u
  nth_rewrite 2 [← mul_one u]
  rw [Interchange, InterchangeTrans]

/-! ### Commutator relations for (α,βγ) and (αβ,γ) via interchange relations -/

/- Commutator relation for α and βγ. -/
theorem comm_of_α_βγ : single_commutator_of_root_pair (weakA3Ungraded R).pres_mk ⟨α, βγ, αβγ, 1, (by ht)⟩ := by
  intro t u
  simp only [Int.cast_one, one_mul]
  rw [← InterchangeRefl, ← def_of_αβγ (t * u)]

declare_A3_ungraded_single_expr_thms R α βγ αβγ 0 1

/- Commutator relation for αβ and γ. -/
theorem comm_of_αβ_γ : single_commutator_of_root_pair (weakA3Ungraded R).pres_mk ⟨αβ, γ, αβγ, 1, (by ht)⟩ := by
  intro t u
  rw [← InterchangeTrans, comm_of_α_βγ]

declare_A3_ungraded_single_expr_thms R αβ γ αβγ 0 1

/-! ### More rewriting theorems -/

theorem expr_αβγ_as_α_βγ_α_βγ_one_mul : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨α, 1⸩ * ⸨βγ, t⸩ * ⸨α, -1⸩ * ⸨βγ, -t⸩ := by
  intro u
  have := expr_αβγ_as_α_βγ_α_βγ 1 u
  rwa [one_mul] at this

theorem expr_αβγ_as_α_βγ_α_βγ_mul_one : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨α, t⸩ * ⸨βγ, 1⸩ * ⸨α, -t⸩ * ⸨βγ, -1⸩ := by
  intro t
  have := expr_αβγ_as_α_βγ_α_βγ t 1
  rwa [mul_one] at this

theorem expr_αβγ_as_αβ_γ_αβ_γ_one_mul : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨αβ, 1⸩ * ⸨γ, t⸩ * ⸨αβ, -1⸩ * ⸨γ, -t⸩ := by
  intro u
  have := expr_αβγ_as_αβ_γ_αβ_γ 1 u
  rwa [one_mul] at this

theorem expand_αβγ_as_αβ_γ_αβ_γ_mul_one : ∀ (t : R),
    ⸨αβγ, t⸩ = ⸨αβ, t⸩ * ⸨γ, 1⸩ * ⸨αβ, -t⸩ * ⸨γ, -1⸩ := by
  intro t
  have := expr_αβγ_as_αβ_γ_αβ_γ t 1
  rwa [mul_one] at this

/-! ### Commutators of αβγ with other roots -/

/- α and αβγ commute. -/
theorem comm_of_α_αβγ : trivial_commutator_of_root_pair (weakA3Ungraded R).pres_mk (α, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul,
      expr_α_αβ_as_αβ_α, expr_α_γ_as_γ_α,
      expr_α_αβ_as_αβ_α, expr_α_γ_as_γ_α]

/- β and αβγ commute. -/
-- the only commutator proof where we have to do something 'interesting'
theorem comm_of_β_αβγ : trivial_commutator_of_root_pair (weakA3Ungraded R).pres_mk (β, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul,
      expr_β_αβ_as_αβ_β, expr_β_γ_as_γ_βγ_β,
      expr_β_αβ_as_αβ_β, expr_β_γ_as_βγ_γ_β,
      ← expr_αβ_βγ_as_βγ_αβ]

/- γ and αβγ commute. -/
theorem comm_of_γ_αβγ : trivial_commutator_of_root_pair (weakA3Ungraded R).pres_mk (γ, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_α_βγ_α_βγ_one_mul,
    ← expr_α_γ_as_γ_α, expr_γ_βγ_as_βγ_γ,
    ← expr_α_γ_as_γ_α, expr_γ_βγ_as_βγ_γ]

/- αβ and αβγ commute. -/
theorem comm_of_αβ_αβγ : trivial_commutator_of_root_pair (weakA3Ungraded R).pres_mk (αβ, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_α_βγ_α_βγ_one_mul,
    ← expr_α_αβ_as_αβ_α, expr_αβ_βγ_as_βγ_αβ,
    ← expr_α_αβ_as_αβ_α, expr_αβ_βγ_as_βγ_αβ]

/- βγ and αβγ commute. -/
theorem comm_of_βγ_αβγ : trivial_commutator_of_root_pair (weakA3Ungraded R).pres_mk (βγ, αβγ) := by
  intro t u
  apply triv_comm_iff_commutes.mpr
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul,
    ← expr_αβ_βγ_as_βγ_αβ, h, ← expr_γ_βγ_as_βγ_γ,
    ← expr_αβ_βγ_as_βγ_αβ, h, ← expr_γ_βγ_as_βγ_γ]

declare_A3_ungraded_triv_expr_thm R α αβγ
declare_A3_ungraded_triv_expr_thm R β αβγ
declare_A3_ungraded_triv_expr_thm R γ αβγ
declare_A3_ungraded_triv_expr_thm R αβ αβγ
declare_A3_ungraded_triv_expr_thm R βγ αβγ

/- Linearity for αβγ. -/
@[group_reassoc (attr := simp, chev_simps)]
theorem lin_of_αβγ : lin_of_root((weakA3Ungraded R).pres_mk, αβγ) := by
  intro t u
  grw [expr_αβγ_as_α_βγ_α_βγ_mul_one,
    expr_βγ_αβγ_as_αβγ_βγ,
    expr_α_αβγ_as_αβγ_α,
    expr_βγ_αβγ_as_αβγ_βγ,
    expr_αβγ_as_α_βγ_α_βγ_mul_one,
    ← neg_add, add_comm u t,
    ← expr_αβγ_as_α_βγ_α_βγ]

theorem full_rels_satisfied_in_weak_group :
  ∀ r ∈ (fullA3 R).all_rels, (weakA3Ungraded R).pres_mk r = 1 := by
  simp only [fullA3, weakA3Ungraded]
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
      simp only [rels_of_trivial_commutator_of_root_pair] at h_r
      rcases h_r with ⟨ t, u, goal ⟩
      rcases h_new with h_αβ_βγ|h_α_αβγ|h_β_αβγ|h_γ_αβγ|h_αβ_αβγ|h_βγ_αβγ
      all_goals subst p r
      · exact comm_of_αβ_βγ t u
      · exact comm_of_α_αβγ t u
      · exact comm_of_β_αβγ t u
      · exact comm_of_γ_αβγ t u
      · exact comm_of_αβ_αβγ t u
      · exact comm_of_βγ_αβγ t u
  · rcases h with h_old|h_new
    · tauto
    · right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_new
      intro r h_r
      simp only [rels_of_single_commutator_of_root_pair] at h_r
      rcases h_r with ⟨ t, u, goal ⟩
      rcases h_new with h_α_βγ|h_αβ_γ
      all_goals (
        subst p r
        simp only [map_mul, map_inv, mul_inv_eq_one]
      )
      · exact comm_of_α_βγ t u
      · exact comm_of_αβ_γ t u
  · tauto
  · rcases h with h_old|h_new
    · tauto
    · right
      simp_all only [Set.mem_singleton_iff]
      intro r h_r
      simp only [rels_of_lin_of_root] at h_r
      rcases h_r with ⟨ t, u, goal ⟩
      subst r
      simp only [map_mul, map_inv, mul_inv_eq_one]
      exact lin_of_αβγ t u
  · simp only [def_rels, Set.mem_iUnion, Set.mem_setOf_eq] at h
    rcases h with ⟨ζ, ht, h⟩
    subst p
    simp only [fullA3, full_mk, inv_mul_cancel, map_one]

end Steinberg.A3.Ungraded
