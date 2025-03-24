/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.B3Large.Defs

namespace Steinberg.B3Large

open Steinberg B3Large PartialChevalley PartialChevalleySystem ChevalleyGenerator B3LargePosRoot

variable {F : Type TF} [Field F] (Fchar : (2 : F) ≠ 0)

set_option hygiene false in
/-- Shorthand for building group elements from a root and ring element. -/
scoped notation (priority:=high) "⸨" ζ ", " t "⸩" =>
  (fullB3Large F).project {ζ, t}

-- Instantiate macros for ungraded case

macro "declare_B3Large_ungraded_lin_id_inv_thms" F:term:arg root:term:arg : command =>
  `(command| declare_ungraded_lin_id_inv_thms fullB3Large $F $root)

macro "declare_B3Large_ungraded_trivial_span_expr_thm" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_ungraded_trivial_span_expr_thm fullB3Large $F $r₁ $r₂)

macro "declare_B3Large_ungraded_trivial_span_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_ungraded_trivial_span_of_root_pair_thms fullB3Large $F $r₁ $r₂)

macro "declare_B3Large_ungraded_single_span_expr_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg isNeg:num n:num : command =>
  `(command| declare_ungraded_single_span_expr_thms fullB3Large $F $r₁ $r₂ $r₃ $isNeg $n)

macro "declare_B3Large_ungraded_single_span_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg isNeg:num n:num : command =>
  `(command| declare_ungraded_single_span_of_root_pair_thms fullB3Large $F $r₁ $r₂ $r₃ $isNeg $n)


-- Declare relations

declare_B3Large_ungraded_lin_id_inv_thms F α
declare_B3Large_ungraded_lin_id_inv_thms F β
declare_B3Large_ungraded_lin_id_inv_thms F ψ
declare_B3Large_ungraded_lin_id_inv_thms F αβ
declare_B3Large_ungraded_lin_id_inv_thms F βψ
declare_B3Large_ungraded_lin_id_inv_thms F β2ψ
declare_B3Large_ungraded_lin_id_inv_thms F αβψ
declare_B3Large_ungraded_lin_id_inv_thms F αβ2ψ
declare_B3Large_ungraded_lin_id_inv_thms F α2β2ψ

declare_B3Large_ungraded_trivial_span_of_root_pair_thms F αβ2ψ α2β2ψ
declare_B3Large_ungraded_trivial_span_of_root_pair_thms F βψ αβ2ψ
declare_B3Large_ungraded_trivial_span_of_root_pair_thms F β2ψ αβψ
declare_B3Large_ungraded_trivial_span_of_root_pair_thms F β2ψ αβ2ψ
declare_B3Large_ungraded_trivial_span_of_root_pair_thms F ψ α2β2ψ
declare_B3Large_ungraded_trivial_span_of_root_pair_thms F αβ α2β2ψ

declare_B3Large_ungraded_single_span_of_root_pair_thms F αβψ ψ αβ2ψ 1 2
declare_B3Large_ungraded_single_span_of_root_pair_thms F α β2ψ αβ2ψ 0 1
declare_B3Large_ungraded_single_span_of_root_pair_thms F αβ β2ψ α2β2ψ 1 1
declare_B3Large_ungraded_single_span_of_root_pair_thms F αβψ βψ α2β2ψ 1 2
declare_B3Large_ungraded_single_span_of_root_pair_thms F αβ2ψ β α2β2ψ 1 1

theorem comm_of_α_βψ : doubleSpanPropOfRootPair (fullB3Large F).project ⟨α, βψ, αβψ, α2β2ψ, 1, 1, by ht, by ht⟩ :=
  (fullB3Large F).doubleSpanProp_of_mem_doubleSpanRootPairs ⟨α, βψ, αβψ, α2β2ψ, 1, 1, by ht, by ht⟩
  (by simp only [fullB3Large, PartialChevalleyGroup.fullMk, doubleCommutatorRootPairs, fullB3LargeSystem, mkFull, fullDoubleSpanRootPairs]; tauto)

theorem comm_of_αβ_ψ : doubleSpanPropOfRootPair (fullB3Large F).project ⟨αβ, ψ, αβψ, αβ2ψ, 1, 1, by ht, by ht⟩ :=
  (fullB3Large F).doubleSpanProp_of_mem_doubleSpanRootPairs ⟨αβ, ψ, αβψ, αβ2ψ, 1, 1, by ht, by ht⟩
  (by simp only [fullB3Large, PartialChevalleyGroup.fullMk, doubleCommutatorRootPairs, fullB3LargeSystem, mkFull, fullDoubleSpanRootPairs]; tauto)

include Fchar
theorem Fchar4 : (4 : F) ≠ 0 := by
  have : (4 : F) = 2 * 2 := by ring_nf
  rw [this]
  exact mul_ne_zero Fchar Fchar

theorem helper1 (t u : F) : ⸨ψ, -(u / 2)⸩ * ⸨αβ, t⸩ * ⸨ψ, u⸩ * ⸨αβ, -t⸩ * ⸨ψ, -(u / 2)⸩ = ⸨αβψ, t * u⸩ := by
  symm
  have : ⸨ψ, -(u/2)⸩ * ⸨αβ, t⸩ * ⸨ψ, u⸩ * ⸨αβ, -t⸩ * ⸨ψ, -(u/2)⸩ = ⸨αβ, t⸩ ⋆ ⸨ψ, u/2⸩ := by
    unfold starCommutator_def
    simp only [inv_of_ψ, inv_of_αβ, lin_of_ψ, pow_two]
    field_simp
    ring_nf
    field_simp
  rw [this]
  apply starCommutator_helper ⸨αβ2ψ, t * u^2⸩
  · rw [pow_two, lin_of_ψ, comm_of_αβ_ψ]
    have := Fchar4 Fchar
    field_simp
    ring_nf
    field_simp
  · rw [inv_of_αβψ, comm_of_αβψ_ψ]
    field_simp
    ring_nf
    field_simp

theorem helper2 (t u : F) : ⸨βψ, -(u / 2)⸩ * ⸨α, t⸩ * ⸨βψ, u⸩ * ⸨α, -t⸩ * ⸨βψ, -(u / 2)⸩ = ⸨αβψ, t * u⸩ := by
  symm
  have : ⸨βψ, -(u / 2)⸩ * ⸨α, t⸩ * ⸨βψ, u⸩ * ⸨α, -t⸩ * ⸨βψ, -(u / 2)⸩ = ⸨α, t⸩ ⋆ ⸨βψ, u/2⸩ := by
    unfold starCommutator_def
    simp only [inv_of_βψ, inv_of_α, lin_of_βψ, pow_two]
    field_simp
    ring_nf
    field_simp
  rw [this]
  apply starCommutator_helper ⸨α2β2ψ, t * u^2⸩
  · rw [pow_two, lin_of_βψ, comm_of_α_βψ]
    have := Fchar4 Fchar
    field_simp
    ring_nf
    field_simp
  · rw [inv_of_αβψ, comm_of_αβψ_βψ]
    field_simp
    ring_nf
    field_simp

-- include Fchar in
theorem valid_of_hom_lifted (F : Type TF) [Field F] (Fchar : (2 : F) ≠ 0) :
  ∀ S ∈ hom_lifted_sets F, ∃ r : FreeGroup (ChevalleyGenerator B3LargePosRoot F), S = hom_lift_set r ∧ (fullB3Large F).project r = 1 := by
  intro S h_S
  simp only [hom_lifted_sets, hom_lift_base_set] at h_S
  simp only [Set.mem_image] at h_S
  rcases h_S with ⟨ r, h_r, h ⟩
  use r
  subst S
  constructor
  tauto
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at h_r
  rcases h_r with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst r
  · simp only [base_rel_of_hom_lift_of_interchange_of_αβψ]
    simp only [map_mul, map_inv]
    apply mul_inv_eq_one.mpr
    chev_simp
    grw [helper1 Fchar, helper2 Fchar]
  · simp only [base_rel_of_hom_lift_of_doub_of_αβψ]
    simp only [map_mul, map_inv, map_one, neg_div]
    apply mul_inv_eq_one.mpr
    have : ⸨ψ, -1⸩ = ⸨ψ, -(2 / 2)⸩ := by field_simp
    rw [this]
    grw [helper1 Fchar, helper1 Fchar, helper1 Fchar]
    ring_nf
  · simp only [base_rel_of_hom_lift_of_interchange_of_αβ2ψ]
    simp only [map_commutatorElement, map_mul, map_inv, neg_div]
    apply mul_inv_eq_one.mpr
    grw [helper1 Fchar]
    grw [comm_of_αβψ_ψ, comm_of_α_β2ψ]
  · simp only [base_rel_of_hom_lift_of_comm_of_βψ_α_β2ψ]
    simp only [map_commutatorElement]
    grw [comm_of_α_β2ψ, comm_of_βψ_αβ2ψ]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_a]
    simp only [map_mul, map_commutatorElement]
    have : ⁅⸨β2ψ, -1⸩, ⸨α, -1⸩⁆ = ⸨αβ2ψ, 1⸩⁻¹ := by
      rw [← comm_swap, comm_of_α_β2ψ]
      field_simp
    grw [comm_of_α_β2ψ, this]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_b]
    simp only [map_mul]
    grw [comm_of_α_β2ψ, comm_of_α_β2ψ, comm_of_α_β2ψ]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_c]
    simp only [map_mul, map_commutatorElement]
    have : ⁅⸨β2ψ, 2⸩, ⸨α, 1⸩⁆ = ⸨αβ2ψ, 2⸩⁻¹ := by
      rw [← comm_swap, comm_of_α_β2ψ]
      field_simp
    grw [comm_of_α_β2ψ, this]
    ring_nf
    exact id_of_αβ2ψ
  · simp only [base_rel_of_hom_lift_of_comm_of_β2ψ_αβψ]
    simp only [map_commutatorElement, map_mul, neg_div]
    grw [helper1 Fchar, comm_of_β2ψ_αβψ]
  · simp only [base_rel_of_hom_lift_of_interchange_of_α2β2ψ_a]
    simp only [map_commutatorElement, map_mul, neg_div]
    have : ⁅⸨βψ, 1⸩, ⸨αβψ, 1⸩⁆ = ⸨α2β2ψ, 2⸩ := by
      rw [← comm_swap, comm_of_αβψ_βψ]
      norm_num
    chev_simp
    grw [helper1 Fchar, comm_of_αβ_β2ψ, this, this]
  · simp only [base_rel_of_hom_lift_of_interchange_of_α2β2ψ_b]
    simp only [map_commutatorElement, map_mul, map_inv, neg_div]
    have : ⁅⸨β, 1⸩, ⸨αβ2ψ, 2⸩⁆ = ⸨α2β2ψ, 2⸩ := by
      rw [← comm_swap, comm_of_αβ2ψ_β]
      norm_num
    grw [helper1 Fchar, comm_of_αβψ_βψ, comm_of_α_β2ψ, this, this]
  · grw [base_rel_of_hom_lift_of_comm_of_ψ_αβ_β2ψ]
    grw [comm_of_αβ_β2ψ, comm_of_ψ_α2β2ψ]
  · simp only [base_rel_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_a]
    simp only [map_commutatorElement]
    grw [comm_of_αβ_β2ψ, comm_of_αβ_α2β2ψ]
  · simp only [base_rel_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_b]
    simp only [map_commutatorElement]
    grw [comm_of_αβ_β2ψ, comm_of_αβ_α2β2ψ]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a]
    simp only [map_mul, map_inv]
    have : ⁅⸨β2ψ, -1⸩, ⸨αβ, -1⸩⁆ = ⸨α2β2ψ, 1⸩ := by
      rw [← comm_swap, comm_of_αβ_β2ψ]
      norm_num
    grw [comm_of_αβ_β2ψ, comm_of_αβ_β2ψ, this, this]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b]
    simp only [map_mul, map_commutatorElement]
    grw [comm_of_αβ_β2ψ, comm_of_αβ_β2ψ]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c]
    simp only [map_mul, map_commutatorElement]
    have : ⁅⸨β2ψ, 1⸩, ⸨αβ, 2⸩⁆ = ⸨α2β2ψ, 2⸩ := by
      rw [← comm_swap, comm_of_αβ_β2ψ]
      norm_num
    grw [comm_of_αβ_β2ψ, this]
    ring_nf; exact id_of_α2β2ψ
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a]
    simp only [map_mul, map_commutatorElement]
    have : ⁅⸨β, 1⸩, ⸨αβ2ψ, 1⸩⁆ = ⸨α2β2ψ, 1⸩ := by
      rw [← comm_swap, comm_of_αβ2ψ_β]
      norm_num
    grw [comm_of_α_β2ψ, comm_of_α_β2ψ, this, comm_of_αβ2ψ_β]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b]
    have aux1 : ⁅⸨β, -1⸩, ⸨αβ2ψ, 1⸩⁆ = ⸨α2β2ψ, -1⸩ := by
      rw [← comm_swap, comm_of_αβ2ψ_β]
      norm_num
    have aux2 : ⁅⸨β, 1⸩, ⸨αβ2ψ, 1⸩⁆ = ⸨α2β2ψ, 1⸩ := by
      rw [← comm_swap, comm_of_αβ2ψ_β]
      norm_num
    grw [comm_of_α_β2ψ, comm_of_α_β2ψ, comm_of_αβ2ψ_β, aux1, aux2]
  · simp only [base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c]
    have : ⁅⸨β, 1⸩, ⸨αβ2ψ, 1⸩⁆ = ⸨α2β2ψ, 1⸩ := by
      rw [← comm_swap, comm_of_αβ2ψ_β]
      norm_num
    grw [comm_of_α_β2ψ, comm_of_α_β2ψ, comm_of_αβ2ψ_β, this, this]
    norm_num
  · simp only [base_rel_of_hom_lift_of_comm_of_βψ_αβ2ψ]
    simp only [map_commutatorElement]
    grw [comm_of_α_β2ψ, comm_of_βψ_αβ2ψ]
  · simp only [base_rel_of_hom_lift_of_comm_of_β2ψ_αβ2ψ]
    simp only [map_commutatorElement]
    grw [comm_of_α_β2ψ, comm_of_β2ψ_αβ2ψ]
