import Steinberg.B3Large.Basic

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

import Steinberg.Defs.Lattice
import Steinberg.Defs.Commutator
import Steinberg.Defs.ReflDeg

import Steinberg.Upstream.FreeGroup


namespace Steinberg.B3Large

open Steinberg B3LargePosRoot GradedPartialChevalley GradedChevalleyGenerator GradedPartialChevalleyGroup ReflDeg

variable {F : Type TF} [Field F] (Fchar : (2 : F) ≠ 0)
variable (F_sum_of_squares : ∀ (a : F), ∃ (x y : F), a = x^2 + y^2)

theorem def_of_αβψ : forall_i_t αβψ,
  {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2 *
  {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1 *
  {βψ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 *
  {α, (split_3_into_1_2 i hi).1, -t}'(correct_of_split_3_into_1_2 i hi).1 *
  {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2
    = {αβψ, i, t} := by
  intro i hi t
  apply GradedPartialChevalleyGroup.helper
  apply (weakB3Large F).def_helper rels_of_def_of_αβψ
  · simp only [weakB3Large, def_sets]
    tauto
  · exists i, hi, t

theorem def_of_αβ2ψ : forall_i_t αβ2ψ,
    ⁅ ({α, (split_4_into_1_3 i hi).1, t}'(correct_of_split_4_into_1_3 i hi).1),
      ({β2ψ, (split_4_into_1_3 i hi).2, 1}'(correct_of_split_4_into_1_3 i hi).2)
    ⁆ = {αβ2ψ, i, t} := by
  intro i hi t
  apply GradedPartialChevalleyGroup.helper
  apply (weakB3Large F).def_helper rels_of_def_of_αβ2ψ
  · simp only [weakB3Large, def_sets]
    tauto
  · exists i, hi, t

theorem def_of_α2β2ψ : forall_i_t α2β2ψ,
    ⁅ ({αβ, (split_5_into_2_3 i hi).1, t}'(correct_of_split_5_into_2_3 i hi).1),
      ({β2ψ, (split_5_into_2_3 i hi).2, 1}'(correct_of_split_5_into_2_3 i hi).2)
    ⁆ = {α2β2ψ, i, -t} := by
  intro i hi t
  apply GradedPartialChevalleyGroup.helper
  apply (weakB3Large F).def_helper rels_of_def_of_α2β2ψ
  · simp only [weakB3Large, def_sets]
    tauto
  · exists i, hi, t

/-! ### Nonhomogeneous lift -/

-- 8.81
theorem raw_nonhomog_lift_of_comm_of_αβ_βψ : ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}
    , {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} ⁆
    = 1 := by
  hom_tac rels_of_nonhomog_lift_of_comm_of_αβ_βψ [t₁, t₀, u₁, u₀, v₁, v₀]

-- 8.82
theorem raw_nonhomog_lift_of_comm_of_α_α2β2ψ : ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {α, 1, t₁} * {α, 0, t₀},
      ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
        {β2ψ, 3, u₁ * v₁^2} * {β2ψ, 2, u₀ * v₁^2 + 2 * u₁ * v₀ * v₁}
          * {β2ψ, 1, u₁ * v₀^2 + 2 * u₀ * v₀ * v₁} * {β2ψ, 0, u₀ * v₀^2} ⁆⁆ = 1 := by
  hom_tac rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ [t₁, t₀, u₁, u₀, v₁, v₀]

/-! ### Homogeneous lift -/

-- 8.83
theorem raw_hom_lift_of_interchange_of_αβψ : forall_ijk_tuv,
    {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} =
    {βψ, j + k, -u * v / 2} * {α, i, t} * {βψ, j + k, u * v} * {α, i, -t} * {βψ, j + k, -u * v / 2} := by
  hom_tac rels_of_hom_lift_of_interchange_of_αβψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.84
theorem raw_hom_lift_of_doub_of_αβψ : forall_ik_tuv αβ ψ,
    {ψ, k, -v / 2} * {αβ, i, t * u} * {ψ, k, v} * {αβ, i, -t * u} * {ψ, k, -v / 2} *
    {ψ, k, -v / 2} * {αβ, i, t * u} * {ψ, k, v} * {αβ, i, -t * u} * {ψ, k, -v / 2} =
    {ψ, k, -v} * {αβ, i, t * u} * {ψ, k, 2 * v} * {αβ, i, -t * u} * {ψ, k, -v} := by
  hom_tac rels_of_hom_lift_of_doub_of_αβψ [i, k, hi, hk, t, u, v]

-- 8.85
theorem raw_hom_lift_of_interchange_of_αβ2ψ : forall_ijk_tuv,
    ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
      {ψ, k, v} ⁆
      = ⁅ {α, i, t}, {β2ψ, j + 2 * k, -2 * u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_interchange_of_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.86
theorem raw_hom_lift_of_comm_of_βψ_α_β2ψ : forall_ijk_tuv,
    ⁅ {βψ, j + k, u * v}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_βψ_α_β2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.87a
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_a : forall_ijk_tuv,
    ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {α, i, -t}, {β2ψ, j + 2 * k, -u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.87b
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_b : forall_ijk_tuv,
    ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {α, i, t}, {β2ψ, j + 2 * k, -u * v^2} ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.87c
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_c : forall_ijk_tuv,
    ⁅ {α, i, t} , {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅{α, i, t}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.88
theorem raw_hom_lift_of_comm_of_β2ψ_αβψ : forall_ijk_tuv,
    ⁅ {β2ψ, j + 2 * k, u * v^2},
      {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_β2ψ_αβψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.89a
theorem raw_hom_lift_of_interchange_of_α2β2ψ_a : forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆
      = ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
          {βψ, j + k, u * v} ⁆ := by
  hom_tac rels_of_hom_lift_of_interchange_of_α2β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.89b
theorem raw_hom_lift_of_interchange_of_α2β2ψ_b : forall_ijk_tuv,
    ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
      {βψ, j + k, u * v} ⁆
      = ⁅ ⁅ {α, i, t}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆, {β, j, u} ⁆ := by
  hom_tac rels_of_hom_lift_of_interchange_of_α2β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.90
theorem raw_hom_lift_of_comm_of_ψ_αβ_β2ψ : forall_ijk_tuv,
    ⁅ {ψ, k, v}, ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_ψ_αβ_β2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.91a
theorem raw_hom_lift_of_comm_of_αβ_αβ_β2ψ_a : forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.91b
theorem raw_hom_lift_of_comm_of_αβ_αβ_β2ψ_b : forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.92a
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_a : forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, -u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.92b
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_b : forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.92c
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_c : forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {αβ, i + j, 2 * t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.93a
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_a : forall_ijk_tuv,
    ⁅ {β, j, u},
      ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
      = ⁅ {β, j, -u}, ⁅ {α, i, -t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.93b
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_b : forall_ijk_tuv,
    ⁅ {β, j, u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
    * ⁅ {β, j, -u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.93c
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_c : forall_ijk_tuv,
    ⁅ {β, j, u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
    * ⁅ {β, j, u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
      = ⁅ {β, j, 2 * u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.94
theorem raw_hom_lift_of_comm_of_βψ_αβ2ψ : forall_ijk_tuv,
    ⁅ {βψ, j + k, u * v}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_βψ_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.95
theorem raw_hom_lift_of_comm_of_β2ψ_αβ2ψ : forall_ijk_tuv,
    ⁅ {β2ψ, j + 2 * k, u * v^2}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_β2ψ_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

theorem refl_of_lifted :
  ∀ S ∈ lifted_sets F,
    ∀ r ∈ S, (weakB3Large F).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [lifted_sets]
  intro s hs r hr

  sorry

theorem refl_of_def : ∀ S ∈ def_sets F, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  intro s hs r hr
  simp_all only [def_sets, rels_of_def_of_αβψ, rels_of_def_of_αβ2ψ, rels_of_def_of_α2β2ψ]
  rcases hs with hs | hs | hs
  · rcases hs
    rcases hr with ⟨i, hi, t, rfl⟩
    chev_simp [split_3_into_1_2]
    exists (αβψ.height - i), (by omega), t
    split
    all_goals (simp only; congr)
  · rcases hs
    rcases hr with ⟨i, hi, t, rfl⟩
    chev_simp [split_4_into_1_3]
    exists (αβ2ψ.height - i), (by omega), t
    split
    all_goals (simp only; congr)
    stop -- Ummmm what...
    sorry
  · rcases hs
    rcases hr with ⟨i, hi, t, rfl⟩
    chev_simp [split_5_into_2_3]
    exists (α2β2ψ.height - i), (by omega), t
    split
    all_goals (simp only; congr)


theorem b3large_valid : ReflDeg.refl_valid (weakB3Large F) :=
  ⟨refl_of_lifted, refl_of_def⟩

include Fchar

-- 8.108
theorem expr_βψ_as_ψ_β_ψ_β_ψ :
  forall_ij_tu 1 1,
    {βψ, i + j, t * u} = {ψ, i, -t/2} * {β, j, u} * {ψ, i, t} * {β, j, -u} * {ψ, i, -t/2} := by
  intro i j hi hj t u
  have hij : i + j ≤ βψ.height := by ht
  rw [← mul_inv_eq_iff_eq_mul]
  mar; rw [← inv_mul_eq_iff_eq_mul]; mal
  apply mul_right_cancel (b := {ψ, i, t}⁻¹)
  rw [← inv_of_β, ← commutatorElement_def]
  grw [comm_of_β_ψ, expr_βψ_β2ψ_as_β2ψ_βψ]
  rw [eq_of_hR_eq β2ψ (i + (i + j)) (by omega) (2 * (t / 2) * (t * u)) (by field_simp; ring)]
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ hi hij]
  ring_nf
  mul_inj
  have neg_add_div_two_eq : -t + (t / 2) = -t / 2 := by field_simp; ring
  chev_simp [← div_eq_mul_inv, neg_add_div_two_eq]

omit Fchar

-- 8.111
@[group_reassoc]
theorem expr_β_α_as_αβ_α_β : forall_ij_tu α β,
    {β, j, u} * {α, i, t} = {αβ, i + j, -t * u} * {α, i, t} * {β, j, u} := by
  intro i j hi hj t u
  rw [neg_mul, ← inv_of_αβ]
  have : t * u = ↑(1 : ℤ) * t * u := by chev_simp
  rw [this]
  rw [← comm_of_α_β hi hj]
  exact comm_left _ _

-- 8.112a
@[group_reassoc]
theorem expr_ψ_β_as_β_ψ_βψ_β2ψ : forall_ij_tu β ψ,
    {ψ, j, u} * {β, i, t} = {β, i, t} * {ψ, j, u} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, t * u^2} := by
  intro i j hi hj t u
  have hij : i + j ≤ βψ.height := by ht
  have hi2j : i + (2 * j) ≤ β2ψ.height := by ht
  rw [comm_right_rev, inv_of_β, inv_of_ψ]
  grw [comm_of_β_ψ, mul_inv_rev, expr_βψ_β2ψ_as_β2ψ_βψ hij hi2j, pow_two]

-- 8.112b
@[group_reassoc]
theorem expr_ψ_β_as_β2ψ_βψ_β_ψ : forall_ij_tu β ψ,
    {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := by
  intro i j hi hj t u
  have hij : i + j ≤ βψ.height := by ht
  have hi2j : i + (2 * j) ≤ β2ψ.height := by ht
  rw [comm_left_rev]
  grw [comm_of_β_ψ, mul_inv_rev, pow_two]

-- 8.112c
omit Fchar
@[group_reassoc]
theorem expr_ψ_β_as_β_β2ψ_βψ_ψ : forall_ij_tu β ψ,
    {ψ, j, u} * {β, i, t} = {β, i, t} * {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {ψ, j, u} := by
  intro i j hi hj t u
  have hij : i + j ≤ βψ.height := by ht
  have hi2j : i + (2 * j) ≤ β2ψ.height := by ht
  rw [comm_mid_rev, inv_of_β]
  grw [comm_of_β_ψ, expr_βψ_β2ψ_as_β2ψ_βψ hij hi2j, pow_two]

-- 8.112d
@[group_reassoc]
theorem expr_ψ_β_as_β_βψ_β2ψ_ψ : forall_ij_tu β ψ,
    {ψ, j, u} * {β, i, t} = {β, i, t} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, -t * u^2} * {ψ, j, u} := by
  intro i j hi hj t u
  have hij : i + j ≤ βψ.height := by ht
  have hi2j : i + (2 * j) ≤ β2ψ.height := by ht
  rw [expr_ψ_β_as_β_β2ψ_βψ_ψ hi hj t u,
        greassoc_of% expr_βψ_β2ψ_as_β2ψ_βψ hij hi2j (-t * u) (-t * u^2)]

-- 8.113a
@[group_reassoc]
theorem expr_ψ_βψ_as_βψ_β2ψ_ψ : forall_ij_tu ψ βψ,
    {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {β2ψ, i + j, 2 * t * u} * {ψ, i, t} := by
  intro i j hi hj t u
  rw [comm_mid, inv_of_βψ]
  grw [comm_of_ψ_βψ hi hj]

-- 8.113b
@[group_reassoc]
theorem expr_ψ_βψ_as_βψ_ψ_β2ψ :
  forall_ij_tu ψ βψ,
    {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {ψ, i, t} * {β2ψ, i + j, 2 * t * u} := by
  intro i j hi hj t u
  have hij : i + j ≤ β2ψ.height := by ht
  grw [expr_ψ_β2ψ_as_β2ψ_ψ hi hij, expr_ψ_βψ_as_βψ_β2ψ_ψ hi hj]

-- 8.114a
@[group_reassoc]
theorem expr_βψ_ψ_as_ψ_β2ψ_βψ :
  forall_ij_tu ψ βψ,
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {β2ψ, i + j, -2 * t * u} * {βψ, j, u} := by
  intro i j hi hj t u
  have hij : j + i ≤ β2ψ.height := by ht
  rw [h_add_comm β2ψ i j, ← greassoc_of% expr_βψ_β2ψ_as_β2ψ_βψ hj hij, h_add_comm β2ψ j i]
  grw [expr_ψ_βψ_as_βψ_ψ_β2ψ hi hj]

-- 8.114b
@[group_reassoc]
theorem expr_βψ_ψ_as_ψ_βψ_β2ψ : forall_ij_tu ψ βψ,
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {βψ, j, u} * {β2ψ, i + j, -2 * t * u} := by
  intro i j hi hj t u
  have hij : i + j ≤ β2ψ.height := by ht
  rw [expr_βψ_ψ_as_ψ_β2ψ_βψ hi hj, greassoc_of% expr_βψ_β2ψ_as_β2ψ_βψ hj hij]

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) (via the previous theorem). -/
private lemma homog_lift_of_comm_of_αβ_βψ (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : F), ⁅ { αβ, i + j, t}, {βψ, j + k, u} ⁆ = 1 := by
    intro t u
    let t₁ : F := match i with
      | 1 => t
      | 0 => 0
    let t₀ : F := match i with
      | 1 => 0
      | 0 => t
    let u₁ : F := match j with
      | 1 => 1
      | 0 => 0
    let u₀ : F := match j with
      | 1 => 0
      | 0 => 1
    let v₁ : F := match k with
      | 1 => u
      | 0 => 0
    let v₀ : F := match k with
      | 1 => 0
      | 0 => u
    have hf_i : i ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have hf_j : j ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have hf_k : k ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have id₁ : {αβ, i + j, t} = {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    have id₂ : {βψ, j + k, u} = {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    rw [id₁, id₂, raw_nonhomog_lift_of_comm_of_αβ_βψ]

private lemma image_of_homog_lift_of_comm_of_αβ_βψ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ βψ.height)
    : ((i, j) ∈ ij_jk_image) → ∀ (t u : F), ⁅ {αβ, i, t}, {βψ, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  simp [f_ij_jk] at this
  rcases this with ⟨ i', j', k', ⟨ hi', hj', hk' ⟩, rfl, rfl ⟩
  rw [← homog_lift_of_comm_of_αβ_βψ i' j' k' hi' hj' hk' t u]

private lemma comm_of_αβ_βψ_20 : ∀ (t u : F), ⁅ {αβ, 2, t}, {βψ, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {βψ, 1, u} _ ({αβ, 1, t + 1} * {αβ, 0, 1})
  · mul_assoc_l
    rw [←raw_nonhomog_lift_of_comm_of_αβ_βψ t 1 1 1 0 u]
    simp only [one_mul, mul_one, mul_zero, add_zero]
    rw [id_of_βψ]
    rw [one_mul]
  · rw [←homog_lift_of_comm_of_αβ_βψ 1 1 0 (by trivial) (by trivial) (by trivial) t u]
  · apply triv_comm_mul_left
    rw [←homog_lift_of_comm_of_αβ_βψ 0 1 0 (by trivial) (by trivial) (by trivial) (t+1) u]
    rw [←homog_lift_of_comm_of_αβ_βψ 0 0 1 (by trivial) (by trivial) (by trivial) 1 u]
  apply triv_comm_mul_left
  rw [←homog_lift_of_comm_of_αβ_βψ 1 0 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [←homog_lift_of_comm_of_αβ_βψ 0 0 0 (by trivial) (by trivial) (by trivial) 1 u]

private lemma comm_of_αβ_βψ_02 : ∀ (t u : F), ⁅ {αβ, 0, t}, {βψ, 2, u}⁆ = 1 := by
  intro t u
  apply triv_comm_symm.1
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {αβ, 1, t} _ ({βψ, 1, u + 1} * {βψ, 0, 1})
  · mul_assoc_l
    rw [←triv_comm_symm.1 (raw_nonhomog_lift_of_comm_of_αβ_βψ 0 t 1 1 u 1)]
    simp only [one_mul, mul_one, mul_zero, add_zero, zero_add]
    rw [add_comm u 1, id_of_αβ, one_mul]
  · rw [←triv_comm_symm.1 (homog_lift_of_comm_of_αβ_βψ 0 1 1 (by trivial) (by trivial) (by trivial) t u)]
  · apply triv_comm_mul_left
    rw [←triv_comm_symm.1 (homog_lift_of_comm_of_αβ_βψ 0 1 0 (by trivial) (by trivial) (by trivial) t (u + 1))]
    rw [←triv_comm_symm.1 (homog_lift_of_comm_of_αβ_βψ 1 0 0 (by trivial) (by trivial) (by trivial) t 1)]
  apply triv_comm_mul_left
  rw [←triv_comm_symm.1 (homog_lift_of_comm_of_αβ_βψ 0 0 1 (by trivial) (by trivial) (by trivial) t (u + 1))]
  rw [←triv_comm_symm.1 (homog_lift_of_comm_of_αβ_βψ 0 0 0 (by trivial) (by trivial) (by trivial) t 1)]

-- 8.115
theorem comm_of_αβ_βψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ βψ := by
  intro i j hi hj t u
  by_cases hij : (i, j) ∈ ij_jk_image
  · apply image_of_homog_lift_of_comm_of_αβ_βψ hi hj hij
  · have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
      simp [ij_jk_image] at hij
      ht
    rcases this with ( ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
    · rw [← comm_of_αβ_βψ_02 t u]
    · rw [← comm_of_αβ_βψ_20 t u]
declare_B3Large_triv_expr_thm F αβ βψ
