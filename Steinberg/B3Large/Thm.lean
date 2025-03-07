/-

LICENSE.

-/

import Steinberg.B3Large.Basic

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

import Steinberg.Defs.Lattice
import Steinberg.Defs.Commutator
import Steinberg.Defs.ReflDeg

import Steinberg.Upstream.FreeGroup

/-!

  File dox.

-/

namespace Steinberg.B3Large

open Steinberg B3LargePosRoot GradedGen ReflDeg

variable {F : Type TF} [Field F] (Fchar : (2 : F) ≠ 0)
variable (F_sum_of_squares : ∀ (a : F), ∃ (x y : F), a = x^2 + y^2)

theorem def_of_αβψ :
  forall_i_t αβψ,
  {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2 *
  {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1 *
  {βψ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 *
  {α, (split_3_into_1_2 i hi).1, -t}'(correct_of_split_3_into_1_2 i hi).1 *
  {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2
  = {αβψ, i, t} := by
  intro i hi t
  apply WeakChevalley.helper
  apply (weakB3Large F).def_helper rels_of_def_of_αβψ
  · simp only [weakB3Large, def_sets]
    exact Set.mem_insert rels_of_def_of_αβψ _
  · exists i, hi, t

theorem def_of_αβ2ψ :
  forall_i_t αβ2ψ,
    ⁅ ({α, (split_4_into_1_3 i hi).1, t}'(correct_of_split_4_into_1_3 i hi).1),
      ({β2ψ, (split_4_into_1_3 i hi).2, 1}'(correct_of_split_4_into_1_3 i hi).2)
    ⁆ = {αβ2ψ, i, t} := by
  intro i hi t
  apply WeakChevalley.helper
  apply (weakB3Large F).def_helper rels_of_def_of_αβ2ψ
  · simp only [weakB3Large, def_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, hi, t

theorem def_of_α2β2ψ :
  forall_i_t α2β2ψ,
    ⁅ ({αβ, (split_5_into_2_3 i hi).1, t}'(correct_of_split_5_into_2_3 i hi).1),
      ({β2ψ, (split_5_into_2_3 i hi).2, 1}'(correct_of_split_5_into_2_3 i hi).2)
    ⁆ = {α2β2ψ, i, -t} := by
  intro i hi t
  apply WeakChevalley.helper
  apply (weakB3Large F).def_helper rels_of_def_of_α2β2ψ
  · simp only [weakB3Large, def_sets, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  · exists i, hi, t

/-! ### Nonhomogeneous lift -/

-- 8.81
theorem raw_nonhomog_lift_of_comm_of_αβ_βψ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}
    , {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} ⁆
    = 1 := by
  hom_tac rels_of_nonhomog_lift_of_comm_of_αβ_βψ [t₁, t₀, u₁, u₀, v₁, v₀]

-- 8.82
theorem raw_nonhomog_lift_of_comm_of_α_α2β2ψ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {α, 1, t₁} * {α, 0, t₀},
      ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
        {β2ψ, 3, u₁ * v₁^2} * {β2ψ, 2, u₀ * v₁^2 + 2 * u₁ * v₀ * v₁}
          * {β2ψ, 1, u₁ * v₀^2 + 2 * u₀ * v₀ * v₁} * {β2ψ, 0, u₀ * v₀^2} ⁆⁆ = 1 := by
  hom_tac rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ [t₁, t₀, u₁, u₀, v₁, v₀]

/-! ### Homogeneous lift -/

-- 8.83
theorem raw_hom_lift_of_interchange_of_αβψ :
  forall_ijk_tuv,
    {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} =
    {βψ, j + k, -u * v / 2} * {α, i, t} * {βψ, j + k, u * v} * {α, i, -t} * {βψ, j + k, -u * v / 2} := by
  hom_tac rels_of_hom_lift_of_interchange_of_αβψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.84
theorem raw_hom_lift_of_doub_of_αβψ :
  forall_ik_tuv αβ ψ,
    {ψ, k, -v / 2} * {αβ, i, t * u} * {ψ, k, v} * {αβ, i, -t * u} * {ψ, k, -v / 2} *
    {ψ, k, -v / 2} * {αβ, i, t * u} * {ψ, k, v} * {αβ, i, -t * u} * {ψ, k, -v / 2} =
    {ψ, k, -v} * {αβ, i, t * u} * {ψ, k, 2 * v} * {αβ, i, -t * u} * {ψ, k, -v} := by
  hom_tac rels_of_hom_lift_of_doub_of_αβψ [i, k, hi, hk, t, u, v]

-- 8.85
theorem raw_hom_lift_of_interchange_of_αβ2ψ :
  forall_ijk_tuv,
    ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
      {ψ, k, v} ⁆
      = ⁅ {α, i, t}, {β2ψ, j + 2 * k, -2 * u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_interchange_of_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.86
theorem raw_hom_lift_of_comm_of_βψ_α_β2ψ :
  forall_ijk_tuv,
    ⁅ {βψ, j + k, u * v}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_βψ_α_β2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.87a
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_a :
  forall_ijk_tuv,
    ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {α, i, -t}, {β2ψ, j + 2 * k, -u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.87b
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_b :
  forall_ijk_tuv,
    ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {α, i, t}, {β2ψ, j + 2 * k, -u * v^2} ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.87c
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_c :
  forall_ijk_tuv,
    ⁅ {α, i, t} , {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅{α, i, t}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.88
theorem raw_hom_lift_of_comm_of_β2ψ_αβψ :
  forall_ijk_tuv,
    ⁅ {β2ψ, j + 2 * k, u * v^2},
      {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_β2ψ_αβψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.89a
theorem raw_hom_lift_of_interchange_of_α2β2ψ_a :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆
      = ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
          {βψ, j + k, u * v} ⁆ := by
  hom_tac rels_of_hom_lift_of_interchange_of_α2β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.89b
theorem raw_hom_lift_of_interchange_of_α2β2ψ_b :
  forall_ijk_tuv,
    ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
      {βψ, j + k, u * v} ⁆
      = ⁅ ⁅ {α, i, t}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆, {β, j, u} ⁆ := by
  hom_tac rels_of_hom_lift_of_interchange_of_α2β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.90
theorem raw_hom_lift_of_comm_of_ψ_αβ_β2ψ :
  forall_ijk_tuv,
    ⁅ {ψ, k, v}, ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_ψ_αβ_β2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.91a
theorem raw_hom_lift_of_comm_of_αβ_αβ_β2ψ_a :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.91b
theorem raw_hom_lift_of_comm_of_αβ_αβ_β2ψ_b :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.92a
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_a :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, -u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.92b
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_b :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.92c
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_c :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {αβ, i + j, 2 * t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.93a
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_a :
  forall_ijk_tuv,
    ⁅ {β, j, u},
      ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
      = ⁅ {β, j, -u}, ⁅ {α, i, -t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.93b
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_b :
  forall_ijk_tuv,
    ⁅ {β, j, u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
    * ⁅ {β, j, -u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.93c
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_c :
  forall_ijk_tuv,
    ⁅ {β, j, u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
    * ⁅ {β, j, u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
      = ⁅ {β, j, 2 * u}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ := by
  hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.94
theorem raw_hom_lift_of_comm_of_βψ_αβ2ψ :
  forall_ijk_tuv,
    ⁅ {βψ, j + k, u * v}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  hom_tac rels_of_hom_lift_of_comm_of_βψ_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.95
theorem raw_hom_lift_of_comm_of_β2ψ_αβ2ψ :
  forall_ijk_tuv,
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
  have := calc
    ⁅{β, j, u}, {ψ, i, t}⁆ = {βψ, i + j, t * u} * {β2ψ, j + 2 * i, u * t^2} := by rw [comm_of_β_ψ]; group
    _ = {β2ψ, j + 2 * i, u * t^2} * {βψ, i + j, t * u} := by rw [comm_left, comm_of_βψ_β2ψ]; group
    _ = ⁅{ψ, i, t / 2}, {βψ, i + j, t * u}⁆ * {βψ, i + j, t * u} := by rw [comm_of_ψ_βψ]; field_simp; group
    _ = {ψ, i, t / 2} * {βψ, i + j, t * u} * {ψ, i, t / 2}⁻¹ := by group
  calc
    {βψ, i + j, t * u} = {ψ, i, t / 2}⁻¹ * ⁅{β, j, u}, {ψ, i, t}⁆ * {ψ, i, t / 2} := by rw [this]; group
    _ = {ψ, i, t / 2}⁻¹ * {β, j, u} * {ψ, i, t} * {β, j, u}⁻¹ * {ψ, i, t}⁻¹ * {ψ, i, t / 2} := by group
    _ = {ψ, i, -t / 2} * {β, j, u} * {ψ, i, t} * {β, j, -u} * {ψ, i, -t} * {ψ, i, t / 2} := by rw [inv_of_ψ, inv_of_β, inv_of_ψ]; group
    _ = {ψ, i, -t / 2} * {β, j, u} * {ψ, i, t} * {β, j, -u} * {ψ, i, -t / 2} := by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, lin_of_ψ]; field_simp; group

omit Fchar

-- 8.111
@[group_reassoc]
theorem expr_β_α_as_αβ_α_β :
  forall_ij_tu α β,
    {β, j, u} * {α, i, t} = {αβ, i + j, -t * u} * {α, i, t} * {β, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ, i + j, -t * u} * {α, i, t} * {β, j, u} = {αβ, i + j, t * u}⁻¹ * {α, i, t} * {β, j, u} := by rw [inv_of_αβ]; group
    _ = ⁅{α, i, t}, {β, j, u}⁆⁻¹ * {α, i, t} * {β, j, u} := by rw [comm_of_α_β, one_mul];
    _ = {β, j, u} * {α, i, t} := by group
  exact this.symm

-- 8.112a
@[group_reassoc]
theorem expr_ψ_β_as_β_ψ_βψ_β2ψ :
  forall_ij_tu 1 1,
  {ψ, j, u} * {β, i, t} = {β, i, t} * {ψ, j, u} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, t * u^2} := by
  intro i j hi hj t u
  calc
    {ψ, j, u} * {β, i, t} = {β, i, t} * {ψ, j, u} * ⁅{β, i, t}⁻¹, {ψ, j, u}⁻¹⁆⁻¹ := by group
    _ = {β, i, t} * {ψ, j, u} * ⁅{β, i, -t}, {ψ, j, -u}⁆⁻¹ := by chev_simp
    _ = {β, i, t} * {ψ, j, u} * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, -t * u^2})⁻¹ := by grw [comm_of_β_ψ]; field_simp; group
    _ = {β, i, t} * {ψ, j, u} * {β2ψ, i + 2 * j, -t * u^2}⁻¹ * {βψ, i + j, t * u}⁻¹ := by group
    _ = {β, i, t} * {ψ, j, u} * {β2ψ, i + 2 * j, t * u^2} * {βψ, i + j, -t * u} := by grw [neg_mul, neg_mul, inv_of_β2ψ, inv_of_βψ, inv_inv]
    _ = {β, i, t} * {ψ, j, u} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, t * u^2} := by grw [expr_βψ_β2ψ_as_β2ψ_βψ (add_le_add hi hj) (add_le_add hi (mul_le_mul_of_nonneg_left hj (by trivial)))]


-- 8.112b
@[group_reassoc]
theorem expr_ψ_β_as_β2ψ_βψ_β_ψ :
  forall_ij_tu 1 1,
    {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := by
  intro i j hi hj t u
  have h₁ : ⁅{β, i, t}, {ψ, j, u}⁆ = {βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} := by rw [comm_of_β_ψ]; group
  have h₂ := congrArg (HMul.hMul ({β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u})) (reorder_left_of_eq_comm h₁)
  calc
    {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, t * u^2}⁻¹ * {βψ, i + j, t * u}⁻¹ * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} * {ψ, j, u} * {β, i, t}) := by group
    _ = {β2ψ, i + 2 * j, -(t * u^2)} * {βψ, i + j, -(t * u)} * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} * {ψ, j, u} * {β, i, t}) := by rw [inv_of_βψ, inv_of_β2ψ]
    _ = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} * {ψ, j, u} * {β, i, t}) := by group
    _ = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * ({β, i, t} * {ψ, j, u}) := by rw [h₂]
    _ = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := by group

-- 8.112c
omit Fchar
@[group_reassoc]
theorem expr_ψ_β_as_β_β2ψ_βψ_ψ :
  forall_ij_tu 1 1,
  {ψ, j, u} * {β, i, t} = {β, i, t} * {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {ψ, j, u} := by
  intro i j hi hj t u
  calc
    {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := expr_ψ_β_as_β2ψ_βψ_β_ψ hi hj t u
    _ = {β2ψ, i + 2 * j, -t * u^2} * ({βψ, i + j, -t * u} * {β, i, t}) * {ψ, j, u} := rfl
    _ = {β2ψ, i + 2 * j, -t * u^2} * ({β, i, t} * {βψ, i + j, -t * u}) * {ψ, j, u} := by rw [triv_comm_iff_commutes.1 (comm_of_β_βψ _ _ t (-t * u))]
    _ = ({β2ψ, i + 2 * j, -t * u^2} * {β, i, t}) * {βψ, i + j, -t * u} * {ψ, j, u} := rfl
    _ = ({β, i, t} * {β2ψ, i + 2 * j, -t * u^2}) * {βψ, i + j, -t * u} * {ψ, j, u} := by rw [triv_comm_iff_commutes.1 (comm_of_β_β2ψ _ _ t (-t * u^2))]

-- 8.112d
@[group_reassoc]
theorem expr_ψ_β_as_β_βψ_β2ψ_ψ :
  forall_ij_tu β ψ,
    {ψ, j, u} * {β, i, t} = {β, i, t} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, -t * u^2} * {ψ, j, u} := by
  intro i j hi hj t u
  calc
    {ψ, j, u} * {β, i, t} = {β, i, t} * {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {ψ, j, u} := expr_ψ_β_as_β_β2ψ_βψ_ψ hi hj t u
    _ = {β, i, t} * ({β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u}) * {ψ, j, u} := rfl
    _ = {β, i, t} * ({βψ, i + j, -t * u} * {β2ψ, i + 2 * j, -t * u^2}) * {ψ, j, u} := by rw [triv_comm_iff_commutes.1 (comm_of_βψ_β2ψ _ _ (-t * u) (-t * u^2))]

-- 8.113a
@[group_reassoc]
theorem expr_ψ_βψ_as_βψ_β2ψ_ψ :
  forall_ij_tu ψ βψ,
    {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {β2ψ, i + j, 2 * t * u} * {ψ, i, t} := by
  intro i j hi hj t u
  have := comm_of_βψ_β2ψ (j := i + j) hj (by ht) u (2 * t * u)
  rw [triv_comm_iff_commutes] at this
  grw [reorder_left_of_eq_comm (comm_of_ψ_βψ hi hj t u), this]

-- 8.113b
@[group_reassoc]
theorem expr_ψ_βψ_as_βψ_ψ_β2ψ :
  forall_ij_tu ψ βψ,
    {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {ψ, i, t} * {β2ψ, i + j, 2 * t * u} := by
  intro i j hi hj t u
  have := comm_of_ψ_β2ψ (i := i) (j := i + j) hi (by ht) t (2 * t * u)
  rw [triv_comm_iff_commutes] at this
  grw [expr_ψ_βψ_as_βψ_β2ψ_ψ hi hj t u, this]

-- 8.114a
@[group_reassoc]
theorem expr_βψ_ψ_as_ψ_β2ψ_βψ :
  forall_ij_tu ψ βψ,
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {β2ψ, i + j, -2 * t * u} * {βψ, j, u} := by
  intro i j hi hj t u
  calc
    {βψ, j, u} * {ψ, i, t} = ({βψ, j, u} * {ψ, i, t} * {β2ψ, i + j, 2 * t * u}) * {β2ψ, i + j, 2 * t * u}⁻¹ := by group
    _ = ({ψ, i, t} * {βψ, j, u}) * {β2ψ, i + j, 2 * t * u}⁻¹ := by rw [expr_ψ_βψ_as_βψ_ψ_β2ψ hi hj]
    _ = ({ψ, i, t} * {βψ, j, u}) * {β2ψ, i + j, -2 * t * u} := by rw [inv_of_β2ψ]; group
    _ = {ψ, i, t} * ({βψ, j, u} * {β2ψ, i + j, -2 * t * u}) := rfl
    _ = {ψ, i, t} * ({β2ψ, i + j, -2 * t * u} * {βψ, j, u}) := by rw [triv_comm_iff_commutes.1 (comm_of_βψ_β2ψ _ _ u (-2 * t * u))]

-- 8.114b
@[group_reassoc]
theorem expr_βψ_ψ_as_ψ_βψ_β2ψ :
  forall_ij_tu ψ βψ,
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {βψ, j, u} * {β2ψ, i + j, -2 * t * u} := by
  intro i j hi hj t u
  calc
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * ({β2ψ, i + j, -2 * t * u} * {βψ, j, u}) := expr_βψ_ψ_as_ψ_β2ψ_βψ hi hj t u
    _ = {ψ, i, t} * ({βψ, j, u} * {β2ψ, i + j, -2 * t * u}) := by rw [triv_comm_iff_commutes.1 (comm_of_βψ_β2ψ _ _ u (-2 * t * u))]

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

-- symmetric to proof of `comm_of_αβ_βγ_20`
private lemma comm_of_αβ_βψ_02 : ∀ (t u : F), ⁅ {αβ, 0, t}, {βψ, 2, u} ⁆ = 1 := by
  intro t u
  have : ⁅ {αβ, 0, t}, {βψ, 2, u} ⁆ = ReflDeg.refl_symm b3large_valid ⁅ {αβ, 2, t}, {βψ, 0, u} ⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, comm_of_αβ_βψ_20, map_one]

-- 8.115
theorem trivial_comm_of_αβ_βψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ βψ := by
  intro i j hi hj t u
  have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ ((i, j) ∈ ij_jk_image) := by
    rw [ij_jk_image]
    simp only [PosRootSys.height, height] at *
    simp -- should fix
    omega
  rcases this with ( ⟨ rfl, rfl ⟩ | ⟨rfl, rfl⟩ | hij )
  · rw [←comm_of_αβ_βψ_02 t u]
  · rw [←comm_of_αβ_βψ_20 t u]
  · exact image_of_homog_lift_of_comm_of_αβ_βψ hi hj hij _ _

@[group_reassoc]
theorem expr_αβ_βψ_as_βψ_αβ :
  forall_ij_tu αβ βψ,
    {αβ, i, t} * {βψ, j, u} = {βψ, j, u} * {αβ, i, t} := by
  intro i j hi hj t u
  rw [triv_comm_iff_commutes.1 (trivial_comm_of_αβ_βψ _ _ t u)]

/- ### Establishing α + β + ψ -/

private lemma interchange_αβψ_refl_v :
  forall_ijk_tu 1 1 1,
  {ψ, k, -1/2} * {αβ, i + j, t * u} * {ψ, k, 1} * {αβ, i + j, -t * u} * {ψ, k, -1/2} = {βψ, j + k, -u/2} * {α, i, t} * {βψ, j + k, u} * {α, i, -t} * {βψ, j + k, -u/2} := by
  intro i j k hi hj hk t u
  rw [raw_hom_lift_of_interchange_of_αβψ hi hj hk t u 1]
  simp only [mul_one]

private lemma interchange_αβψ_refl_u :
  forall_ijk_tu 1 1 1,
  {ψ, k, -u/2} * {αβ, i + j, t} * {ψ, k, u} * {αβ, i + j, -t} * {ψ, k, -u/2} = {βψ, j + k, -u/2} * {α, i, t} * {βψ, j + k, u} * {α, i, -t} * {βψ, j + k, -u/2} := by
  intro i j k hi hj hk t u
  rw [←mul_one t, ←neg_mul, raw_hom_lift_of_interchange_of_αβψ hi hj hk t 1 u]
  simp only [neg_mul, one_mul, mul_one]

private lemma interchange_αβψ_trans_βψ_α :
  forall_ijk_tu 1 1 1,
  {βψ, j + k, -1/2} * {α, i, t * u} * {βψ, j + k, 1} * {α, i, -t * u} * {βψ, j + k, -1/2} = {βψ, j + k, -u/2} * {α, i, t} * {βψ, j + k, u} * {α, i, -t} * {βψ, j + k, -u/2} := by
  intro i j k hi hj hk t u
  have aux₁ := raw_hom_lift_of_interchange_of_αβψ hi hj hk t u 1
  have aux₂ := raw_hom_lift_of_interchange_of_αβψ hi hj hk (t * u) 1 1
  simp only [one_mul, mul_one] at aux₁
  simp only [one_mul, mul_one, ←neg_mul] at aux₂
  rwa [aux₂] at aux₁

private lemma interchange_αβψ_trans_ψ_αβ :
  forall_ijk_tu 1 1 1,
  {ψ, k, -1 / 2} * {αβ, i + j, t * u} * {ψ, k, 1} * {αβ, i + j, -t * u} * {ψ, k, -1 / 2} = {ψ, k, -u / 2} * {αβ, i + j, t} * {ψ, k, u} * {αβ, i + j, -t} * {ψ, k, -u / 2} := by
  intro i j k hi hj hk t u
  have aux₁ := raw_hom_lift_of_interchange_of_αβψ hi hj hk 1 t u
  have aux₂ := raw_hom_lift_of_interchange_of_αβψ hi hj hk 1 (t * u) 1
  simp only [one_mul, mul_one, neg_mul] at aux₁
  simp only [one_mul, mul_one, neg_mul] at aux₂
  rwa [←aux₁, ←neg_mul] at aux₂

-- height 0
private lemma expr_αβψ_as_βψ_α_βψ_α_βψ_00 :
  ∀ t u : F, {αβψ, 0, t * u} = {βψ, 0, -u/2} * {α, 0, t} * {βψ, 0, u} * {α, 0, -t} * {βψ, 0, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 0 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_00 :
  ∀ t u : F, {αβψ, 0, t * u} = {ψ, 0, -u/2} * {αβ, 0, t} * {ψ, 0, u} * {αβ, 0, -t} * {ψ, 0, -u/2} := by
  intro t u
  rw [expr_αβψ_as_βψ_α_βψ_α_βψ_00, ←@interchange_αβψ_refl_v _ _ 0 0 0 (by trivial) (by trivial) (by trivial),
  interchange_αβψ_trans_ψ_αβ (by trivial) (by trivial) (by trivial)]

-- height 1
private lemma expr_αβψ_as_βψ_α_βψ_α_βψ_01 :
  ∀ t u : F, {αβψ, 1, t * u} = {βψ, 1, -u/2} * {α, 0, t} * {βψ, 1, u} * {α, 0, -t} * {βψ, 1, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 1 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_01 :
  ∀ t u : F, {αβψ, 1, t * u} = {ψ, 1, -u/2} * {αβ, 0, t} * {ψ, 1, u} * {αβ, 0, -t} * {ψ, 1, -u/2} := by
  intro t u
  rw [expr_αβψ_as_βψ_α_βψ_α_βψ_01, @interchange_αβψ_refl_u _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_10 :
  ∀ t u : F, {αβψ, 1, t * u} = {ψ, 0, -u/2} * {αβ, 1, t} * {ψ, 0, u} * {αβ, 1, -t} * {ψ, 0, -u/2} := by
  intro t u
  rw [expr_αβψ_as_βψ_α_βψ_α_βψ_01, ←@interchange_αβψ_refl_v _ _ 0 1 0 (by trivial) (by trivial) (by trivial),
  interchange_αβψ_trans_ψ_αβ (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_βψ_α_βψ_α_βψ_10 :
  ∀ t u : F, {αβψ, 1, t * u} = {βψ, 0, -u/2} * {α, 1, t} * {βψ, 0, u} * {α, 1, -t} * {βψ, 0, -u/2} := by
  intro t u
  rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_10, @interchange_αβψ_refl_u _ _ 1 0 0 (by trivial) (by trivial) (by trivial)]

-- height 2
private lemma expr_αβψ_as_βψ_α_βψ_α_βψ_11 :
  ∀ t u : F, {αβψ, 2, t * u} = {βψ, 1, -u/2} * {α, 1, t} * {βψ, 1, u} * {α, 1, -t} * {βψ, 1, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 2 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_20 :
  ∀ t u : F, {αβψ, 2, t * u} = {ψ, 0, -u/2} * {αβ, 2, t} * {ψ, 0, u} * {αβ, 2, -t} * {ψ, 0, -u/2} := by
  intro t u
  rw [expr_αβψ_as_βψ_α_βψ_α_βψ_11, @interchange_αβψ_refl_u _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_11 :
  ∀ t u : F, {αβψ, 2, t * u} = {ψ, 1, -u/2} * {αβ, 1, t} * {ψ, 1, u} * {αβ, 1, -t} * {ψ, 1, -u/2} := by
  intro t u
  rw [expr_αβψ_as_βψ_α_βψ_α_βψ_11, @interchange_αβψ_refl_u _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_βψ_α_βψ_α_βψ_02 :
  ∀ t u : F, {αβψ, 2, t * u} = {βψ, 2, -u/2} * {α, 0, t} * {βψ, 2, u} * {α, 0, -t} * {βψ, 2, -u/2} := by
  intro t u
  rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_11, @interchange_αβψ_refl_u _ _ 0 1 1 (by trivial) (by trivial) (by trivial)]

-- height 3
private lemma expr_αβψ_as_βψ_α_βψ_α_βψ_12 :
  ∀ t u : F, {αβψ, 3, t * u} = {βψ, 2, -u/2} * {α, 1, t} * {βψ, 2, u} * {α, 1, -t} * {βψ, 2, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 3 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_21 :
  ∀ t u : F, {αβψ, 3, t * u} = {ψ, 1, -u/2} * {αβ, 2, t} * {ψ, 1, u} * {αβ, 2, -t} * {ψ, 1, -u/2} := by
  intro t u
  rw [expr_αβψ_as_βψ_α_βψ_α_βψ_12, @interchange_αβψ_refl_u _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]

-- 8.116a
theorem expr_αβψ_as_ψ_αβ_ψ_αβ_ψ :
  forall_ij_tu 2 1,
    {αβψ, i + j, t * u} = {ψ, j, -u/2} * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * {ψ, j, -u/2} := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_00]
  | 1, 0 => rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_10]
  | 0, 1 => rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_01]
  | 2, 0 => rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_20]
  | 1, 1 => rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_11]
  | 2, 1 => rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ_21]

-- 8.116b
theorem expr_αβψ_as_βψ_α_βψ_α_βψ :
  forall_ij_tu 1 2,
  {αβψ, i + j, t * u} = {βψ, j, -u/2} * {α, i, t} * {βψ, j, u} * {α, i, -t} * {βψ, j, -u/2} := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_αβψ_as_βψ_α_βψ_α_βψ_00]
  | 1, 0 => rw [expr_αβψ_as_βψ_α_βψ_α_βψ_10]
  | 0, 1 => rw [expr_αβψ_as_βψ_α_βψ_α_βψ_01]
  | 0, 2 => rw [expr_αβψ_as_βψ_α_βψ_α_βψ_02]
  | 1, 1 => rw [expr_αβψ_as_βψ_α_βψ_α_βψ_11]
  | 1, 2 => rw [expr_αβψ_as_βψ_α_βψ_α_βψ_12]

-- 8.117
theorem comm_of_α_αβψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk α αβψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height ψ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  rw [←one_mul u]
  grw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hj₁ hj₂, expr_α_ψ_as_ψ_α hi hj₂,
  expr_α_αβ_as_αβ_α hi hj₁, expr_α_ψ_as_ψ_α hi hj₂, expr_α_αβ_as_αβ_α hi hj₁,
  expr_α_ψ_as_ψ_α hi hj₂]

declare_B3Large_triv_expr_thm F α αβψ

-- 8.118
theorem comm_of_αβ_αβψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ αβψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height ψ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  have : {αβψ, j₁ + j₂, u} = {αβψ, j₂ + j₁, u} := by group
  rw [this]
  rw [←one_mul u]
  grw [expr_αβψ_as_βψ_α_βψ_α_βψ hj₂ hj₁,
  expr_αβ_βψ_as_βψ_αβ hi hj₁, ←expr_α_αβ_as_αβ_α hj₂ hi, expr_αβ_βψ_as_βψ_αβ hi hj₁, ←expr_α_αβ_as_αβ_α hj₂ hi,
  expr_αβ_βψ_as_βψ_αβ hi hj₁]

declare_B3Large_triv_expr_thm F αβ αβψ

-- 8.119
theorem comm_of_β_αβψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk β αβψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height ψ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  have : {αβψ, j₁ + j₂, u} = {αβψ, j₂ + j₁, u} := by group
  rw [this]
  rw [←one_mul u]
  grw [expr_αβψ_as_βψ_α_βψ_α_βψ hj₂ hj₁, expr_β_βψ_as_βψ_β hi hj₁,
  expr_β_α_as_αβ_α_β hj₂ hi, expr_β_βψ_as_βψ_β hi hj₁, expr_β_α_as_αβ_α_β hj₂ hi,
  expr_β_βψ_as_βψ_β hi hj₁, ←expr_α_αβ_as_αβ_α hj₂ (add_le_add hj₂ hi),
  expr_αβ_βψ_as_βψ_αβ (add_le_add hj₂ hi) hj₁, neg_neg, neg_mul, one_mul, inv_of_αβ,
  inv_mul_cancel_right]

declare_B3Large_triv_expr_thm F β αβψ

-- 8.120a
@[simp, chev_simps]
private lemma inv_doub_of_αβψ_a :
  forall_i_t αβψ,
    {αβψ, i, t} * {αβψ, i, -t} = 1 := by
  intro i hi t
  rcases decompose αβ.height ψ.height i hi with ⟨ i₁, i₂, ⟨ rfl, hi₁, hi₂ ⟩ ⟩
  have : (-(1 : F) / 2) = -((1 : F) / 2) := by ring
  rw [←mul_one t, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂, mul_one]
  have expand := expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂ t (-1)
  rw [mul_neg_one, neg_neg] at expand
  grw [expand, neg_neg, this]

-- restatement of 8.120a using our naming conventions
@[simp, chev_simps]
theorem inv_of_αβψ :
  forall_i_t αβψ,
    {αβψ, i, t}⁻¹ = {αβψ, i, -t} := by
  intro i hi t
  have := eq_inv_of_mul_eq_one_left (inv_doub_of_αβψ_a hi (-t))
  rw [neg_neg] at this
  exact this.symm

-- 8.120b
include Fchar
theorem doub_of_αβψ :
  forall_i_t αβψ,
    {αβψ, i, t} * {αβψ, i, t} = {αβψ, i, 2 * t} := by
  intros i hi t
  rcases decompose αβ.height ψ.height i hi with ⟨ i₁, i₂, ⟨ rfl, hi₁, hi₂ ⟩ ⟩
  rw [←mul_one t]
  rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  have := raw_hom_lift_of_doub_of_αβψ hi₁ hi₂ t 1 1
  rw [mul_one, neg_mul, mul_one, mul_one] at this
  grw [this]
  rw [mul_comm 2 t]
  grw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂, neg_div_self Fchar]

lemma half_add_half (u : F) : (u / 2) + (u / 2) = u := by
  have : ((2 : F) / 2) = 1 := (div_eq_one_iff_eq Fchar).mpr rfl
  rw [←mul_two, div_mul_comm, this, one_mul]

-- 8.121
theorem generic_comm_of_αβ_ψ :
  forall_ij_tu 2 1,
    ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβψ, i + j, t * u} * ⁅{αβψ, i + j, -t * u}, {ψ, j, u / 2}⁆
    ∧ ⁅{αβ, i, t}, {ψ, j, u}⁆ = ⁅{αβψ, i + j, t * u}, {ψ, j, u / 2}⁆⁻¹ * {αβψ, i + j, t * u} := by
  intro i j hi hj t u
  set x := {αβ, i, t} with hx
  set y := {ψ, j, u/2} with hy
  have xinv : x⁻¹ = {αβ, i, -t} := by rw [inv_of_αβ]
  have ysquare : y^2 = {ψ, j, u} := by
    rw [pow_two, lin_of_ψ, ←two_mul, mul_div_left_comm, div_self Fchar, mul_one]
  have yinv : y⁻¹ = {ψ, j, -(u / 2)} := by rw [inv_of_ψ]
  have x_star_y : (x ⋆ y) = {αβψ, i + j, t * u} := by
    unfold star x y
    grw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi hj, neg_div 2 u, inv_of_ψ, pow_two, inv_of_αβ,
    lin_of_ψ, half_add_half Fchar u]
  have x_star_y_inv : (x ⋆ y)⁻¹ = {αβψ, i + j, -t * u} := by
    rw [x_star_y, eq_inv_of_mul_eq_one_left (inv_doub_of_αβψ_a (add_le_add hi hj) (t * u)), inv_inv, neg_mul]
  rw [←ysquare, ←x_star_y, ←x_star_y_inv]
  exact ⟨(star_commutator x y).symm, (commutator_star x y).symm⟩

-- 8.122
theorem generic_comm_of_α_βψ :
  forall_ij_tu 1 2,
    ⁅{α, i, t}, {βψ, j, u}⁆ = {αβψ, i + j, t * u} * ⁅{αβψ, i + j, -t * u}, {βψ, j, u / 2}⁆
    ∧ ⁅{α, i, t}, {βψ, j, u}⁆ = ⁅{αβψ, i + j, t * u}, {βψ, j, u / 2}⁆⁻¹ * {αβψ, i + j, t * u} := by
  intro i j hi hj t u
  set x := {α, i, t} with hx
  set y := {βψ, j, u / 2} with hy
  have ysquare : y^2 = {βψ, j, u} := by
    rw [pow_two, hy, lin_of_βψ, half_add_half Fchar u]
  have x_star_y : (x ⋆ y) = {αβψ, i + j, t * u} := by
    unfold star x y
    grw [expr_αβψ_as_βψ_α_βψ_α_βψ hi hj, neg_div 2 u, inv_of_βψ, pow_two, lin_of_βψ, half_add_half Fchar u, inv_of_α]
  have x_star_y_inv : (x ⋆ y)⁻¹ = {αβψ, i + j, -t * u} := by
    rw [x_star_y, eq_inv_of_mul_eq_one_left (inv_doub_of_αβψ_a (add_le_add hi hj) (t * u)), inv_inv, neg_mul]
  rw [←ysquare, ←x_star_y, ←x_star_y_inv]
  exact ⟨(star_commutator x y).symm, (commutator_star x y).symm⟩

-- 8.123
omit Fchar
theorem lift_hom_interchange_of_αβ2ψ :
  forall_ijk_tuv,
    ⁅{αβψ, i + j + k, t * u}, {ψ, k, v}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u * v}⁆ := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, mul_zero, id_of_ψ, id_of_β2ψ]; group
  have expr_αβ2ψ := raw_hom_lift_of_interchange_of_αβ2ψ hi hj hk t (u / v) v
  have : -2 * (u / v) * v^2 = -2 * u * v := by field_simp; group
  rw [this] at expr_αβ2ψ
  have expr_αβψ := expr_αβψ_as_ψ_αβ_ψ_αβ_ψ (add_le_add hi hj) hk (t * (u / v)) v
  have : t * (u / v) * v = t * u := by field_simp
  rw [this] at expr_αβψ
  grw [←expr_αβ2ψ, expr_αβψ, neg_mul]


-- 8.124
theorem lift_hom_comm_of_βψ_α_β2ψ :
  forall_ijk_tuv,
    ⁅{βψ, j + k, t}, ⁅{α, i, u}, {β2ψ, j + 2 * k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, id_of_β2ψ]; group
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_βψ]; group
  have hβψ := raw_hom_lift_of_comm_of_βψ_α_β2ψ hi hj hk u (t^2 / v) (v / t)
  have : t^2 / v * (v / t) = t := by rw [pow_two]; field_simp
  rw [this] at hβψ
  have : t^2 / v * (v / t)^2 = v := by field_simp; group
  rw [this] at hβψ
  exact hβψ

-- 8.125a
theorem lift_hom_inv_doub_of_α_β2ψ_a :
  forall_ij_tu 1 3,
    ⁅{α, i, t}, {β2ψ, j, u}⁆ = ⁅{α, i, -t}, {β2ψ, j, -u}⁆ := by
  intro i j hi hj t u
  rcases decompose_3_into_booleans_1_2 j hj with ⟨j₁, j₂, ⟨ rfl, hj₁, hj₂⟩ ⟩
  have := raw_hom_lift_of_inv_doub_of_α_β2ψ_a hi hj₁ hj₂ t u 1
  field_simp at this
  exact this

-- 8.125b
theorem lift_hom_inv_doub_of_α_β2ψ_b :
  forall_ij_tu α β2ψ,
    ⁅{α, i, t}, {β2ψ, j, u}⁆ * ⁅{α, i, t}, {β2ψ, j, -u}⁆ = 1 := by
  intro i j hi hj t u
  rcases decompose_3_into_booleans_1_2 j hj with ⟨j₁, j₂, ⟨ rfl, hj₁, hj₂⟩ ⟩
  have := raw_hom_lift_of_inv_doub_of_α_β2ψ_b hi hj₁ hj₂ t u 1
  field_simp at this
  exact this

theorem inv_of_comm_of_α_β2ψ :
  forall_ij_tu α β2ψ,
    ⁅{α, i, t}, {β2ψ, j, u}⁆⁻¹ = ⁅{α, i, t}, {β2ψ, j, -u}⁆ := by
  intro i j hi hj t u
  exact inv_eq_of_mul_eq_one_right (lift_hom_inv_doub_of_α_β2ψ_b hi hj t u)

-- 8.125c
theorem lift_hom_inv_doub_of_α_β2ψ_c :
  forall_ij_tu α β2ψ,
    ⁅{α, i, t}, {β2ψ, j, u}⁆ * ⁅{α, i, t}, {β2ψ, j, u}⁆ = ⁅{α, i, t}, {β2ψ, j, 2 * u}⁆ := by
  intro i j hi hj t u
  rcases decompose_3_into_booleans_1_2 j hj with ⟨j₁, j₂, ⟨ rfl, hj₁, hj₂⟩ ⟩
  have := raw_hom_lift_of_inv_doub_of_α_β2ψ_c hi hj₁ hj₂ t u 1
  field_simp at this
  exact this

-- 8.126
theorem lift_hom_comm_of_β2ψ_αβψ :
  forall_ijk_tu α β ψ,
    ⁅{β2ψ, j + 2 * k, t}, {αβψ, i + j + k, u}⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_β2ψ]; group
  have expr_β2ψ := raw_hom_lift_of_comm_of_β2ψ_αβψ hi hj hk (u / t) t 1
  rw [←mul_one u, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ (add_le_add hi hj) hk u 1]
  field_simp at expr_β2ψ
  have : -(u * t) / t = -u := by field_simp
  rw [this] at expr_β2ψ
  exact expr_β2ψ

-- 8.127
theorem comm_of_ψ_α_β2ψ :
  forall_ijk_tuv ψ α β2ψ,
    ⁅{ψ, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.mpr
  rw [commutatorElement_def]
  grw [←inv_of_α, ←inv_of_β2ψ, ←expr_α_ψ_as_ψ_α hj hi, expr_ψ_β2ψ_as_β2ψ_ψ hi hk,
  ←expr_α_ψ_as_ψ_α hj hi, expr_ψ_β2ψ_as_β2ψ_ψ hi hk]

@[group_reassoc]
theorem expr_ψ_comm_α_β2ψ_as_comm_α_β2ψ_ψ :
  forall_ijk_tuv ψ α β2ψ,
    {ψ, i, t} * ⁅{α, j, u}, {β2ψ, k, v}⁆ = ⁅{α, j, u}, {β2ψ, k, v}⁆ * {ψ, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_ψ_α_β2ψ hi hj hk t u v)

-- 8.128
theorem comm_of_α_αβψ_ψ :
  forall_ijk_tuv α αβψ ψ,
    ⁅{α, i, t}, ⁅{αβψ, j, u}, {ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.mpr
  rw [commutatorElement_def]
  grw [inv_of_αβψ hj, expr_α_αβψ_as_αβψ_α hi hj, expr_α_ψ_as_ψ_α hi hk,
  expr_α_αβψ_as_αβψ_α hi hj, expr_α_ψ_as_ψ_α hi hk]

@[group_reassoc]
theorem expr_α_comm_αβψ_ψ_as_comm_αβψ_ψ_α :
  forall_ijk_tuv α αβψ ψ,
    {α, i, t} * ⁅{αβψ, j, u}, {ψ, k, v}⁆ = ⁅{αβψ, j, u}, {ψ, k, v}⁆ * {α, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_α_αβψ_ψ hi hj hk t u v)

include Fchar
-- 8.129
theorem comm_of_α_α_β2ψ :
  forall_ijk_tuv α α β2ψ,
    ⁅{α, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  rcases decompose_3_into_booleans_1_2 k hk with ⟨ j', k', ⟨ rfl, hj', hk' ⟩ ⟩
  have : v = -2 * v * (-1 / 2) := by field_simp
  rw [this, ←lift_hom_interchange_of_αβ2ψ hj hj' hk', expr_α_comm_αβψ_ψ_as_comm_αβψ_ψ_α hi (by linarith) hk']

@[group_reassoc]
theorem expr_α_comm_α_β2ψ_as_comm_α_β2ψ_α :
  forall_ijk_tuv α α β2ψ,
    {α, i, t} * ⁅{α, j, u}, {β2ψ, k, v}⁆ = ⁅{α, j, u}, {β2ψ, k, v}⁆ * {α, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_α_α_β2ψ Fchar hi hj hk t u v)

-- Proposition 8.130
theorem sufficient_conditions_for_comm_of_αβψ_and_ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 1)
  (hyp : ∀ (t u v : F), ⁅{βψ, j, t}, ⁅{α, i, u}, {β2ψ, j + k, v}⁆⁆ = 1),
  ∀ (t u v : F), ⁅{αβψ, i + j, t * u}, {ψ, k, v}⁆ = ⁅{α, i, t}, {β2ψ, j + k, -2 * u * v}⁆ := by
  intro i j k hi hj hk hyp t u v
  apply eq_comm_of_reorder_left
  grw [expr_αβψ_as_βψ_α_βψ_α_βψ hi hj, expr_βψ_ψ_as_ψ_β2ψ_βψ hk hj, expr_α_ψ_as_ψ_α hi hk, expr_βψ_ψ_as_ψ_β2ψ_βψ hk hj, expr_α_ψ_as_ψ_α hi hk, expr_βψ_ψ_as_ψ_β2ψ_βψ hk hj]
  have : -2 * v * (-u / 2) = u * v := by field_simp; group
  rw [this]
  have hyp' := fun t' u' v' ↦ triv_comm_iff_commutes.1 (hyp t' u' v')
  have aux₁ : {β2ψ, k + j, u * v} * {α, i, t} = ⁅{α, i, t}, {β2ψ, j + k, -u * v}⁆ * {α, i, t} * {β2ψ, j + k, u * v} := by
    rw [comm_left_rev, inv_of_comm_of_α_β2ψ hi (add_le_add hk hj), neg_mul]
    group
  have aux₂ : {α, i, -t} * {β2ψ, k + j, u * v} = {β2ψ, j + k, u * v} * {α, i, -t} * ⁅{α, i, t}, {β2ψ, j + k, -u * v}⁆ := by
    rw [← inv_of_α, neg_mul, ← inv_of_β2ψ]
    group
  have aux₃ := calc
   {β2ψ, j + k, u * v} * {β2ψ, k + j, -2 * v * u} = {β2ψ, j + k, u * v} * {β2ψ, j + k, -2 * u * v} := by group
   _ = {β2ψ, j + k, -u * v} := by rw [lin_of_β2ψ]; ring_nf
  have aux₄ : {β2ψ, j + k, -u * v} * {β2ψ, j + k, u * v} = 1 := by
    rw [neg_mul, ← inv_of_β2ψ, inv_mul_cancel]
  grw [←expr_βψ_β2ψ_as_β2ψ_βψ hj (add_le_add hk hj) (-u / 2), aux₁, aux₂,
  expr_βψ_β2ψ_as_β2ψ_βψ hj (add_le_add hj hk) u (u * v), aux₃, aux₄, hyp' (-u/2),
  expr_ψ_comm_α_β2ψ_as_comm_α_β2ψ_ψ hk hi (add_le_add hj hk), expr_α_comm_α_β2ψ_as_comm_α_β2ψ_α Fchar hi hi (add_le_add hj hk)]
  field_simp
  grw [hyp' u, expr_α_comm_α_β2ψ_as_comm_α_β2ψ_α Fchar hi hi (add_le_add hj hk), hyp' (-u/2), expr_ψ_comm_α_β2ψ_as_comm_α_β2ψ_ψ hk hi (add_le_add hj hk),
  lift_hom_inv_doub_of_α_β2ψ_c hi (add_le_add hj hk)]
  group

-- 8.131
theorem partial_A_interchange_of_αβ2ψ :
  ∀ (t u v : F),
  ⁅{αβψ, 0, t * u}, {ψ, 1, v}⁆ = ⁅{α, 0, t}, {β2ψ, 1, -2 * u * v}⁆ := by
  apply @sufficient_conditions_for_comm_of_αβψ_and_ψ _ _ Fchar 0 0 1 (by trivial) (by trivial) (by trivial)
  intro t u v
  have h₁ := @lift_hom_interchange_of_αβ2ψ _ _ 1 0 0 (by trivial) (by trivial) (by trivial) u (-v/2) 1
  have h := @lift_hom_interchange_of_αβ2ψ _ _ 0 1 0 (by trivial) (by trivial) (by trivial) u (-v/2) 1
  norm_num at h₁
  norm_num at h
  rw [h₁] at h
  have : -(2 * (-v / 2)) = v := by field_simp
  rw [this] at h
  have h₁ := @lift_hom_comm_of_βψ_α_β2ψ _ _ 1 0 0 (by trivial) (by trivial) (by trivial) t u v
  rwa [h] at h₁


-- Proposition 8.132
theorem sufficient_conditions_for_comm_of_βψ_and_α_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 3) (hyp : ∀ (t u : F), ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1),
  ∀ (t u v : F), ⁅{βψ, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk hyp t u v
  apply triv_comm_iff_commutes.2
  have hyp' := fun t' u' ↦ triv_comm_iff_commutes.1 (hyp t' u')
  have aux₁ : ∀ (u' : F), {βψ, i, t} * {α, j, u'} = {α, j, u'} * ⁅{α, j, -u'}, {βψ, i, t}⁆ * {βψ, i, t} := by
    intro u'; rw [← inv_of_α]; group
  have aux₂ : ∀ (u' : F), {βψ, i, t} * {α, j, u'} = ⁅{α, j, u'}, {βψ, i, t}⁆⁻¹ * {α, j, u'} * {βψ, i, t} := by
    intro u'; group
  grw [commutatorElement_def, ←inv_of_α, ←inv_of_β2ψ, aux₁ u, expr_βψ_β2ψ_as_β2ψ_βψ hi hk, aux₂ (-u), expr_βψ_β2ψ_as_β2ψ_βψ hi hk]
  suffices h : ⁅{α, j, -u}, {βψ, i, t}⁆ * {β2ψ, k, v} * ⁅{α, j, -u}, {βψ, i, t}⁆⁻¹ = {β2ψ, k, v} by
    have : ⁅{βψ, i, t}, {α, j, -u}⁆ = ⁅{α, j, -u}, {βψ, i, t}⁆⁻¹ := by rw [←inv_of_α]; group
    rw [this]; exact h
  apply mul_inv_eq_iff_eq_mul.2
  have := (generic_comm_of_α_βψ Fchar hj hi (-u) t).1
  field_simp at this
  have := calc
    ⁅{α, j, -u}, {βψ, i, t}⁆ = {αβψ, j + i, -(u * t)} * ⁅{αβψ, j + i, u * t}, {βψ, i, t / 2}⁆ := this
    _ = {αβψ, i + j, -t * u} * ⁅{αβψ, i + j, t * u}, {βψ, i, t / 2}⁆ := by group
  grw [this, commutatorElement_def, expr_βψ_β2ψ_as_β2ψ_βψ hi hk, inv_of_αβψ, ←hyp', ←hyp']
  rw [mul_assoc, hyp']
  grw [expr_βψ_β2ψ_as_β2ψ_βψ]
  exact add_le_add hi hj

-- 8.133
theorem partial_comm_of_βψ_α_β2ψ :
  ∀ (t u v : F),
  ⁅{βψ, 2, t}, ⁅{α, 0, u}, {β2ψ, 2, v}⁆⁆ = 1 := by
  apply @sufficient_conditions_for_comm_of_βψ_and_α_β2ψ _ _ Fchar 2 0 2 (by trivial) (by trivial) Nat.AtLeastTwo.prop
  intro t u
  have := triv_comm_iff_commutes.mp (@lift_hom_comm_of_β2ψ_αβψ _ _ 1 0 1 (by trivial) (by trivial) (by trivial) u t)
  apply triv_comm_iff_commutes.mpr
  rw [←this]

-- 8.134
theorem partial_B_interchange_of_αβ2ψ :
  ∀ (t u v : F),
  ⁅{αβψ, 2, t * u}, {ψ, 0, v}⁆ = ⁅{α, 0, t}, {β2ψ, 2, -2 * u * v}⁆ :=
  @sufficient_conditions_for_comm_of_αβψ_and_ψ _ _ Fchar 0 2 0 (by trivial) (by trivial) (by trivial) (@partial_comm_of_βψ_α_β2ψ _ _ Fchar)

/- ### Establishing α + β + 2ψ -/

private lemma interchange_of_αβ2ψ_trans_α_β2ψ :
  forall_ijk_tu 1 1 1, ⁅{α, i, t * u}, {β2ψ, j + 2 * k, 1}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, u}⁆ := by
  intro i j k hi hj hk t u
  have aux₁ := lift_hom_interchange_of_αβ2ψ hi hj hk (t * u) 1 (-1/2)
  have aux₂ := lift_hom_interchange_of_αβ2ψ hi hj hk t u (-1/2)
  field_simp at aux₁
  field_simp at aux₂
  rwa [aux₁] at aux₂

omit Fchar
private lemma interchange_of_αβ2ψ_refl_u :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t}, {ψ, k, u}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u}⁆ := by
  intro i j k hi hj hk t u
  rw [←mul_one t, lift_hom_interchange_of_αβ2ψ hi hj hk]
  simp only [neg_mul, mul_one]

private lemma interchange_of_αβ2ψ_refl_v :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t * u}, {ψ, k, 1}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u}⁆ := by
  intro i j k hi hj hk t u
  rw [lift_hom_interchange_of_αβ2ψ hi hj hk]
  simp only [neg_mul, mul_one]

private lemma interchange_of_αβ2ψ_trans_αβψ_ψ :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t * u}, {ψ, k, 1}⁆ = ⁅{αβψ, i + j + k, t}, {ψ, k, u}⁆ := by
  intro i j k hi hj hk t u
  rw [interchange_of_αβ2ψ_refl_v hi hj hk, interchange_of_αβ2ψ_refl_u hi hj hk]

include Fchar
private lemma interchange_A_of_αβ2ψ_refl_u :
  ∀ t u : F, ⁅{αβψ, 0, t}, {ψ, 1, u}⁆ = ⁅{α, 0, t}, {β2ψ, 1, -2 * u}⁆ := by
  intro t u
  rw [←mul_one t, partial_A_interchange_of_αβ2ψ Fchar]
  simp only [mul_one, neg_mul]

private lemma interchange_A_of_αβ2ψ_refl_v :
  ∀ t u : F, ⁅{αβψ, 0, t * u}, {ψ, 1, 1}⁆ = ⁅{α, 0, t}, {β2ψ, 1, -2 * u}⁆ := by
  intro t u
  rw [partial_A_interchange_of_αβ2ψ Fchar]
  simp only [neg_mul, mul_one]

private lemma interchange_A_of_αβ2ψ_trans_αβψ_ψ :
  ∀ t u : F, ⁅{αβψ, 0, t * u}, {ψ, 1, 1}⁆ = ⁅{αβψ, 0, t}, {ψ, 1, u}⁆ := by
  intro t u
  rw [interchange_A_of_αβ2ψ_refl_v Fchar, interchange_A_of_αβ2ψ_refl_u Fchar]

private lemma interchange_B_of_αβ2ψ_refl_u :
  ∀ t u : F, ⁅{αβψ, 2, t}, {ψ, 0, u}⁆ = ⁅{α, 0, t}, {β2ψ, 2, -2 * u}⁆ := by
  intro t u
  rw [←mul_one t, partial_B_interchange_of_αβ2ψ Fchar]
  simp only [mul_one, neg_mul]

private lemma interchange_B_of_αβ2ψ_refl_v :
  ∀ t u : F, ⁅{αβψ, 2, t * u}, {ψ, 0, 1}⁆ = ⁅{α, 0, t}, {β2ψ, 2, -2 * u}⁆ := by
  intro t u
  rw [partial_B_interchange_of_αβ2ψ Fchar]
  simp only [neg_mul, mul_one]

private lemma interchange_B_of_αβ2ψ_trans_αβψ_ψ :
  ∀ t u : F, ⁅{αβψ, 2, t * u}, {ψ, 0, 1}⁆ = ⁅{αβψ, 2, t}, {ψ, 0, u}⁆ := by
  intro t u
  rw [interchange_B_of_αβ2ψ_refl_v Fchar, interchange_B_of_αβ2ψ_refl_u Fchar]

-- height 0
private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_00 :
  ∀ t u : F, {αβ2ψ, 0, t * u} = ⁅{α, 0, t}, {β2ψ, 0, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 0 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_00 :
  ∀ t u : F, {αβ2ψ, 0, -2 * t * u} = ⁅{αβψ, 0, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_00 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 0 0 0 (by trivial) (by trivial) (by trivial),
  mul_comm t u, interchange_of_αβ2ψ_trans_αβψ_ψ (by trivial) (by trivial) (by trivial)]

-- height 1
private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_01 :
  ∀ t u : F, {αβ2ψ, 1, t * u} = ⁅{α, 0, t}, {β2ψ, 1, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 1 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]

-- `A` edge
private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_01 :
  ∀ t u : F, {αβ2ψ, 1, -2 * t * u} = ⁅{αβψ, 0, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_01 Fchar, ←interchange_A_of_αβ2ψ_refl_v Fchar,
  mul_comm t u, interchange_A_of_αβ2ψ_trans_αβψ_ψ Fchar]

private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_10 :
  ∀ t u : F, {αβ2ψ, 1, -2 * t * u} = ⁅{αβψ, 1, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_01 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 0 1 0 (by trivial) (by trivial) (by trivial),
  mul_comm t u, @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_10 :
  ∀ t u : F, {αβ2ψ, 1, t * u} = ⁅{α, 1, t}, {β2ψ, 0, u}⁆ := by
  intro t u
  have : t * u = -2 * (-u / 2) * t := by ring_nf; field_simp
  rw [this, expr_αβ2ψ_as_comm_of_αβψ_ψ_10 Fchar, @interchange_of_αβ2ψ_refl_u _ _ 1 0 0 (by trivial) (by trivial) (by trivial)]
  field_simp

-- height 2
private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_11 :
  ∀ t u : F, {αβ2ψ, 2, t * u} = ⁅{α, 1, t}, {β2ψ, 1, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 2 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 1 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_20 :
  ∀ t u : F, {αβ2ψ, 2, -2 * t * u} = ⁅{αβψ, 2, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_11 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 1 1 0 (by trivial) (by trivial) (by trivial),
  mul_comm t u, @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]

-- `B` edge
private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_02 :
  ∀ t u : F, {αβ2ψ, 2, t * u} = ⁅{α, 0, t}, {β2ψ, 2, u}⁆ := by
  intro t u
  have : t * u = -2 * (-u / 2) * t := by ring_nf; field_simp
  rw [this, expr_αβ2ψ_as_comm_of_αβψ_ψ_20 Fchar, interchange_B_of_αβ2ψ_refl_u Fchar]
  field_simp

private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_11 :
  ∀ t u : F, {αβ2ψ, 2, -2 * t * u} = ⁅{αβψ, 1, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_02 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 0 0 1 (by trivial) (by trivial) (by trivial),
  mul_comm t u, interchange_of_αβ2ψ_trans_αβψ_ψ (by trivial) (by trivial) (by trivial)]

-- height 3
private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_12 :
  ∀ t u : F, {αβ2ψ, 3, t * u} = ⁅{α, 1, t}, {β2ψ, 2, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 3 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 1 0 1 (by trivial) (by trivial) (by trivial)]

-- `A` edge
private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_30 :
  ∀ t u : F, {αβ2ψ, 3, -2 * t * u} = ⁅{αβψ, 3, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = u * (-2 * t) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_12 Fchar]
  have : ⁅{αβψ, 3, u}, {ψ, 0, t}⁆ = ReflDeg.refl_symm b3large_valid ⁅{αβψ, 0, u}, {ψ, 1, t}⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this]
  have : ⁅{α, 1, u}, {β2ψ, 2, -2 * t}⁆ = ReflDeg.refl_symm b3large_valid ⁅{α, 0, u}, {β2ψ, 1, -2 * t}⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, interchange_A_of_αβ2ψ_refl_u Fchar]

private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_21 :
  ∀ t u : F, {αβ2ψ, 3, -2 * t * u} = ⁅{αβψ, 2, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = u * (-2 * t) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_12 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 1 0 1 (by trivial) (by trivial) (by trivial),
  @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_03 :
  ∀ t u : F, {αβ2ψ, 3, t * u} = ⁅{α, 0, t}, {β2ψ, 3, u}⁆ := by
  intro t u
  have : t * u = -2 * (-u / 2) * t := by ring_nf; field_simp
  rw [this, expr_αβ2ψ_as_comm_of_αβψ_ψ_21 Fchar, @interchange_of_αβ2ψ_refl_u _ _ 0 1 1 (by trivial) (by trivial) (by trivial)]
  field_simp

-- height 4
private lemma expr_αβ2ψ_as_comm_of_α_β2ψ_13 :
  ∀ t u : F, {αβ2ψ, 4, t * u} = ⁅{α, 1, t}, {β2ψ, 3, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 4 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 1 1 1 (by trivial) (by trivial) (by trivial)]

private lemma expr_αβ2ψ_as_comm_of_αβψ_ψ_31 :
  ∀ t u : F, {αβ2ψ, 4, -2 * t * u} = ⁅{αβψ, 3, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = u * (-2 * t) := by group
  rw [this, expr_αβ2ψ_as_comm_of_α_β2ψ_13 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 1 1 1 (by trivial) (by trivial) (by trivial),
  @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]

-- 8.135a
theorem expr_αβ2ψ_as_comm_of_α_β2ψ :
  forall_ij_tu 1 3,
    {αβ2ψ, i + j, t * u} = ⁅{α, i, t}, {β2ψ, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_00 Fchar]
  | 0, 1 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_01 Fchar]
  | 1, 0 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_10 Fchar]
  | 0, 2 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_02 Fchar]
  | 1, 1 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_11 Fchar]
  | 0, 3 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_03 Fchar]
  | 1, 2 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_12 Fchar]
  | 1, 3 => rw [expr_αβ2ψ_as_comm_of_α_β2ψ_13 Fchar]

-- 8.135b
theorem expr_αβ2ψ_as_comm_of_αβψ_ψ :
  forall_ij_tu 3 1,
    {αβ2ψ, i + j, -2 * t * u} = ⁅{αβψ, i, u}, {ψ, j, t}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_00 Fchar]
  | 1, 0 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_10 Fchar]
  | 0, 1 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_01 Fchar]
  | 1, 1 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_11 Fchar]
  | 2, 0 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_20 Fchar]
  | 2, 1 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_21 Fchar]
  | 3, 0 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_30 Fchar]
  | 3, 1 => rw [expr_αβ2ψ_as_comm_of_αβψ_ψ_31 Fchar]

-- 8.136
theorem comm_of_α_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk α αβ2ψ := by
  intro i j hi hj t u
  rcases decompose 3 1 j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  have expr_αβ2ψ := @expr_αβ2ψ_as_comm_of_αβψ_ψ _ _ Fchar j₁ j₂ hj₁ hj₂ (-1/2) u
  field_simp at expr_αβ2ψ
  have := @comm_of_α_αβψ_ψ _ _ i j₁ j₂ hi hj₁ hj₂ t u (-1/2)
  rwa [←expr_αβ2ψ] at this
declare_B3Large_triv_expr_thm F α αβ2ψ

-- 8.137
theorem comm_of_ψ_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk ψ αβ2ψ := by
  intro i j hi hj t u
  rcases decompose 3 1 j hj with ⟨ j₂, j₁, ⟨ rfl, hj₂, hj₁ ⟩ ⟩
  have expr_αβ2ψ := @expr_αβ2ψ_as_comm_of_α_β2ψ _ _ Fchar j₁ j₂ hj₁ hj₂ 1 u
  have := @comm_of_ψ_α_β2ψ _ _ i j₁ j₂ hi hj₁ hj₂ t 1 u
  rw [←expr_αβ2ψ] at this
  rw [←this]
  group
declare_B3Large_triv_expr_thm F ψ αβ2ψ

-- 8.138a
@[simp, chev_simps]
private lemma inv_doub_of_αβ2ψ_a :
  forall_i_t αβ2ψ,
    {αβ2ψ, i, t} * {αβ2ψ, i, -t} = 1 := by
  intro i hi t
  rcases decompose 3 1 i hi with ⟨ i₂, i₁, ⟨ rfl, hi₂, hi₁ ⟩ ⟩
  have := @expr_αβ2ψ_as_comm_of_α_β2ψ _ _ Fchar i₁ i₂ hi₁ hi₂
  calc
    {αβ2ψ, i₂ + i₁, t} * {αβ2ψ, i₂ + i₁, -t} = {αβ2ψ, i₁ + i₂, t * 1} * {αβ2ψ, i₁ + i₂, t * (-1)} := by group
    _ = ⁅{α, i₁, t}, {β2ψ, i₂, 1}⁆ * ⁅{α, i₁, t}, {β2ψ, i₂, -1}⁆ := by rw [this t 1, this t (-1)]
    _ = 1 := by rw [lift_hom_inv_doub_of_α_β2ψ_b hi₁ hi₂]

@[simp, chev_simps]
theorem inv_of_αβ2ψ :
  forall_i_t αβ2ψ,
    {αβ2ψ, i, t}⁻¹ = {αβ2ψ, i, -t} := by
  intro i hi t
  have := @inv_doub_of_αβ2ψ_a _ _ Fchar i hi t
  rw [eq_inv_of_mul_eq_one_left this, inv_inv]

-- 8.138b
theorem doub_of_αβ2ψ :
  forall_i_t αβ2ψ.height,
    {αβ2ψ, i, t} * {αβ2ψ, i, t} = {αβ2ψ, i, 2 * t} := by
  intro i hi t
  rcases decompose 3 1 i hi with ⟨ i₂, i₁, ⟨ rfl, hi₂, hi₁ ⟩ ⟩
  have := @expr_αβ2ψ_as_comm_of_α_β2ψ _ _ Fchar i₁ i₂ hi₁ hi₂
  calc
    {αβ2ψ, i₂ + i₁, t} * {αβ2ψ, i₂ + i₁, t} = {αβ2ψ, i₁ + i₂, 1 * t} * {αβ2ψ, i₁ + i₂, 1 * t} := by group
    _ = ⁅{α, i₁, (1 : F)}, {β2ψ, i₂, t}⁆ * ⁅{α, i₁, (1 : F)}, {β2ψ, i₂, t}⁆ := by rw [this]
    _ = ⁅{α, i₁, (1 : F)}, {β2ψ, i₂, 2 * t}⁆ := by rw [lift_hom_inv_doub_of_α_β2ψ_c hi₁ hi₂]
    _ = {αβ2ψ, i₂ + i₁, 2 * t} := by rw [←this]; group

-- 8.139a
theorem commutator_of_αβ_ψ_a :
  forall_ij_tu 2 1,
    ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, t * u^2} := by
  intro i j hi hj t u
  have aux := expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar (add_le_add hi hj) hj (u / 2) (-t * u)
  have : {αβ2ψ, i + j + j, -2 * (u / 2) * (-t * u)} = {αβ2ψ, i + 2 * j, t * u^2} := by ring_nf; field_simp
  rw [this] at aux
  rw [(generic_comm_of_αβ_ψ Fchar hi hj t u).1, aux]

-- 8.139b
theorem commutator_of_αβ_ψ_b :
  forall_ij_tu 2 1,
    ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβ2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} := by
  intro i j hi hj t u
  have aux := expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar (add_le_add hi hj) hj (u / 2) (t * u)
  rw [(generic_comm_of_αβ_ψ Fchar hi hj t u).2, ←aux, inv_of_αβ2ψ Fchar (by ht)]
  ring_nf; field_simp

-- 8.140a
theorem expr_αβ2ψ_as_α_β2ψ_α_β2ψ :
  forall_ij_tu α β2ψ,
    {αβ2ψ, i + j, t * u} = {α, i, t} * {β2ψ, j, u} * {α, i, -t} * {β2ψ, j, -u} := by
  intro i j hi hj t u
  rw [expr_αβ2ψ_as_comm_of_α_β2ψ Fchar hi hj, ← inv_of_α, ← inv_of_β2ψ, commutatorElement_def]

-- 8.140b
theorem expr_αβ2ψ_as_β2ψ_α_β2ψ_α :
  forall_ij_tu α β2ψ,
    {αβ2ψ, i + j, t * u} = {β2ψ, j, -u} * {α, i, t} * {β2ψ, j, u} * {α, i, -t} := by
  intro i j hi hj t u
  calc
    {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, t * (-u)}⁻¹ := by rw [inv_of_αβ2ψ Fchar (add_le_add hi hj)]; group
    _ = ⁅{α, i, t}, {β2ψ, j, -u}⁆⁻¹ := by rw [expr_αβ2ψ_as_comm_of_α_β2ψ Fchar hi hj]
    _ = ⁅{α, i, t}, {β2ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_β2ψ]
    _ = {β2ψ, j, -u} * {α, i, t} * {β2ψ, j, u} * {α, i, -t} := by rw [← inv_of_β2ψ, ← inv_of_α]; group

-- 8.141a
theorem expr_αβ2ψ_as_αβψ_ψ_αβψ_ψ :
  forall_ij_tu αβψ ψ,
    {αβ2ψ, i + j, -2 * t * u} = {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} * {ψ, j, -t} := by
  intro i j hi hj t u
  rw [expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar hi hj, ← inv_of_αβψ hi, ← inv_of_ψ hj, commutatorElement_def];

-- 8.141b
theorem expr_αβ2ψ_as_ψ_αβψ_ψ_αβψ :
  forall_ij_tu αβψ ψ,
    {αβ2ψ, i + j, -2 * t * u} = {ψ, j, -t} * {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} := by
  intro i j hi hj t u
  calc
    {αβ2ψ, i + j, -2 * t * u} = {αβ2ψ, i + j, -2 * (-t) * u}⁻¹ := by rw [inv_of_αβ2ψ Fchar (add_le_add hi hj)]; group
    _ = ⁅{αβψ, i, u}, {ψ, j, -t}⁆⁻¹ := by rw [expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar hi hj]
    _ = ⁅{αβψ, i, u}, {ψ, j, t}⁻¹⁆⁻¹ := by rw [inv_of_ψ]
    _ = {ψ, j, -t} * {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} := by rw [← inv_of_ψ hj, ← inv_of_αβψ hi]; group

-- 8.142a
@[group_reassoc]
theorem expr_α_β2ψ_as_αβ2ψ_β2ψ_α :
  forall_ij_tu α β2ψ,
    {α, i, t} * {β2ψ, j, u} = {αβ2ψ, i + j, t * u} * {β2ψ, j, u} * {α, i, t} := by
  intro i j hi hj t u
  rw [expr_αβ2ψ_as_comm_of_α_β2ψ Fchar hi hj]
  group

-- 8.142b
@[group_reassoc]
theorem expr_α_β2ψ_as_β2ψ_αβ2ψ_α :
  forall_ij_tu α β2ψ,
    {α, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {αβ2ψ, i + j, t * u} * {α, i, t} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, t * (-u)}⁻¹ := by rw [inv_of_αβ2ψ Fchar (add_le_add hi hj)]; group
    _ = ⁅{α, i, t}, {β2ψ, j, -u}⁆⁻¹ := by rw [expr_αβ2ψ_as_comm_of_α_β2ψ Fchar hi hj]
    _ = ⁅{α, i, t}, {β2ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_β2ψ]
  rw [this]
  group

-- 8.142c
@[group_reassoc]
theorem expr_α_β2ψ_as_β2ψ_α_αβ2ψ :
  forall_ij_tu α β2ψ,
    {α, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {α, i, t} * {αβ2ψ, i + j, t * u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, (-t) * (-u)} := by group
    _ = ⁅{α, i, -t}, {β2ψ, j, -u}⁆ := by rw [expr_αβ2ψ_as_comm_of_α_β2ψ Fchar hi hj]
    _ = ⁅{α, i, t}⁻¹, {β2ψ, j, u}⁻¹⁆ := by rw [inv_of_β2ψ, inv_of_α]
  rw [this]
  group

-- 8.143a
@[group_reassoc]
theorem expr_ψ_αβψ_as_αβψ_αβ2ψ_ψ :
  forall_ij_tu ψ αβψ,
    {ψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {αβ2ψ, i + j, 2 * t * u} * {ψ, i, t} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, 2 * t * u} = {αβ2ψ, j + i, -2 * t * (-u)} := by group
    _ = ⁅{αβψ, j, u}⁻¹, {ψ, i, t}⁆ := by rw [expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar hj hi, inv_of_αβψ hj]
  rw [this]
  group

-- 8.143b
@[group_reassoc]
theorem expr_ψ_αβψ_as_αβψ_ψ_αβ2ψ :
  forall_ij_tu ψ αβψ,
    {ψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {ψ, i, t} * {αβ2ψ, i + j, 2 * t * u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, 2 * t * u} = {αβ2ψ, j + i, -2 * (-t) * (-u)}⁻¹ := by rw [inv_of_αβ2ψ Fchar (by ht)]; group
    _ = ⁅{αβψ, j, u}⁻¹, {ψ, i, t}⁻¹⁆⁻¹ := by rw [expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar hj hi, inv_of_αβψ hj, inv_of_ψ]
  rw [this]
  group

-- 8.144a
@[group_reassoc]
theorem expr_αβψ_ψ_as_αβ2ψ_ψ_αβψ :
  forall_ij_tu ψ αβψ,
    {αβψ, j, u} * {ψ, i, t} = {αβ2ψ, i + j, -2 * t * u} * {ψ, i, t} * {αβψ, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, -2 * t * u} = {αβ2ψ, j + i, -2 * t * u} := by group
    _ = ⁅{αβψ, j, u}, {ψ, i, t}⁆ := by rw [expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar hj hi]
  rw [this]
  group

-- 8.144b
@[group_reassoc]
theorem expr_αβψ_ψ_as_ψ_αβ2ψ_αβψ :
  forall_ij_tu ψ αβψ,
    {αβψ, j, u} * {ψ, i, t} = {ψ, i, t} * {αβ2ψ, i + j, -2 * t * u} * {αβψ, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, -2 * t * u} = {αβ2ψ, j + i, -2 * (-t) * u}⁻¹ := by rw [inv_of_αβ2ψ Fchar (by ht)]; group
    _ = ⁅{αβψ, j, u}, {ψ, i, t}⁻¹⁆⁻¹ := by rw [expr_αβ2ψ_as_comm_of_αβψ_ψ Fchar hj hi, inv_of_ψ]
  rw [this]
  group

-- 8.145a
@[group_reassoc]
theorem expr_αβ_ψ_as_ψ_αβ_αβψ_αβ2ψ :
  forall_ij_tu 2 1,
    {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβ, i, t} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} := by
  intro i j hi hj t u
  have aux := calc
    {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} = {αβψ, i + j, (-t) * (-u)} * {αβ2ψ, i + 2 * j, -t * (-u)^2} := by ring_nf
    _ = ⁅{αβ, i, -t}, {ψ, j, -u}⁆ := by rw [commutator_of_αβ_ψ_a Fchar hi hj]
  have := calc
    {ψ, j, u} * {αβ, i, t} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u ^ 2}
    = {ψ, j, u} * {αβ, i, t} * ({αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2}) := rfl
    _ = {ψ, j, u} * {αβ, i, t} * ⁅{αβ, i, -t}, {ψ, j, -u}⁆ := by rw [aux]
    _ = {ψ, j, u} * {αβ, i, t} * ⁅{αβ, i, t}⁻¹, {ψ, j, u}⁻¹⁆ := by rw [inv_of_αβ, inv_of_ψ]
    _ = {αβ, i, t} * {ψ, j, u} := by group
  exact this.symm

-- 8.145b
@[group_reassoc]
theorem expr_αβ_ψ_as_ψ_αβψ_αβ2ψ_αβ :
  forall_ij_tu 2 1,
    {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβ, i, t} := by
  intro i j hi hj t u
  have aux : {ψ, j, u} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβ, i, t} = {ψ, j, u} * ({αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2}) * {αβ, i, t} := rfl
  have := calc
    {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} = {αβψ, i + j, t * (-u)}⁻¹ * {αβ2ψ, i + 2 * j, t * u^2}⁻¹ := by
      rw [inv_of_αβ2ψ Fchar (by ht), inv_of_αβψ (by ht)]; field_simp
    _ = ({αβ2ψ, i + 2 * j, t * (-u)^2} * {αβψ, i + j, t * (-u)})⁻¹ := by ring_nf; group
    _ = ⁅{αβ, i, t}, {ψ, j, -u}⁆⁻¹ := by rw [commutator_of_αβ_ψ_b Fchar hi hj]
    _ = ⁅{αβ, i, t}, {ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_ψ]
  rw [aux, this]
  group

-- 8.145c
@[group_reassoc]
theorem expr_αβ_ψ_as_ψ_αβ2ψ_αβψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (t u : F),
  {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u} * {αβ, i, t} := by
  intro i j hi hj t u
  have aux : {ψ, j, u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u} * {αβ, i, t} = {ψ, j, u} * ({αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u}) * {αβ, i, t} := rfl
  have := calc
    {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u} = {αβ2ψ, i + 2 * j, t * (-u)^2}⁻¹ * {αβψ, i + j, t * (-u)}⁻¹ := by rw [inv_of_αβ2ψ Fchar (by ht), inv_of_αβψ (by ht)]; field_simp
    _ = ({αβψ, i + j, t * (-u)} * {αβ2ψ, i + 2 * j, t * (-u)^2})⁻¹ := by group
    _ = ⁅{αβ, i, t}, {ψ, j, -u}⁆⁻¹ := by rw [commutator_of_αβ_ψ_a Fchar hi hj]
    _ = ⁅{αβ, i, t}, {ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_ψ]
  rw [aux, this]
  group

-- 8.145d
@[group_reassoc]
theorem expr_αβ_ψ_as_αβ2ψ_αβψ_ψ_αβ :
  forall_ij_tu 2 1,
    {αβ, i, t} * {ψ, j, u} = {αβ2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} * {ψ, j, u} * {αβ, i, t} := by
  intro i j hi hj t u
  rw [←commutator_of_αβ_ψ_b Fchar hi hj]
  group

-- 8.146
@[group_reassoc]
theorem expr_ψ_αβ_as_αβ_αβ2ψ_αβψ_ψ :
  forall_ij_tu αβ ψ,
    {ψ, j, u} * {αβ, i, t} = {αβ, i, t} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, -t * u} * {ψ, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, -t * u} = ⁅{αβ, i, -t}, {ψ, j, u}⁆ := by rw [commutator_of_αβ_ψ_b Fchar hi hj]
    _ = ⁅{αβ, i, t}⁻¹, {ψ, j, u}⁆ := by rw [inv_of_αβ]
  grw [this]
  rw [←inv_of_αβ]
  group

@[simp, chev_simps]
theorem id_of_αβψ : id_of_root((weakB3Large F).pres_mk, αβψ) := by
  intro i hi
  have := doub_of_αβψ Fchar hi 0
  rw [mul_zero] at this
  exact mul_right_eq_self.1 this

@[simp, chev_simps]
theorem id_of_αβ2ψ : id_of_root((weakB3Large F).pres_mk, αβ2ψ) := by
  intro i hi
  have := doub_of_αβ2ψ Fchar hi 0
  rw [mul_zero] at this
  exact mul_right_eq_self.1 this

set_option maxHeartbeats 0

-- 8.147a
theorem hom_lift_of_interchange_of_α2β2ψ_a : forall_ijk_tuv,
    ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, 2 * u * v}⁆ = ⁅{αβψ, i + j + k, t * u}, {βψ, j + k, v}⁆ := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, mul_zero, mul_zero, zero_mul, id_of_β2ψ, id_of_αβψ Fchar]; group
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, mul_zero, id_of_βψ, id_of_β2ψ]; group
  have aux := raw_hom_lift_of_interchange_of_α2β2ψ_a hi hj hk (t * u / v) (v / u) u
  have : t * u / v * (v / u) = t := by field_simp
  rw [this] at aux
  have : 2 * (v / u) * u ^ 2 = 2 * u * v := by calc
    2 * (v / u) * u ^ 2 = 2 * v * (u^2 / u) := by field_simp
    _ = 2 * v * (u * u / u) := by rw [pow_two]
    _ = 2 * v * u := by rw [mul_div_assoc, div_self hu, mul_one]
    _ = 2 * u * v := mul_right_comm 2 v u
  rw [this] at aux
  have : -(t * u / v) * (v / u) = -t := by ring_nf; field_simp
  rw [this] at aux
  have : v / u * u = v := div_mul_cancel₀ v hu
  rw [this] at aux
  grw [aux, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ (add_le_add hi hj) hk]

-- 8.147b
theorem hom_lift_of_interchange_of_α2β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u v : F),
  ⁅{αβψ, i + j + k, t}, {βψ, j + k, u * v}⁆ = ⁅{αβ2ψ, i + j + 2 * k, 2 * t * u}, {β, j, v}⁆ := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, mul_zero, zero_mul, id_of_βψ, id_of_αβ2ψ Fchar]; group
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, mul_zero, id_of_βψ, id_of_β]; group
  have aux := raw_hom_lift_of_interchange_of_α2β2ψ_b hi hj hk (t / (u * v)) v u
  have : t / (u * v) * v = t / u := by field_simp; group
  rw [this] at aux
  have : -(t / (u * v)) * v = -(t / u) := by field_simp; group
  rw [this] at aux
  grw [← expr_αβψ_as_ψ_αβ_ψ_αβ_ψ (add_le_add hi hj) hk] at aux
  field_simp at aux;
  have : u * v = v * u := by exact CommMonoid.mul_comm u v
  rw [← this] at aux; rw [aux]
  grw [commutatorElement_def, commutatorElement_def,
      commutatorElement_def, commutatorElement_def, inv_of_αβ2ψ]
  have : t / (u * v) * 2 * v * u ^ 2 = 2 * t * u := by
      grw [CommMonoid.mul_comm]
      field_simp
      group
  have h1 : {αβ2ψ, i + (j + 2 * k), t / (u * v) * 2 * v * u ^ 2} =
         {αβ2ψ, i + j + 2 * k, 2 * t * u} := by
    rw [this]
    simp only [← add_assoc]
  have h2 : {αβ2ψ, i + (j + 2 * k), -(t / (u * v) * 2 * v * u ^ 2)} =
         {αβ2ψ, i + j + 2 * k, -(2 * t * u)} := by
    grw [neg_inj]
    have : -(t / (u * v) * 2 * v * u ^ 2) = -(2 * t * u) := by
      rw [neg_inj]
      exact this
    rw [this]
    simp only [← add_assoc]
  have h3 := @expr_αβ2ψ_as_β2ψ_α_β2ψ_α F _ Fchar i (j + 2 * k) hi (by norm_num; omega) (t / (u * v)) (-2 * v * u^2)
  have h4 := @expr_αβ2ψ_as_α_β2ψ_α_β2ψ F _ Fchar i (j + 2 * k) hi (by norm_num; omega) (t / (u * v)) (2 * v * u^2)
  norm_num at h3; norm_num at h4
  grw [← h4, ← h1, ← h3, ← h2]
  assumption; norm_num; omega

-- 8.148
omit Fchar
theorem hom_lift_of_comm_ψ_αβ_β2ψ : forall_ijk_tuv,
    ⁅{ψ, k, t}, ⁅{αβ, i + j, u}, {β2ψ, j + 2 * k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_ψ]; group
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, id_of_β2ψ]; group
  have aux := raw_hom_lift_of_comm_of_ψ_αβ_β2ψ hi hj hk (u * t * t / v) (v / (t * t)) t
  have : u * t * t / v * (v / (t * t)) = u := by ring_nf; field_simp
  rw [this] at aux
  have : v / (t * t) * t ^ 2 = v := by ring_nf; field_simp
  rw [this] at aux
  exact aux

-- 8.149
theorem hom_lift_of_comm_αβ_αβ_β2ψ : forall_ijk_tu α β ψ,
    ⁅{αβ, i + j, t}, ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆⁆ = 1 ∧
  ⁅{αβ, i + j, t}, ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, u}⁆⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, id_of_β2ψ]
    exact ⟨by group, by group⟩
  have aux₁ := raw_hom_lift_of_comm_of_αβ_αβ_β2ψ_a hi hj hk (t / u) u 1
  have aux₂ := raw_hom_lift_of_comm_of_αβ_αβ_β2ψ_b hi hj hk (t / u) u 1
  have : t / u * u = t := by field_simp
  rw [this, pow_two, one_mul, mul_one] at aux₁
  rw [this, pow_two, one_mul, mul_one] at aux₂
  have : -(t / u) * u = -t := by field_simp
  rw [this] at aux₂
  exact ⟨aux₁, aux₂⟩

-- 8.150
theorem hom_lift_of_inv_doub_of_αβ_β2ψ : forall_ijk_tu α β ψ,
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ = ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, -u}⁆ ∧
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ * ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, u}⁆ = 1 ∧
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ * ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ = ⁅{αβ, i + j, 2 * t}, {β2ψ, j + 2 * k, u}⁆ := by
  intro i j k hi hj hk t u
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, neg_zero, id_of_β2ψ]
    exact ⟨by group, by group, by group⟩
  have aux₁ := raw_hom_lift_of_inv_doub_of_αβ_β2ψ_a hi hj hk (t / u) u 1
  have aux₂ := raw_hom_lift_of_inv_doub_of_αβ_β2ψ_b hi hj hk (t / u) u 1
  have aux₃ := raw_hom_lift_of_inv_doub_of_αβ_β2ψ_c hi hj hk (t / u) u 1
  have eq1 : (t / u) * u = t := by field_simp
  have eq2 : u * 1^2 = u := by rw [pow_two, mul_one, mul_one]
  have eq3 : -(t / u) * u = -t := by field_simp
  have eq4 : -u * 1^2 = -u := by rw [pow_two, mul_one, mul_one]
  have eq5 : 2 * (t / u) * u = 2 * t := by field_simp
  rw [eq1, eq2, eq3, eq4] at aux₁
  rw [eq1, eq2, eq3] at aux₂
  rw [eq1, eq2, eq5] at aux₃
  exact ⟨aux₁, aux₂, aux₃⟩

-- 8.151
include Fchar
theorem hom_lift_of_inv_doub_of_β_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u : F),
  ⁅{β, j, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = ⁅{β, j, -t}, {αβ2ψ, i + j + 2 * k, -u}⁆ ∧
  ⁅{β, j, t}, {αβ2ψ, i + j + 2 * k, u}⁆ * ⁅{β, j, -t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 ∧
  ⁅{β, j, t}, {αβ2ψ, i + j + 2 * k, u}⁆ * ⁅{β, j, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = ⁅{β, j, 2 * t}, {αβ2ψ, i + j + 2 * k, u}⁆ := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, neg_zero, mul_zero, id_of_β]
    group; tauto
  have aux₁ := raw_hom_lift_of_inv_doub_of_β_αβ2ψ_a hi hj hk (u / t) t 1
  have aux₂ := raw_hom_lift_of_inv_doub_of_β_αβ2ψ_b hi hj hk (u / t) t 1
  have aux₃ := raw_hom_lift_of_inv_doub_of_β_αβ2ψ_c hi hj hk (u / t) t 1
  field_simp at aux₁ aux₂ aux₃
  have h1 := @expr_αβ2ψ_as_α_β2ψ_α_β2ψ F _ Fchar i (j + 2 * k) hi (by norm_num; omega) (-(u/t)) (t)
  have h2 := @expr_αβ2ψ_as_α_β2ψ_α_β2ψ F _ Fchar i (j + 2 * k) hi (by norm_num; omega) (u/t) (t)
  norm_num at h1 h2; field_simp at h1 h2
  have eq1 : -u/t = -(u/t) := by field_simp
  simp only [← inv_of_β2ψ, eq1] at h1 h2
  simp only [← inv_of_α] at h2
  have : {α, i, u / t} = {α, i, -(u / t)}⁻¹ := by
    rw [inv_of_α]; norm_num
  rw [this] at h1
  grw [← commutatorElement_def] at h1 h2
  grw [eq_of_h_eq αβ2ψ (i + j + 2 * k) (by rw [add_assoc])] at h1 h2
  constructor
  · grw [h2, h1, ← eq1]
    assumption
  · constructor
    · grw [h2, h2]
      assumption
    · grw [h2, h2]
      assumption

-- 8.152
theorem hom_lift_of_comm_βψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u : F),
  ⁅{βψ, j + k, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_βψ]; group
  have aux := raw_hom_lift_of_comm_of_βψ_αβ2ψ hi hj hk (u / t) t 1
  rw [pow_two, mul_one, mul_one, mul_one] at aux
  have aux' := @expr_αβ2ψ_as_comm_of_α_β2ψ _ _ Fchar i (j + 2 * k) hi (by omega) (u / t) t
  have : {αβ2ψ, i + (j + 2 * k), u / t * t} = {αβ2ψ, i + j + 2 * k, u} := by field_simp; group
  rw [this] at aux'
  rw [aux', aux]

-- 8.153
theorem hom_lift_of_comm_of_β2ψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u : F),
  ⁅{β2ψ, j + 2 * k, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_β2ψ]; group
  have aux := raw_hom_lift_of_comm_of_β2ψ_αβ2ψ hi hj hk (u / t) t 1
  rw [pow_two, mul_one, mul_one] at aux
  have aux' := @expr_αβ2ψ_as_comm_of_α_β2ψ _ _ Fchar i (j + 2 * k) hi (by omega) (u / t) t
  have : {αβ2ψ, i + (j + 2 * k), u / t * t}  = {αβ2ψ, i + j + 2 * k, u} := by field_simp; group
  rw [this] at aux'
  rw [aux', aux]

-- 8.154
omit Fchar
theorem comm_of_βψ_αβ_β2ψ : forall_ijk_tuv βψ αβ β2ψ,
    ⁅{βψ, i, t}, ⁅{αβ, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, ←inv_of_αβ, ←inv_of_β2ψ, ←expr_αβ_βψ_as_βψ_αβ hj hi, expr_βψ_β2ψ_as_β2ψ_βψ hi hk,
  ←expr_αβ_βψ_as_βψ_αβ hj hi, expr_βψ_β2ψ_as_β2ψ_βψ hi hk]

@[group_reassoc]
theorem expr_βψ_comm_αβ_β2ψ_as_comm_αβ_β2ψ_βψ : forall_ijk_tuv βψ αβ β2ψ,
    {βψ, i, t} * ⁅{αβ, j, u}, {β2ψ, k, v}⁆ = ⁅{αβ, j, u}, {β2ψ, k, v}⁆ * {βψ, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_βψ_αβ_β2ψ hi hj hk t u v)

-- 8.155
theorem comm_of_αβ_βψ_αβψ : forall_ijk_tuv αβ βψ αβψ,
    ⁅{αβ, i, t}, ⁅{βψ, j, u}, {αβψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, ←inv_of_βψ, inv_of_αβψ hk, expr_αβ_βψ_as_βψ_αβ hi hj, expr_αβ_αβψ_as_αβψ_αβ hi hk,
  expr_αβ_βψ_as_βψ_αβ hi hj, expr_αβ_αβψ_as_αβψ_αβ hi hk]

@[group_reassoc]
theorem expr_αβ_comm_βψ_αβψ_as_comm_βψ_αβψ_αβ : forall_ijk_tuv αβ βψ αβψ,
    {αβ, i, t} * ⁅{βψ, j, u}, {αβψ, k, v}⁆ = ⁅{βψ, j, u}, {αβψ, k, v}⁆ * {αβ, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_αβ_βψ_αβψ hi hj hk t u v)

-- 8.156
theorem comm_of_β_αβ_β2ψ : forall_ijk_tuv β αβ β2ψ,
    ⁅{β, i, t}, ⁅{αβ, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, ←inv_of_αβ, ←inv_of_β2ψ, expr_β_αβ_as_αβ_β hi hj, expr_β_β2ψ_as_β2ψ_β hi hk,
  expr_β_αβ_as_αβ_β hi hj, expr_β_β2ψ_as_β2ψ_β hi hk]

@[group_reassoc]
theorem expr_β_comm_αβ_β2ψ_as_comm_αβ_β2ψ_β : forall_ijk_tuv β αβ β2ψ,
    {β, i, t} * ⁅{αβ, j, u}, {β2ψ, k, v}⁆ = ⁅{αβ, j, u}, {β2ψ, k, v}⁆ * {β, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_β_αβ_β2ψ hi hj hk t u v)

-- 8.157
theorem comm_of_β_αβψ_βψ : forall_ijk_tuv β αβψ βψ,
    ⁅{β, i, t}, ⁅{αβψ, j, u}, {βψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, inv_of_αβψ hj, expr_β_αβψ_as_αβψ_β hi hj, expr_β_βψ_as_βψ_β hi hk,
  expr_β_αβψ_as_αβψ_β hi hj, expr_β_βψ_as_βψ_β hi hk]

@[group_reassoc]
theorem expr_β_comm_αβψ_βψ_as_comm_αβψ_βψ_β : forall_ijk_tuv β αβψ βψ,
    {β, i, t} * ⁅{αβψ, j, u}, {βψ, k, v}⁆ = ⁅{αβψ, j, u}, {βψ, k, v}⁆ * {β, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_β_αβψ_βψ hi hj hk t u v)

include Fchar
-- 8.158 (revised)
theorem sufficient_conditions_for_comm_of_αβψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 2)
  (h35a : ∀ (t u v : F), ⁅{ψ, j, t}, ⁅{αβ, i, u}, {β2ψ, j + k, v}⁆⁆ = 1)
  (h35b : ∀ (t u : F), ⁅{αβ, i, t}, ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆⁆ = 1 ∧ ⁅{αβ, i, t}, ⁅{αβ, i, -t}, {β2ψ, j + k, u}⁆⁆ = 1)
  (h35c : ∀ (t u : F), ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, -t}, {β2ψ, j + k, -u}⁆)
  (h35d : ∀ (t u : F), ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ * ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u}⁆),
  ∀ (t u v : F), ⁅{αβψ, i + j, t * u}, {βψ, k, v}⁆ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ := by
  intro i j k hi hj hk h35a h35b h35c h35d t u v
  have h35a' := fun t' u' v' ↦ triv_comm_iff_commutes.1 (h35a t' u' v')
  have h35b₁ := fun t' u' ↦ triv_comm_iff_commutes.1 (h35b t' u').left
  have h35b₂ := fun t' u' ↦ triv_comm_iff_commutes.1 (h35b t' u').right
  have h35b₃ := fun t' u' ↦ triv_comm_iff_commutes.1 (h35b (-t') u').right
  norm_num at h35b₃
  have aux₀ : 2 * (-u / 2) * v = -u * v := by ring_nf; field_simp
  have eq36 : {β2ψ, j + k, -u * v} * {αβ, i, t} = {αβ, i, t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {β2ψ, j + k, -u * v} := by calc
    {β2ψ, j + k, -u * v} * {αβ, i, t} = {αβ, i, t} * ⁅{αβ, i, -t}, {β2ψ, j + k, -u * v}⁆ * {β2ψ, j + k, -u * v} := by
      rw [← inv_of_αβ, neg_mul, ← inv_of_β2ψ]; group
    _ = {αβ, i, t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {β2ψ, j + k, -u * v} := by grw [h35c]; ring_nf
  have eq37 : {αβ, i, -t} * {β2ψ, j + k, -u * v} = {β2ψ, j + k, -u * v} * {αβ, i, -t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ := by
    rw [← inv_of_αβ, neg_mul, ← inv_of_β2ψ]; group
  have := calc
    {αβψ, i + j, t * u} * {βψ, k, v} = {ψ, j, -u/2} * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * {ψ, j, -u/2} * {βψ, k, v} := by rw [expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi hj]
    _ = {βψ, k, v} * {ψ, j, -u/2} * {β2ψ, j + k, -u * v} * {αβ, i, t} * {β2ψ, j + k, 2 * u * v} * {ψ, j, u} * {αβ, i, -t} * {β2ψ, j + k, -u * v} * {ψ, j, -u/2} := by
      grw [expr_ψ_βψ_as_βψ_β2ψ_ψ hj hk, aux₀, expr_αβ_βψ_as_βψ_αβ hi hk, expr_ψ_βψ_as_βψ_β2ψ_ψ hj hk, expr_αβ_βψ_as_βψ_αβ hi hk, expr_ψ_βψ_as_βψ_ψ_β2ψ hj hk, aux₀]
    _ = {βψ, k, v} * {ψ, j, -u/2} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {αβ, i, t} * {β2ψ, j + k, -u * v} * {β2ψ, j + k, 2 * u * v} * {ψ, j, u} * {β2ψ, j + k, -u * v} * {αβ, i, -t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {ψ, j, -u/2} := by
      grw [eq36, eq37, h35b₁, h35b₂]
    _ = {βψ, k, v} * {ψ, j, -u/2} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {ψ, j, -u/2} := by
      grw [expr_ψ_β2ψ_as_β2ψ_ψ hj (add_le_add hj hk)]; ring_nf
      rw [id_of_β2ψ, one_mul]
    _ = ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {βψ, k, v} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {ψ, j, -u/2} * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * {ψ, j, -u/2} := by
      grw [h35a', expr_βψ_comm_αβ_β2ψ_as_comm_αβ_β2ψ_βψ hk hi (add_le_add hj hk), ← h35a', ← h35b₁, ← h35a', h35b₃]
    _ = ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {βψ, k, v} * {ψ, j, -u/2} * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * {ψ, j, -u/2} := by
      grw [expr_βψ_comm_αβ_β2ψ_as_comm_αβ_β2ψ_βψ hk hi (add_le_add hj hk)]
    _ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ * {βψ, k, v} * {αβψ, i + j, t * u} := by
      grw [h35d, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi hj]
  exact eq_comm_of_reorder_left this

lemma interchange_of_α2β2ψ_aux :
  ∀ (t u : F), ⁅{αβ, 1, t}, {β2ψ, 1, u}⁆ = ⁅{αβ, 0, t}, {β2ψ, 2, u}⁆ := by
    intro t u
    have := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    have this' := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 0 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at this'
    specialize this t (u/2) 1; norm_num at this; field_simp at this
    specialize this' t (u/2) 1; norm_num at this'; field_simp at this'
    exact Eq.trans this (Eq.symm this')

-- 8.159a
theorem partial_A_interchange_of_α2β2ψ_a :
  ∀ (t u v : F),
  ⁅{αβψ, 0, t * u}, {βψ, 2, v}⁆ = ⁅{αβ, 0, t}, {β2ψ, 2, 2 * u * v}⁆ := by
  have h1 := @hom_lift_of_comm_ψ_αβ_β2ψ F _ 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  have h2 := @hom_lift_of_comm_αβ_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h3 := @hom_lift_of_inv_doub_of_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h4 := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have := @sufficient_conditions_for_comm_of_αβψ_and_βψ _ _ Fchar 0 0 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  · intro t u v
    have := @interchange_of_α2β2ψ_aux _ _ Fchar u v
    rw [← this]
    specialize h1 t u v; norm_num at h1; exact h1
  · exact h2
  · exact fun t u ↦ (h3 t u).left
  · intro t u
    have h4a := h4 t 1 u; norm_num at h4a
    have h4b := h4 (2*t) (1/2) u; norm_num at h4b; field_simp at h4b
    specialize h3 t u
    grw [h3.right.right, h4a, h4b]

-- 8.159b
theorem partial_A_interchange_of_α2β2ψ_b :
  ∀ (t u v : F),
  ⁅{αβψ, 2, t * u}, {βψ, 0, v}⁆ = ⁅{αβ, 1, t}, {β2ψ, 1, 2 * u * v}⁆ := by
  have := @sufficient_conditions_for_comm_of_αβψ_and_βψ _ _ Fchar 1 1 0 (by norm_num) (by norm_num) (by norm_num)
  have h := @interchange_of_α2β2ψ_aux _ _ Fchar
  have h1 := @hom_lift_of_comm_ψ_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h2 := @hom_lift_of_comm_αβ_αβ_β2ψ F _ 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  have h3 := @hom_lift_of_inv_doub_of_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h4 := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  · intro t u v
    rw [h u v]
    specialize h1 t u v; norm_num at h1; exact h1
  · exact h2
  · intro t u
    have h1a := h t u
    have h1b := h (-t) (-u)
    grw [h1a, h1b]
    exact (h3 t u).left
  · intro t u
    specialize h3 t u; norm_num at h3
    rw [h t u]
    grw [h3.right.right]
    rw [h t (2*u)]
    have h4a := h4 t 1 u; norm_num at h4a
    have h4b := h4 (2*t) (1/2) u; norm_num at h4b; field_simp at h4b
    grw [h4a, h4b]

-- 8.160
include Fchar in
theorem more_sufficient_conditions_for_comm_of_αβψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 1)
  (h38a : ∀ (t u v : F), ⁅{β, k, t}, ⁅{αβ2ψ, i + j, u}, {β, k, v}⁆⁆ = 1)
  (h38b : ∀ (t u v : F), ⁅{ψ, j, t}, ⁅{αβ2ψ, i + j, u}, {β, k, v}⁆⁆ = 1)
  (h38c : ∀ (t u : F), ⁅{β, k, u}, {αβ2ψ, i + j, -t}⁆ = ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆)
  (h38d : ∀ (t u : F), ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆ * ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆ = ⁅{αβ2ψ, i + j, 2 * t}, {β, k, u}⁆),
  ∀ (t u v : F), ⁅{αβψ, i, t}, {βψ, j + k, u * v}⁆ = ⁅{αβ2ψ, i + j, 2 * t * u}, {β, k, v}⁆ := by
  intro i j k hi hj hk h38a h38b h38c h38d t u v
  have h39 : {αβ2ψ, i + j, t * u} * {β, k, v} = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {β, k, v} * {αβ2ψ, i + j, t * u} := by group
  have h40 : {β, k, -v} * {αβ2ψ, i + j, t * u}  = {αβ2ψ, i + j, t * u} * {β, k, -v} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ := by
    simp [← h38c, commutatorElement_def, inv_of_β]
    have h1 : {β, k, v}⁻¹ = {β, k, -v} := by grw [inv_of_β]
    have h2 : {αβ2ψ, i + j, t * u}⁻¹ = {αβ2ψ, i + j, -(t * u)} := by
      rw [inv_of_αβ2ψ Fchar (by ht)]
    grw [← h1, ← h2]
  have h : i + j ≤ αβ2ψ.height := by simp [height]; omega
  have : {αβψ, i, t} * {βψ, j + k, u * v} = ⁅{αβ2ψ, i + j, 2 * t * u}, {β, k, v}⁆ * {βψ, j + k, u * v} * {αβψ, i, t} := by
    nth_rw 1 [expr_βψ_as_ψ_β_ψ_β_ψ]
    grw [expr_αβψ_ψ_as_ψ_αβ2ψ_αβψ,
         ← expr_β_αβψ_as_αβψ_β,
         expr_αβψ_ψ_as_αβ2ψ_ψ_αβψ,
         ← expr_β_αβψ_as_αβψ_β]
    grw [expr_αβψ_ψ_as_αβ2ψ_ψ_αβψ]
    field_simp [add_comm, mul_comm, ← mul_assoc]
    grw [h39, h40]
    have : {ψ, j, u} * {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, t * u} * {ψ, j, u} := by
      rw [triv_comm_iff_commutes.1]
      rw [comm_of_ψ_αβ2ψ]
      exact Fchar
    grw [this]
    have : {αβ2ψ, i + j, t * u} * {αβ2ψ, i + j, -(t * u * 2)} * {αβ2ψ, i + j, t * u} = 1 := by
      have : -(t * u * 2) = 2 * (-t * u) := by ring
      rw [this, ← doub_of_αβ2ψ Fchar h]
      group
      rw [← inv_of_αβ2ψ Fchar (by ht)]
      simp
    grw [this]
    grw [h38a, h38b]
    have h1 : {ψ, j, -u / 2} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {ψ, j, -u / 2} := by
      rw [triv_comm_iff_commutes.1]
      exact h38b (-u / 2) (t * u) v
    have h2 : {ψ, j, u} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {ψ, j, u} := by
      rw [triv_comm_iff_commutes.1]
      exact h38b u (t * u) v
    have h3 : {β, k, -v} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {β, k, -v} := by
      rw [triv_comm_iff_commutes.1]
      exact h38a (-v) (t * u) v
    have h4 : {β, k, v} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {β, k, v} := by
      rw [triv_comm_iff_commutes.1]
      exact h38a v (t * u) v
    grw [h1, h2, h3, h2, h4, h1, h38d]
    have : {βψ, j + k, u * v} = {ψ, j, -u / 2} * {β, k, v} * {ψ, j, u} * {β, k, -v} * {ψ, j, -u / 2} := by
      rw [← expr_βψ_as_ψ_β_ψ_β_ψ Fchar hj hk u v, mul_comm]
    have h5 : 2 * t * u = t * u * 2 := by
      ring
    grw [h5, ← this]
    repeat assumption
  exact reorder_left_iff_eq_comm.mp this

-- 8.161
theorem sufficient_conditions_for_comm_of_αβ2ψ_and_β2ψ :
    ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 3)
    (hyp : ∀ (t u : F), ⁅{β2ψ, k, t}, {αβ2ψ, i + j, u}⁆ = 1),
    ∀ (t u : F), ⁅{β2ψ, i, t}, {αβ2ψ, j + k, u}⁆ = 1 := by
  intro i j k hi hj hk hyp t u
  have hyp' := fun t' u' ↦ triv_comm_iff_commutes.1 (hyp t' u')
  apply triv_comm_iff_commutes.2
  -- expand αβ2ψ element as a product of α and β2ψ elements
  rw [←mul_one u, expr_αβ2ψ_as_α_β2ψ_α_β2ψ Fchar hj hk]
  -- commute the β2ψ element fully to the left (working on RHS)
  grw [expr_β2ψ_β2ψ_as_β2ψ_β2ψ, expr_α_β2ψ_as_β2ψ_αβ2ψ_α (t := -u) Fchar hj hi,
  expr_β2ψ_β2ψ_as_β2ψ_β2ψ, expr_α_β2ψ_as_β2ψ_α_αβ2ψ Fchar hj hi]
  rw [eq_of_h_eq αβ2ψ (i + j) (add_comm j i), eq_of_h_eq αβ2ψ (i + j) (add_comm j i)]
  rw [←hyp', neg_mul, ←inv_of_αβ2ψ Fchar (add_le_add hi hj)]
  group

-- 8.162a
include Fchar in
theorem partial_comm_of_β2ψ_αβ2ψ_a :
  ∀ (t u : F), ⁅{β2ψ, 2, t}, {αβ2ψ, 1, u}⁆ = 1 := by
  have := sufficient_conditions_for_comm_of_αβ2ψ_and_β2ψ (F := F) (i := 2) (j := 0) (k := 1) (by ht)
  norm_num at this
  apply this
  have := hom_lift_of_comm_of_β2ψ_αβ2ψ (i := 1) (j := 1) (k := 0) (by ht)
  norm_num at this
  exact this

-- 8.162b
include Fchar in
theorem partial_comm_of_β2ψ_αβ2ψ_b :
  ∀ (t u : F), ⁅{β2ψ, 0, t}, {αβ2ψ, 2, u}⁆ = 1 := by
  have := @sufficient_conditions_for_comm_of_αβ2ψ_and_β2ψ F _ Fchar 0 1 1 (by ht) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  have := @hom_lift_of_comm_of_β2ψ_αβ2ψ F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

-- 8.163
theorem sufficient_conditions_for_comm_of_ψ_and_αβ2ψ_β :
    ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 4) (hk : k ≤ 1)
    (h41a : ∀ (t u : F), ⁅{β2ψ, 2 * i + k, t}, {αβ2ψ, j, u}⁆ = 1)
    (h41b : ∀ (t u : F), ⁅{βψ, i + k, t}, {αβ2ψ, j, u}⁆ = 1),
    ∀ (t u v : F), ⁅{ψ, i, t}, ⁅{αβ2ψ, j, u}, {β, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk h41a h41b t u v
  have h₁ := fun t' u' ↦ triv_comm_iff_commutes.1 (h41a t' u')
  have h₂ := fun t' u' ↦ triv_comm_iff_commutes.1 (h41b t' u')
  apply triv_comm_iff_commutes.2
  -- expand the commutator (work on LHS)
  rw [commutatorElement_def, inv_of_αβ2ψ Fchar hj, inv_of_β]
  -- move the ψ element fully to the right
  grw [expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar, expr_ψ_β_as_β_βψ_β2ψ_ψ hk hi, expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar, expr_ψ_β_as_β2ψ_βψ_β_ψ hk hi]
  -- use assumptions to cancel stuff
  rw [eq_of_h_eq β2ψ (2 * i + k) (by linarith), mul_assoc {βψ, k + i, -v * t}, h₁]
  nth_rewrite 2 [eq_of_h_eq β2ψ (2 * i + k) (by linarith)]
  grw [rfl]
  rw [eq_of_R_eq β2ψ 0 (by ring), id_of_β2ψ, mul_one]
  rw [eq_of_h_eq βψ (i + k) (by linarith), h₂]
  nth_rewrite 2 [eq_of_h_eq βψ (i + k) (by linarith)]
  grw [rfl]
  rw [eq_of_R_eq βψ 0 (by ring), id_of_βψ, mul_one]


-- 8.164
include Fchar
theorem partial_comm_of_ψ_αβ2ψ_β :
  ∀ (t u v : F), ⁅{ψ, 1, v}, ⁅{αβ2ψ, 1, t}, {β, 0, u}⁆⁆ = 1 := by
  intro t u v
  have := @sufficient_conditions_for_comm_of_ψ_and_αβ2ψ_β F _ Fchar 1 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  exact @partial_comm_of_β2ψ_αβ2ψ_a F _ Fchar
  have := @hom_lift_of_comm_βψ_αβ2ψ F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

-- 8.165
theorem partial_B_interchange_of_α2β2ψ :
  ∀ (t u v : F), ⁅{αβψ, 0, t}, {βψ, 1, u * v}⁆ = ⁅{αβ2ψ, 1, 2 * t * u}, {β, 0, v}⁆ := by
  have h := @hom_lift_of_inv_doub_of_β_αβ2ψ F _ Fchar 1 0 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  have := @more_sufficient_conditions_for_comm_of_αβψ_and_βψ F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  · intro t u v
    have h1 := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 1 0 0 (by norm_num) (by norm_num) (by norm_num) u (1/2) v
    have h2 := @hom_lift_of_interchange_of_α2β2ψ_b F _ Fchar 1 0 0 (by norm_num) (by norm_num) (by norm_num) (u/2) 1 v
    norm_num at h1; norm_num at h2; field_simp at h1; field_simp at h2
    rw [h2] at h1
    have := @comm_of_β_αβ_β2ψ F _ 0 1 0 (by norm_num) (by norm_num) (by norm_num) t u v
    rw [h1] at this
    exact this
  · intro t u v
    have := @partial_comm_of_ψ_αβ2ψ_β F _ Fchar u v t
    exact this
  · intro t u
    nth_rw 2 [← comm_swap]
    rw [← inv_inj, inv_inv]
    apply Eq.symm
    apply eq_inv_iff_mul_eq_one.mpr
    rcases h (-u) (-t) with ⟨h1, ⟨h2, _⟩⟩
    norm_num at h1; norm_num at h2
    rw [← h1]
    exact h2
  · intro t u
    rcases h (-u) t with ⟨h1, ⟨h2, h3⟩⟩
    norm_num at h1
    apply mul_eq_one_iff_eq_inv.mp at h2
    simp only [neg_neg, commutatorElement_inv] at h2
    grw [← h2, h3]
    rcases h (-2*u) t with ⟨_, ⟨h4, _⟩⟩
    apply mul_eq_one_iff_eq_inv.mp at h4
    simp only [neg_neg, commutatorElement_inv] at h4
    norm_num at h4
    rw [h4]
    have h5 := @hom_lift_of_interchange_of_α2β2ψ_b F _ Fchar 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h5
    have h5a := h5 t 1 u; norm_num at h5a
    have h5b := h5 (t) (1/2) (2*u); field_simp at h5b;
    rw [←h5a, ←h5b]

-- 8.166
theorem sufficient_conditions_for_comm_of_αβ_and_β2ψ :
    ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 2)
    (h42a : ∀ (t u : F), ⁅{αβ2ψ, i + 2 * j, t}, {βψ, k, u}⁆ = 1)
    (h42b : ∀ (t u v : F), ⁅{ψ, j, t}, ⁅{αβψ, i + j, u}, {βψ, k, v}⁆⁆ = 1),
    ∀ (t u v : F), ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ = ⁅{αβψ, i + j, t * u}, {βψ, k, v}⁆ := by
  intro i j k hi hj hk h42a h42b t u v
  have h₁ := fun t u ↦ triv_comm_iff_commutes.1 (h42a t u)
  have h₂ := fun t u v ↦ triv_comm_iff_commutes.1 (h42b t u v)
  apply eq_comm_of_reorder_left
  -- expand β2ψ element as product of βψ and ψ elements
  rw [expr_β2ψ_as_ψ_βψ_ψ_βψ hj hk]
  -- move αβ element fully to the right
  grw [expr_αβ_ψ_as_ψ_αβψ_αβ2ψ_αβ Fchar hi hj, expr_αβ_βψ_as_βψ_αβ hi hk,
  expr_αβ_ψ_as_αβ2ψ_αβψ_ψ_αβ Fchar hi hj, expr_αβ_βψ_as_βψ_αβ hi hk]
  -- by h₁, commute αβ2ψ elements together and cancel them
  grw [h₁ (-t * u^2)]
  rw [neg_mul, ←inv_of_αβ2ψ Fchar (by linarith), neg_sq]
  grw [rfl, comm_left {αβψ, i + j, t * u}, ←inv_of_αβψ (by linarith), h₂]

omit Fchar
-- 8.167
include Fchar in
theorem sufficient_conditions_for_comm_of_αβ2ψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 4) (hj : j ≤ 1) (hk : k ≤ 1)
  (h44a : ∀ (t u v : F), ⁅⁅{αβ2ψ, i, t}, {β, j, u}⁆, {ψ, k, v}⁆ = 1)
  (h44b : ∀ (t u : F), ⁅{β, j, -u}, {αβ2ψ, i, t}⁆ = ⁅{αβ2ψ, i, t}, {β, j, u}⁆)
  (h44c : ∀ (t u : F), ⁅{αβ2ψ, i, t}, {β, j, u}⁆ * ⁅{αβ2ψ, i, -t}, {β, j, u}⁆ = 1),
  ∀ (t u : F), ⁅{αβ2ψ, i, t}, {βψ, j + k, u}⁆ = 1 := by
  intro i j k hi hj hk h44a h44b h44c t u
  have := inv_of_αβ2ψ Fchar (by exact hi) (-t); rw [neg_neg] at this
  have eq45 := calc {αβ2ψ, i, t} * {β, j, u}
    _ = {β, j, u} * ⁅{β, j, -u}, {αβ2ψ, i, t}⁆ * {αβ2ψ, i, t} := by
      rw [comm_mid_rev, inv_of_β]
    _ = {β, j, u} * ⁅{αβ2ψ, i, t}, {β, j, u}⁆ * {αβ2ψ, i, t} := by
      rw [h44b t u]
  have eq46 := calc {αβ2ψ, i, t} * {β, j, -u}
    _ = ⁅{αβ2ψ, i, t}, {β, j, -u}⁆ * {β, j, -u} * {αβ2ψ, i, t} := by
      apply comm_left
  have h44d : ∀ t u, ⁅{αβ2ψ, i, -t}, {β, j, u}⁆ * ⁅{αβ2ψ, i, t}, {β, j, u}⁆ = 1 := by
    intro t u
    have := h44c (-t) (u)
    norm_num at this
    exact this
  have h := expr_βψ_as_ψ_β_ψ_β_ψ Fchar (i := k) (j := j) (by ht) hj 1 u
  norm_num at h; rw [eq_of_h_eq βψ (j + k)] at h
  have := calc {αβ2ψ, i, t} * {βψ, j + k, u}
    _ = {αβ2ψ, i, t} * {ψ, k, -1/2} * {β, j, u} * {ψ, k, 1} * {β, j, -u} * {ψ, k, -1/2} := by
      grw [h]
    _ = {ψ, k, -1/2} * {β, j, u} * ⁅{αβ2ψ, i, t}, {β, j, u}⁆ * {ψ, k, 1} * ⁅{αβ2ψ, i, -t}, {β, j, u}⁆ * {β, j, -u} * {ψ, k, -1/2} * {αβ2ψ, i, t} := by
      have h1 : ∀ u, {ψ, k, u} * {αβ2ψ, i, t} = {αβ2ψ, i, t} * {ψ, k, u} := by
        intro u
        rw [triv_comm_iff_commutes.mp]
        apply comm_of_ψ_αβ2ψ Fchar
      have := calc {αβ2ψ, i, t} * ⁅{αβ2ψ, i, -t}, {β, j, u}⁆
        _ = {αβ2ψ, i, t} * ⁅{β, j, -u}, {αβ2ψ, i, -t}⁆ := by rw [(h44b (-t) (u))]
        _ = {αβ2ψ, i, t} * {β, j, -u} * {αβ2ψ, i, -t} * {β, j, u} * {αβ2ψ, i, t} := by
          grw [commutatorElement_def, inv_of_αβ2ψ Fchar (by ht)]
        _ = ⁅{αβ2ψ, i, t}, {β, j, -u}⁆ * {αβ2ψ, i, t} := by
          grw [commutatorElement_def, inv_of_αβ2ψ Fchar (by ht)]
      grw [← h1, eq45, ← h1, eq46, ← h1]
      nth_rw 2 [← comm_swap]
      apply mul_eq_one_iff_eq_inv.mp
      have := h44b (-t) (-u)
      norm_num at this
      grw [this]
      have := h44d (-t) (-u)
      norm_num at this
      exact this
    _ = {ψ, k, -1/2} * {β, j, u} * {ψ, k, 1} * {β, j, -u} * {ψ, k, -1/2} * {αβ2ψ, i, t} := by
      have := fun t u v ↦ (triv_comm_iff_commutes.mp (h44a t u v))
      grw [this, this, h44c]
    _ = {βψ, j + k, u} * {αβ2ψ, i, t} := by
      grw [← h]
  exact triv_comm_iff_commutes.mpr this
  exact Nat.add_comm k j

include Fchar
private lemma partial_comm_of_βψ_αβ2ψ_help : ∀ t u : F,
    ⁅{αβ2ψ, 2, t}, {β, 0, u}⁆ = ⁅{αβ, 1, t}, {β2ψ, 1, u}⁆ := by
  intro t u
  have : t = 2 * t * (1 / 2) := by field_simp
  rw [this, ←@hom_lift_of_interchange_of_α2β2ψ_b F _ Fchar 0 0 1 (by trivial) (by trivial) (by trivial),
    ←mul_one t, ←@hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]
  field_simp

private lemma partial_comm_of_βψ_αβ2ψ_help' : ∀ t u : F,
    ⁅{β, 0, u}, {αβ2ψ, 2, t}⁆ = ⁅{β2ψ, 1, u}, {αβ, 1, t}⁆ := by
  intro t u
  apply inv_inj.1
  rw [comm_swap, comm_swap]
  apply partial_comm_of_βψ_αβ2ψ_help Fchar

-- 8.168
theorem partial_comm_of_βψ_αβ2ψ :
  ∀ (t u : F), ⁅{αβ2ψ, 2, t}, {βψ, 0, u}⁆ = 1 := by
  apply @sufficient_conditions_for_comm_of_αβ2ψ_and_βψ F _ Fchar 2 0 0 (by trivial) (by trivial) (by trivial)
  · intro t u v
    rw [partial_comm_of_βψ_αβ2ψ_help Fchar, triv_comm_symm, @hom_lift_of_comm_ψ_αβ_β2ψ F _ 0 1 0 (by trivial) (by trivial) (by trivial)]
  · intro t u
    rw [partial_comm_of_βψ_αβ2ψ_help Fchar, partial_comm_of_βψ_αβ2ψ_help' Fchar]
    apply (mul_left_inj (⁅{β2ψ, 1, -u}, {αβ, 1, t}⁆⁻¹)).1
    rw [mul_inv_cancel, comm_swap, (@hom_lift_of_inv_doub_of_αβ_β2ψ F _ 0 1 0 (by trivial) (by trivial) (by trivial) t u).1]
    nth_rewrite 2 [←neg_neg t]
    rw [(@hom_lift_of_inv_doub_of_αβ_β2ψ F _ 0 1 0 (by trivial) (by trivial) (by trivial) (-t) (-u)).2.1]
  · intro t u
    rw [partial_comm_of_βψ_αβ2ψ_help Fchar, partial_comm_of_βψ_αβ2ψ_help Fchar,
    (@hom_lift_of_inv_doub_of_αβ_β2ψ F _ 0 1 0 (by trivial) (by trivial) (by trivial) t u).2.1]

-- 8.169a
theorem partial_C_interchange_of_α2β2ψ_a :
  ∀ (t u v : F), ⁅{αβ, 0, t}, {β2ψ, 1, 2 * u * v}⁆ = ⁅{αβψ, 1, t * u}, {βψ, 0, v}⁆ := by
  apply @sufficient_conditions_for_comm_of_αβ_and_β2ψ F _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)
  · exact @partial_comm_of_βψ_αβ2ψ F _ Fchar
  intro t u v
  have := @hom_lift_of_interchange_of_α2β2ψ_b F _ Fchar 1 0 0 (by trivial) (by trivial) (by trivial) u 1 v
  norm_num at this;
  grw [this, partial_comm_of_ψ_αβ2ψ_β Fchar]

-- 8.169b
theorem partial_C_interchange_of_α2β2ψ_b :
  ∀ (t u v : F), ⁅{αβ, 2, t}, {β2ψ, 0, 2 * u * v}⁆ = ⁅{αβψ, 2, t * u}, {βψ, 0, v}⁆ := by
  apply @sufficient_conditions_for_comm_of_αβ_and_β2ψ F _ Fchar 2 0 0 (by trivial) (by trivial) (by trivial)
  · exact @partial_comm_of_βψ_αβ2ψ F _ Fchar
  intro t u v
  rw [←one_mul u, partial_A_interchange_of_α2β2ψ_b Fchar,
  @hom_lift_of_comm_ψ_αβ_β2ψ F _ 0 1 0 (by trivial) (by trivial) (by trivial)]

-- 8.170
theorem sufficient_conditions_for_comm_of_αβ2ψ_and_β :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 1)
  (h47a : ∀ (t u : F), ⁅{αβψ, i, t}, {β2ψ, 2 * j + k, u}⁆ = 1)
  (h47b : ∀ (t u v : F), ⁅⁅{αβψ, i, t}, {βψ, j + k, u}⁆, {ψ, j, v}⁆ = 1)
  (h47c : ∀ (t u : F), ⁅{βψ, j + k, -u}, {αβψ, i, t}⁆ = ⁅{αβψ, i, t}, {βψ, j + k, u}⁆),
  ∀ (t u v : F), ⁅{αβ2ψ, i + j, t * u}, {β, k, 2 * v}⁆ = ⁅{αβψ, i, t}, {βψ, j + k, u * v}⁆ := by
  intro i j k hi hj hk hyp₁ hyp₂ hyp₃ t u v
  have h₁ := fun t u ↦ triv_comm_iff_commutes.1 (hyp₁ t u)
  have h₂ := fun t u v ↦ triv_comm_iff_commutes.1 (hyp₂ t u v)
  apply eq_comm_of_reorder_left
  -- expand αβ2ψ as product of αβψ and ψ elements
  rw [eq_of_R_eq αβ2ψ (-2 * (-u/2) * t) (by ring_nf; field_simp), expr_αβ2ψ_as_ψ_αβψ_ψ_αβψ Fchar hi hj]
  -- commute β fully to the left
  grw [←expr_β_αβψ_as_αβψ_β, expr_ψ_β_as_β_β2ψ_βψ_ψ hk hj, ←expr_β_αβψ_as_αβψ_β, expr_ψ_β_as_β_ψ_βψ_β2ψ hk hj]
  -- by hyp₁, commute the β2ψ elements across αβψ and cancel them
  rw [eq_of_h_eq β2ψ (2 * j + k) (by linarith), eq_of_R_eq βψ (-v * u) (by ring_nf; field_simp),
  eq_of_R_eq β2ψ (v * u^2 / 2) (by ring_nf; rw [pow_two (2⁻¹), mul_assoc]; field_simp)]
  grw [←h₁ _ (v * u^2 / 2)]
  nth_rewrite 2 [eq_of_R_eq β2ψ (-(v * u^2 / 2)) (by ring_nf; field_simp; group),
  eq_of_h_eq β2ψ (2 * j + k) (by linarith)]
  grw [rfl]
  -- commute the two βψ elements together, creating a generic commutator (using hyp₃)
  grw [comm_left ({βψ, k + j, -v * u}) ({αβψ, i, t})]
  rw [eq_of_h_eq βψ (j + k) (by linarith), eq_of_R_eq βψ (-(v * u)) (by ring_nf)]
  grw [hyp₃]
  -- commute ψ and ⁅αβψ, βψ⁆ by h₂
  grw [←h₂ t]
  -- commute β and ⁅αβψ, βψ⁆ by relation 8.157
  have := triv_comm_iff_commutes.1 (comm_of_β_αβψ_βψ (i := k) (j := i) (k := j + k)
  (t := 2 * v) (u := t) (v := u * v) (by trivial) (by trivial) (by linarith))
  grw [←this, mul_comm u v]
  rw [eq_of_R_eq βψ 0 (by ring_nf; field_simp), id_of_βψ, mul_one]

-- 8.171
include Fchar
theorem sufficient_conditions_for_comm_of_αβψ_and_β2ψ :
    ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
    (hyp : ∀ (t u : F), ⁅{αβ2ψ, i + k, u}, {βψ, j, t}⁆ = 1),
    ∀ (t u : F), ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1 := by
  intro i j k hi hj hk hyp t u
  have hyp' := fun t u ↦ triv_comm_iff_commutes.1 (hyp t u)
  apply triv_comm_iff_commutes.2
  -- expand αβψ element as product of α and βψ elements (working on LHS)
  rw [←one_mul t, expr_αβψ_as_βψ_α_βψ_α_βψ hi hj]
  -- move β2ψ element from the right fully to the left
  grw [expr_βψ_β2ψ_as_β2ψ_βψ, expr_α_β2ψ_as_β2ψ_αβ2ψ_α Fchar hi hk, expr_βψ_β2ψ_as_β2ψ_βψ,
  expr_α_β2ψ_as_β2ψ_α_αβ2ψ Fchar hi hk, expr_βψ_β2ψ_as_β2ψ_βψ]
  -- commute αβ2ψ element across the βψ element and cancel
  rw [hyp', neg_mul, one_mul, ←inv_of_αβ2ψ Fchar (by linarith)]
  group

-- 8.172
theorem partial_comm_of_αβψ_β2ψ :
    ∀ (t u : F), ⁅{αβψ, 0, t}, {β2ψ, 1, u}⁆ = 1 := by
  apply sufficient_conditions_for_comm_of_αβψ_and_β2ψ (i := 0) (j := 0) (k := 1) (by trivial) (by trivial) (by trivial) (by trivial)
  intro t u
  rw [eq_of_h_eq αβ2ψ 1 rfl, ←one_mul u, expr_αβ2ψ_as_comm_of_α_β2ψ (i := 1) (j := 0) Fchar (by trivial) (by trivial)]
  apply triv_comm_symm.1
  rw [lift_hom_comm_of_βψ_α_β2ψ (i := 1) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial)]

private lemma partial_D_interchange_of_α2β2ψ_help : ∀ t u : F,
    ⁅{αβψ, 0, t}, {βψ, 1, u}⁆ = ⁅{αβ, 1, t}, {β2ψ, 0, 2 * u}⁆ := by
  intro t u
  rw [←mul_one u, partial_B_interchange_of_α2β2ψ Fchar,
  ←hom_lift_of_interchange_of_α2β2ψ_b (i := 1) (j := 0) (k := 0) Fchar (by trivial) (by trivial) (by trivial),
  mul_one, ←mul_one t, ←hom_lift_of_interchange_of_α2β2ψ_a Fchar (by trivial) (by trivial) (by trivial)]
  simp only [add_zero, mul_zero, mul_one]

-- 8.173
theorem partial_D_interchange_of_α2β2ψ :
  ∀ (t u v : F), ⁅{αβψ, 0, t}, {βψ, 1, u * v}⁆ = ⁅{αβ2ψ, 0, t * u}, {β, 1, 2 * v}⁆ := by
  intro _ _ _
  apply symm
  apply @sufficient_conditions_for_comm_of_αβ2ψ_and_β F _ Fchar 0 0 1 (by trivial) (by trivial) (by trivial)
  · exact partial_comm_of_αβψ_β2ψ Fchar
  · intro t u v
    rw [partial_D_interchange_of_α2β2ψ_help Fchar, triv_comm_symm,
    hom_lift_of_comm_ψ_αβ_β2ψ (i := 1) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial)]
  · intro t u
    apply (mul_right_inj (⁅{βψ, 0 + 1, -u}, {αβψ, 0, t}⁆⁻¹)).1
    rw [inv_mul_cancel, comm_swap, partial_D_interchange_of_α2β2ψ_help Fchar,
    partial_D_interchange_of_α2β2ψ_help Fchar, eq_of_R_eq β2ψ (-(2 * u)) (by ring),
    (hom_lift_of_inv_doub_of_αβ_β2ψ (i := 1) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial) t (-(2 * u))).1,
    neg_neg]
    nth_rewrite 2 [←neg_neg t]
    rw [(hom_lift_of_inv_doub_of_αβ_β2ψ (i := 1) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial) (-t) (2 * u)).2.1]


/- ### Establishing α + 2β + 2ψ -/

include Fchar
private lemma interchange_of_α2β2ψ_refl_u_αβ_β2ψ :
  forall_ijk_tu 1 1 1, ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, 2 * u}⁆ = ⁅{αβψ, i + j + k, t}, {βψ, j + k, u}⁆ := by
  intro i j k hi hj hk t u
  rw [←one_mul u, ←mul_assoc, hom_lift_of_interchange_of_α2β2ψ_a Fchar hi hj hk t, mul_one, one_mul]

private lemma interchange_of_α2β2ψ_refl_v_αβ_β2ψ :
  forall_ijk_tu 1 1 1, ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, 2 * u}⁆ = ⁅{αβψ, i + j + k, t * u}, {βψ, j + k, 1}⁆ := by
  intro i j k hi hj hk t u
  rw [←mul_one (2 * u), hom_lift_of_interchange_of_α2β2ψ_a Fchar hi hj hk t]

private lemma interchange_of_α2β2ψ_refl_u_αβψ_βψ :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t}, {βψ, j + k, u/2}⁆ = ⁅{αβ2ψ, i + j + 2 * k, t}, {β, j, u}⁆ := by
  intro i j k hi hj hk t u
  have : u/2 = (1/2) * u := by ring
  rw [this, hom_lift_of_interchange_of_α2β2ψ_b Fchar hi hj hk]
  field_simp

private lemma interchange_of_α2β2ψ_trans_αβψ_βψ :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t * u}, {βψ, j + k, 1}⁆ = ⁅{αβψ, i + j + k, t}, {βψ, j + k, u}⁆ := by
  intro i j k hi hj hk t u
  rw [←interchange_of_α2β2ψ_refl_v_αβ_β2ψ Fchar hi hj hk, ←interchange_of_α2β2ψ_refl_u_αβ_β2ψ Fchar hi hj hk]

private lemma interchange_of_α2β2ψ_trans_αβ_β2ψ :
  forall_ijk_tu 1 1 1, ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, 1}⁆ = ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ := by
  intro i j k hi hj hk t u
  have aux₁ := hom_lift_of_interchange_of_α2β2ψ_a Fchar hi hj hk t (u/2) 1
  have aux₂ := hom_lift_of_interchange_of_α2β2ψ_a Fchar hi hj hk (t * u) (1 / 2) 1
  field_simp at aux₁
  field_simp at aux₂
  rwa [←aux₁] at aux₂

private lemma interchange_A_of_α2β2ψ_refl_u :
  ∀ t u : F, ⁅{αβ, 1, t}, {β2ψ, 1, 2 * u}⁆ = ⁅{αβψ, 2, t}, {βψ, 0, u}⁆ := by
  intro t u
  rw [←one_mul u, ←mul_assoc, ←partial_A_interchange_of_α2β2ψ_b Fchar]
  simp only [mul_one, one_mul]

private lemma interchange_A_of_α2β2ψ_refl_u' :
  ∀ t u : F, ⁅{αβ, 0, t}, {β2ψ, 2, 2 * u}⁆ = ⁅{αβψ, 0, t}, {βψ, 2, u}⁆ := by
  intro t u
  rw [←one_mul u, ←mul_assoc, ←partial_A_interchange_of_α2β2ψ_a Fchar]
  simp only [mul_one, one_mul]

private lemma interchange_B_of_α2β2ψ_refl_u_αβψ_βψ :
  ∀ t u : F, ⁅{αβψ, 0, t}, {βψ, 1, u/2}⁆ = ⁅{αβ2ψ, 1, t}, {β, 0, u}⁆ := by
  intro t u
  have : u/2 = (1/2) * u := by ring
  rw [this, partial_B_interchange_of_α2β2ψ Fchar]
  field_simp

private lemma interchange_C_refl_u :
  ∀ t u : F, ⁅{αβ, 0, t}, {β2ψ, 1, 2 * u}⁆ = ⁅{αβψ, 1, t}, {βψ, 0, u}⁆ := by
  intro t u
  rw [←one_mul u, ←mul_assoc, partial_C_interchange_of_α2β2ψ_a Fchar]
  simp only [mul_one, one_mul]

private lemma interchange_C_refl_u' :
  ∀ t u : F, ⁅{αβ, 2, t}, {β2ψ, 0, 2 * u}⁆ = ⁅{αβψ, 2, t}, {βψ, 0, u}⁆ := by
  intro t u
  rw [←one_mul u, ←mul_assoc, partial_C_interchange_of_α2β2ψ_b Fchar]
  simp only [mul_one, one_mul]

private lemma interchange_C_refl_v :
  ∀ t u : F, ⁅{αβ, 0, t}, {β2ψ, 1, 2 * u}⁆ = ⁅{αβψ, 1, t * u}, {βψ, 0, 1}⁆ := by
  intro t u
  rw [←mul_one u, ←mul_assoc, partial_C_interchange_of_α2β2ψ_a Fchar]
  simp only [mul_one]

private lemma interchange_C_of_α2β2ψ_trans_αβψ_βψ :
  ∀ t u : F, ⁅{αβψ, 1, t * u}, {βψ, 0, 1}⁆ = ⁅{αβψ, 1, t}, {βψ, 0, u}⁆ := by
  intro t u
  rw [←interchange_C_refl_v Fchar, ←interchange_C_refl_u Fchar]

private lemma interchange_C_of_α2β2ψ_trans_αβ_β2ψ :
  ∀ t u : F, ⁅{αβ, 0, t * u}, {β2ψ, 1, 1}⁆ = ⁅{αβ, 0, t}, {β2ψ, 1, u}⁆ := by
  intro t u
  have aux₁ := partial_C_interchange_of_α2β2ψ_a Fchar t u (1 / 2)
  have aux₂ := partial_C_interchange_of_α2β2ψ_a Fchar (t * u) 1 (1 / 2)
  field_simp at aux₁
  field_simp at aux₂
  rwa [←aux₁] at aux₂

private lemma interchange_D_refl_u :
  ∀ t u : F, ⁅{αβψ, 0, t}, {βψ, 1, u}⁆ = ⁅{αβ2ψ, 0, t}, {β, 1, 2 * u}⁆ := by
  intro t u
  rw [←one_mul u, partial_D_interchange_of_α2β2ψ Fchar]
  simp only [mul_one, one_mul]

include Fchar
-- height 0
private lemma expr_α2β2ψ_as_comm_of_αβ_β2ψ_00 :
  ∀ t u : F, {α2β2ψ, 0, -t * u} = ⁅{αβ, 0, t}, {β2ψ, 0, u}⁆:= by
  intro t u
  have := @def_of_α2β2ψ _ _ 0 (by trivial) (t * u)
  unfold split_5_into_2_3 at this
  rw [neg_mul, ←this, @interchange_of_α2β2ψ_trans_αβ_β2ψ _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_α2β2ψ_as_comm_of_αβψ_βψ_00 :
  ∀ t u : F, {α2β2ψ, 0, -2 * t * u} = ⁅{αβψ, 0, t}, {βψ, 0, u}⁆ := by
  intro t u
  have : -2 * t * u = -t * (2 * u) := by ring
  rw [this, expr_α2β2ψ_as_comm_of_αβ_β2ψ_00 Fchar, @interchange_of_α2β2ψ_refl_v_αβ_β2ψ _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial),
  interchange_of_α2β2ψ_trans_αβψ_βψ Fchar (by trivial) (by trivial) (by trivial)]

private lemma expr_α2β2ψ_as_comm_of_αβ2ψ_β_00 :
  ∀ t u : F, {α2β2ψ, 0, -t * u} = ⁅{αβ2ψ, 0, t}, {β, 0, u}⁆ := by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_00 Fchar, @interchange_of_α2β2ψ_refl_u_αβψ_βψ _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial)]

-- height 1
private lemma expr_α2β2ψ_as_comm_of_αβ_β2ψ_01 :
  ∀ t u : F, {α2β2ψ, 1, -t * u} = ⁅{αβ, 0, t}, {β2ψ, 1, u}⁆:= by
  intro t u
  have := @def_of_α2β2ψ _ _ 1 (by trivial) (t * u)
  unfold split_5_into_2_3 at this
  rw [neg_mul, ←this, interchange_C_of_α2β2ψ_trans_αβ_β2ψ Fchar]

private lemma expr_α2β2ψ_as_comm_of_αβψ_βψ_10 :
  ∀ t u : F, {α2β2ψ, 1, -2 * t * u} = ⁅{αβψ, 1, t}, {βψ, 0, u}⁆ := by
  intro t u
  have : -2 * t * u = -t * (2 * u) := by ring
  rw [this, expr_α2β2ψ_as_comm_of_αβ_β2ψ_01 Fchar, interchange_C_refl_v Fchar,
  interchange_C_of_α2β2ψ_trans_αβψ_βψ Fchar]

private lemma expr_α2β2ψ_as_comm_of_αβ_β2ψ_10 :
  ∀ t u : F, {α2β2ψ, 1, -t * u} = ⁅{αβ, 1, t}, {β2ψ, 0, u}⁆:= by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_10 Fchar, ←@interchange_of_α2β2ψ_refl_u_αβ_β2ψ _ _ Fchar 1 0 0 (by trivial) (by trivial) (by trivial)]
  field_simp

private lemma expr_α2β2ψ_as_comm_of_αβ2ψ_β_10
    : ∀ (t u : F), {α2β2ψ, 1, -t * u} = ⁅{αβ2ψ, 1, t}, {β, 0, u}⁆ := by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_10 Fchar, @interchange_of_α2β2ψ_refl_u_αβψ_βψ _ _ Fchar 1 0 0 (by trivial) (by trivial) (by trivial)]

-- `B` edge
private lemma expr_α2β2ψ_as_comm_of_αβψ_βψ_01
    : ∀ (t u : F), {α2β2ψ, 1, -2 * t * u} = ⁅{αβψ, 0, t}, {βψ, 1, u}⁆ := by
  intro t u
  have : -2 * t * u = -t * (2 * u) := by ring
  rw [this, expr_α2β2ψ_as_comm_of_αβ2ψ_β_10 Fchar, ←interchange_B_of_α2β2ψ_refl_u_αβψ_βψ Fchar]
  field_simp

-- `D` edge
private lemma expr_α2β2ψ_as_comm_of_αβ2ψ_β_01
    : ∀ (t u : F), {α2β2ψ, 1, -t * u} = ⁅{αβ2ψ, 0, t}, {β, 1, u}⁆ := by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_01 Fchar, interchange_D_refl_u Fchar]
  field_simp

-- height 2
private lemma expr_α2β2ψ_as_comm_of_αβ_β2ψ_11 :
  ∀ t u : F, {α2β2ψ, 2, -t * u} = ⁅{αβ, 1, t}, {β2ψ, 1, u}⁆:= by
  intro t u
  have := @def_of_α2β2ψ _ _ 2 (by trivial) (t * u)
  unfold split_5_into_2_3 at this
  rw [neg_mul, ←this, @interchange_of_α2β2ψ_trans_αβ_β2ψ _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]

-- `A` edge
private lemma expr_α2β2ψ_as_comm_of_αβψ_βψ_20 :
  ∀ t u : F, {α2β2ψ, 2, -2 * t * u} = ⁅{αβψ, 2, t}, {βψ, 0, u}⁆ := by
  intro t u
  have : -2 * t * u = -t * (2 * u) := by ring
  rw [this, expr_α2β2ψ_as_comm_of_αβ_β2ψ_11 Fchar, interchange_A_of_α2β2ψ_refl_u Fchar]

-- `C` edge
private lemma expr_α2β2ψ_as_comm_of_αβ_β2ψ_20 :
  ∀ t u : F, {α2β2ψ, 2, -t * u} = ⁅{αβ, 2, t}, {β2ψ, 0, u}⁆:= by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_20 Fchar, ←interchange_C_refl_u' Fchar]
  field_simp

private lemma expr_α2β2ψ_as_comm_of_αβψ_βψ_11 :
  ∀ t u : F, {α2β2ψ, 2, -2 * t * u} = ⁅{αβψ, 1, t}, {βψ, 1, u}⁆ := by
  intro t u
  have : -2 * t * u = -t * (2 * u) := by ring
  rw [this, expr_α2β2ψ_as_comm_of_αβ_β2ψ_11 Fchar, @interchange_of_α2β2ψ_refl_v_αβ_β2ψ _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial),
  interchange_of_α2β2ψ_trans_αβψ_βψ Fchar (by trivial) (by trivial) (by trivial)]

private lemma expr_α2β2ψ_as_comm_of_αβ_β2ψ_02 :
  ∀ t u : F, {α2β2ψ, 2, -t * u} = ⁅{αβ, 0, t}, {β2ψ, 2, u}⁆:= by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_11 Fchar, ←@interchange_of_α2β2ψ_refl_u_αβ_β2ψ _ _ Fchar 0 0 1 (by trivial) (by trivial) (by trivial)]
  field_simp

-- `A` edge
private lemma expr_α2β2ψ_as_comm_of_αβψ_βψ_02 :
  ∀ t u : F, {α2β2ψ, 2, -2 * t * u} = ⁅{αβψ, 0, t}, {βψ, 2, u}⁆ := by
  intro t u
  have : -2 * t * u = -t * (2 * u) := by ring
  rw [this, expr_α2β2ψ_as_comm_of_αβ_β2ψ_02 Fchar, interchange_A_of_α2β2ψ_refl_u' Fchar]

private lemma expr_α2β2ψ_as_comm_of_αβ2ψ_β_20 :
  ∀ t u : F, {α2β2ψ, 2, -t * u} = ⁅{αβ2ψ, 2, t}, {β, 0, u}⁆ := by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_11 Fchar, ←@interchange_of_α2β2ψ_refl_u_αβψ_βψ _ _ Fchar 0 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expr_α2β2ψ_as_comm_of_αβ2ψ_β_11 :
  ∀ t u : F, {α2β2ψ, 2, -t * u} = ⁅{αβ2ψ, 1, t}, {β, 1, u}⁆ := by
  intro t u
  have : -t * u = -2 * t * (u/2) := by ring_nf; field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ_11 Fchar, ←@interchange_of_α2β2ψ_refl_u_αβψ_βψ _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]

-- height 3
private lemma expr_α2β2ψ_as_comm_of_αβ_β2ψ_12 :
  ∀ t u : F, {α2β2ψ, 3, -t * u} = ⁅{αβ, 1, t}, {β2ψ, 2, u}⁆:= by
  intro t u
  have := @def_of_α2β2ψ _ _ 3 (by trivial) (t * u)
  unfold split_5_into_2_3 at this
  simp only at this
  rw [neg_mul, ←this, @interchange_of_α2β2ψ_trans_αβ_β2ψ _ _ Fchar 1 0 1 (by trivial) (by trivial) (by trivial)]

-- `A` edge
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβψ βψ const neg 2 heights 3 1 2 to 2 2 0

-- `C` edge
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ β2ψ const neg 1 heights 3 0 3 to 2 2 0

private lemma expr_α2β2ψ_as_comm_of_αβψ_βψ_21 :
  ∀ t u : F, {α2β2ψ, 3, -2 * t * u} = ⁅{αβψ, 2, t}, {βψ, 1, u}⁆ := by
  intro t u
  have : -2 * t * u = -t * (2 * u) := by ring
  rw [this, expr_α2β2ψ_as_comm_of_αβ_β2ψ_12 Fchar, @interchange_of_α2β2ψ_refl_v_αβ_β2ψ _ _ Fchar 1 0 1 (by trivial) (by trivial) (by trivial),
  interchange_of_α2β2ψ_trans_αβψ_βψ Fchar (by trivial) (by trivial) (by trivial)]

declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ β2ψ const neg 1 heights 3 2 1 to 2 0 2
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβψ βψ const neg 2 heights 3 3 0 to 2 0 2
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ2ψ β const neg 1 heights 3 3 0 to 2 1 1
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ2ψ β const neg 1 heights 3 2 1 to 2 2 0

-- height 4
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ β2ψ const neg 1 heights 4 2 2 to 1 0 1
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ β2ψ const neg 1 heights 4 1 3 to 1 1 0
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβψ βψ const neg 2 heights 4 3 1 to 1 0 1
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβψ βψ const neg 2 heights 4 2 2 to 1 1 0
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ2ψ β const neg 1 heights 4 4 0 to 1 0 1
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ2ψ β const neg 1 heights 4 3 1 to 1 1 0

-- height 5
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ β2ψ const neg 1 heights 5 2 3 to 0 0 0
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβψ βψ const neg 2 heights 5 3 2 to 0 0 0
declare_B3Large_reflected_thm F b3large_valid α2β2ψ αβ2ψ β const neg 1 heights 5 4 1 to 0 0 0

-- 8.174a
theorem expr_α2β2ψ_as_comm_of_αβ_β2ψ : forall_ij_tu αβ β2ψ,
    {α2β2ψ, i + j, -t * u} = ⁅{αβ, i, t}, {β2ψ, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_00 Fchar]
  | 1, 0 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_10 Fchar]
  | 2, 0 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_20 Fchar]
  | 0, 1 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_01 Fchar]
  | 1, 1 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_11 Fchar]
  | 2, 1 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_21 Fchar]
  | 0, 2 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_02 Fchar]
  | 1, 2 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_12 Fchar]
  | 2, 2 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_22 Fchar]
  | 0, 3 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_03 Fchar]
  | 1, 3 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_13 Fchar]
  | 2, 3 => rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ_23 Fchar]

-- 8.174b
theorem expr_α2β2ψ_as_comm_of_αβψ_βψ : forall_ij_tu αβψ βψ,
    {α2β2ψ, i + j, -2 * t * u} = ⁅{αβψ, i, t}, {βψ, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_00 Fchar]
  | 0, 1 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_01 Fchar]
  | 0, 2 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_02 Fchar]
  | 1, 0 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_10 Fchar]
  | 1, 1 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_11 Fchar]
  | 1, 2 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_12 Fchar]
  | 2, 0 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_20 Fchar]
  | 2, 1 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_21 Fchar]
  | 2, 2 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_22 Fchar]
  | 3, 0 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_30 Fchar]
  | 3, 1 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_31 Fchar]
  | 3, 2 => rw [expr_α2β2ψ_as_comm_of_αβψ_βψ_32 Fchar]

-- 8.174c
theorem expr_α2β2ψ_as_comm_of_αβ2ψ_β : forall_ij_tu αβ2ψ β,
    {α2β2ψ, i + j, -t * u} = ⁅{αβ2ψ, i, t}, {β, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_00 Fchar]
  | 0, 1 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_01 Fchar]
  | 1, 0 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_10 Fchar]
  | 1, 1 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_11 Fchar]
  | 2, 0 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_20 Fchar]
  | 2, 1 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_21 Fchar]
  | 3, 0 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_30 Fchar]
  | 3, 1 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_31 Fchar]
  | 4, 0 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_40 Fchar]
  | 4, 1 => rw [expr_α2β2ψ_as_comm_of_αβ2ψ_β_41 Fchar]

-- 8.175
theorem comm_of_β_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk β α2β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 2 3 j hj with ⟨ j₁, j₂, rfl, hj₁, hj₂ ⟩
  rw [←one_mul u, ←neg_neg 1, expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar hj₁ hj₂,
        expr_β_comm_αβ_β2ψ_as_comm_αβ_β2ψ_β hi hj₁ hj₂]
declare_B3Large_triv_expr_thm F β α2β2ψ

omit Fchar in
theorem expr_αβ_comm_αβψ_βψ_as_comm_αβψ_βψ_αβ : forall_ijk_tuv αβ αβψ βψ,
    {αβ, i, t} * ⁅{αβψ, j, u}, {βψ, k, v}⁆ = ⁅{αβψ, j, u}, {βψ, k, v}⁆ * {αβ, i, t} := by
  intro i j k hi hj hk t u v
  grw [commutatorElement_def, inv_of_αβψ hj, inv_of_βψ,
    expr_αβ_αβψ_as_αβψ_αβ, expr_αβ_βψ_as_βψ_αβ hi hk,
    expr_αβ_αβψ_as_αβψ_αβ, expr_αβ_βψ_as_βψ_αβ hi hk]

-- 8.176
theorem comm_of_αβ_α2β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ α2β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 3 2 j hj with ⟨ j₁, j₂, rfl, hj₁, hj₂ ⟩
  have : u = -2 * (-1/2) * u := by field_simp
  rw [this, expr_α2β2ψ_as_comm_of_αβψ_βψ Fchar hj₁ hj₂,
        expr_αβ_comm_αβψ_βψ_as_comm_αβψ_βψ_αβ hi hj₁ hj₂]
declare_B3Large_triv_expr_thm F αβ α2β2ψ

-- 8.177
theorem comm_of_βψ_α2β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk βψ α2β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 2 3 j hj with ⟨ j₁, j₂, rfl, hj₁, hj₂ ⟩
  rw [←one_mul u, ←neg_neg 1, expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar hj₁ hj₂,
        expr_βψ_comm_αβ_β2ψ_as_comm_αβ_β2ψ_βψ hi hj₁ hj₂]
declare_B3Large_triv_expr_thm F βψ α2β2ψ

-- 8.178a
@[simp, chev_simps]
theorem inv_of_α2β2ψ : forall_i_t α2β2ψ,
    {α2β2ψ, i, t}⁻¹ = {α2β2ψ, i, -t}  := by
  intro i hi t
  rcases decompose_5_into_booleans_1_2_2 i hi with ⟨i₁, i₂, i₃, rfl, hi₁, hi₂, hi₃⟩
  rw [eq_of_hR_eq α2β2ψ ((i₁ + i₂) + (i₂ + 2 * i₃)) (by linarith) (-t * (-1)) (by ring),
  eq_of_hR_eq α2β2ψ (i := i₁ + 2 * i₂ + 2 * i₃) ((i₁ + i₂) + (i₂ + 2 * i₃)) (by linarith) (-t * 1) (by ring),
  expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar (by linarith) (by linarith), expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar (by linarith) (by linarith),
  (hom_lift_of_inv_doub_of_αβ_β2ψ hi₁ hi₂ hi₃ _ _).1, neg_neg]
  apply (mul_right_inj ⁅{αβ, i₁ + i₂, -t}, {β2ψ, i₂ + 2 * i₃, 1}⁆).1
  rw [mul_inv_cancel]
  nth_rewrite 2 [←neg_neg t]
  rw [(hom_lift_of_inv_doub_of_αβ_β2ψ hi₁ hi₂ hi₃ (-t) _).2.1]

-- 8.178b
@[group_reassoc]
theorem inv_doub_of_α2β2ψ_b : forall_i_t α2β2ψ,
    {α2β2ψ, i, t} * {α2β2ψ, i, t} = {α2β2ψ, i, 2 * t} := by
  intro i hi t
  rcases decompose_5_into_booleans_1_2_2 i hi with ⟨i₁, i₂, i₃, rfl, hi₁, hi₂, hi₃⟩
  rw [eq_of_hR_eq α2β2ψ ((i₁ + i₂) + (i₂ + 2 * i₃)) (by linarith) (-t * (-1)) (by ring),
  eq_of_hR_eq α2β2ψ (i := i₁ + 2 * i₂ + 2 * i₃) ((i₁ + i₂) + (i₂ + 2 * i₃)) (by linarith) (-(2 * t) * (-1)) (by ring),
  expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar (by linarith) (by linarith), expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar (by linarith) (by linarith),
  (hom_lift_of_inv_doub_of_αβ_β2ψ hi₁ hi₂ hi₃ _ _).2.2]

-- 8.179a
theorem expr_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ : forall_ij_tu αβ β2ψ,
    {α2β2ψ, i + j, -t * u} = {αβ, i, t} * {β2ψ, j, u} * {αβ, i, -t} * {β2ψ, j, -u} := by
  intro i j hi hj t u
  rw [expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar hi hj, ←inv_of_αβ, ←inv_of_β2ψ, commutatorElement_def]

-- 8.179b
theorem expr_α2β2ψ_as_β2ψ_αβ_β2ψ_αβ : forall_ij_tu αβ β2ψ,
    {α2β2ψ, i + j, -t * u} = {β2ψ, j, -u} * {αβ, i, t} * {β2ψ, j, u} * {αβ, i, -t} := by
  intro i j hi hj t u
  apply inv_inj.1
  rw [inv_of_α2β2ψ Fchar (by linarith)]
  simp only [neg_mul, neg_neg, mul_inv_rev, inv_of_αβ, inv_of_β2ψ]
  rw [eq_of_R_eq α2β2ψ (-t * (-u)) (by ring), expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar hi hj,
  ←inv_of_αβ, ←inv_of_β2ψ]
  group

-- 8.180a
@[group_reassoc]
theorem expr_αβ_β2ψ_as_β2ψ_α2β2ψ_αβ : forall_ij_tu αβ β2ψ,
    {αβ, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {α2β2ψ, i + j, -t * u} * {αβ, i, t} := by
  intro i j hi hj t u
  rw [expr_α2β2ψ_as_β2ψ_αβ_β2ψ_αβ Fchar hi hj, ←inv_of_β2ψ, ←inv_of_αβ]
  group

-- 8.180b
@[group_reassoc]
theorem expr_αβ_β2ψ_as_β2ψ_αβ_α2β2ψ : forall_ij_tu αβ β2ψ,
    {αβ, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {αβ, i, t} * {α2β2ψ, i + j, -t * u} := by
  intro i j hi hj t u
  rw [eq_of_R_eq α2β2ψ (- -t * -u) (by ring), expr_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ Fchar hi hj,
  ←inv_of_αβ, neg_neg, neg_neg, ←inv_of_β2ψ]
  group

-- 8.181a
@[group_reassoc]
theorem expr_β_αβ2ψ_as_αβ2ψ_α2β2ψ_β : forall_ij_tu β αβ2ψ,
    {β, i, t} * {αβ2ψ, j, u} = {αβ2ψ, j, u} * {α2β2ψ, i + j, t * u} * {β, i, t} := by
  intro i j hi hj t u
  rw [eq_of_hR_eq α2β2ψ (j + i) (by linarith) (-(-u) * t) (by ring), expr_α2β2ψ_as_comm_of_αβ2ψ_β Fchar hj hi,
  ←inv_of_αβ2ψ Fchar hj]
  group

-- 8.181b
@[group_reassoc]
theorem expr_β_αβ2ψ_as_αβ2ψ_β_α2β2ψ : forall_ij_tu β αβ2ψ,
    {β, i, t} * {αβ2ψ, j, u} = {αβ2ψ, j, u} * {β, i, t} * {α2β2ψ, i + j, t * u} := by
  intro i j hi hj t u
  rw [←neg_neg (t * u), ←inv_of_α2β2ψ Fchar (by linarith), eq_of_hR_eq α2β2ψ (j + i) (by linarith) (-(-u) * (-t)) (by ring),
  expr_α2β2ψ_as_comm_of_αβ2ψ_β Fchar hj hi, comm_swap, ←inv_of_β, ←inv_of_αβ2ψ Fchar hj]
  group

-- 8.182a
@[group_reassoc]
theorem expr_βψ_αβψ_as_αβψ_α2β2ψ_βψ : forall_ij_tu βψ αβψ,
    {βψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {α2β2ψ, i + j, 2 * t * u} * {βψ, i, t} := by
  intro i j hi hj t u
  rw [eq_of_hR_eq α2β2ψ (j + i) (by linarith) (-2 * (-u) *(t)) (by ring),
  expr_α2β2ψ_as_comm_of_αβψ_βψ Fchar hj hi, ←inv_of_αβψ hj]
  group

-- 8.182b
@[group_reassoc]
theorem expr_βψ_αβψ_as_αβψ_βψ_α2β2ψ : forall_ij_tu βψ αβψ,
    {βψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {βψ, i, t} * {α2β2ψ, i + j, 2 * t * u} := by
  intro i j hi hj t u
  rw [←neg_neg (2 * t * u), ←inv_of_α2β2ψ Fchar (by linarith), eq_of_hR_eq α2β2ψ (j + i) (by linarith) (-2 * (-u) * (-t)) (by ring),
  expr_α2β2ψ_as_comm_of_αβψ_βψ Fchar hj hi, comm_swap, ←inv_of_βψ, ←inv_of_αβψ hj]
  group

-- 8.183a
theorem commutator_of_α_βψ_a : forall_ij_tu α βψ,
    ⁅{α, i, t}, {βψ, j, u}⁆ = {αβψ, i + j, t * u} * {α2β2ψ, i + 2 * j, t * u^2} := by
  intro i j hi hj t u
  rw [(generic_comm_of_α_βψ Fchar hi hj _ _).1, eq_of_hR_eq α2β2ψ ((i + j) + j) (by linarith) (-2 * (-t * u) * (u / 2)) (by ring_nf; field_simp),
  expr_α2β2ψ_as_comm_of_αβψ_βψ Fchar (by linarith) hj]

-- 8.183b
theorem commutator_of_α_βψ_b : forall_ij_tu α βψ,
    ⁅{α, i, t}, {βψ, j, u}⁆ = {α2β2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} := by
  intro i j hi hj t u
  rw [(generic_comm_of_α_βψ Fchar hi hj _ _).2, ←neg_neg (t * u^2), ←inv_of_α2β2ψ Fchar (by linarith),
  eq_of_hR_eq α2β2ψ ((i + j) + j) (by linarith) (-2 * (t * u) * (u / 2)) (by ring_nf; field_simp),
  expr_α2β2ψ_as_comm_of_αβψ_βψ Fchar (by linarith) hj, comm_swap]

-- 8.184
theorem sufficient_conditions_for_comm_of_ψ_and_α2β2ψ :
    ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
    (h50a : ∀ (t u : F), ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1)
    (h50b : ∀ (t u : F), ⁅{αβ2ψ, 2 * i + j, t}, {β2ψ, k, u}⁆ = 1),
    ∀ (t u : F), ⁅{ψ, i, t}, {α2β2ψ, j + k, u}⁆ = 1 := by
  intro i j k hi hj hk h50a h50b t u
  have h₁ := fun t u ↦ triv_comm_iff_commutes.1 (h50a t u)
  have h₂ := fun t u ↦ triv_comm_iff_commutes.1 (h50b t u)
  apply triv_comm_iff_commutes.2
  -- expand α2β2ψ into a product of αβ and β2ψ (work on RHS)
  rw [eq_of_R_eq α2β2ψ (-u * -1) (by ring), expr_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ Fchar hj hk, neg_neg]
  -- move ψ fully to the left
  grw [←expr_ψ_β2ψ_as_β2ψ_ψ, expr_αβ_ψ_as_ψ_αβ2ψ_αβψ_αβ Fchar hj hi, ←expr_ψ_β2ψ_as_β2ψ_ψ, expr_αβ_ψ_as_ψ_αβ_αβψ_αβ2ψ Fchar hj hi]
  -- use h₂ to cancel the αβ2ψ elements
  grw [eq_of_h_eq αβ2ψ (2 * i + j) (by linarith), h₂ (-u * t^2)]
  nth_rewrite 2 [eq_of_h_eq αβ2ψ (2 * i + j) (by linarith)]
  rw [neg_mul, ←inv_of_αβ2ψ Fchar (by linarith)]
  grw [rfl]
  -- use h₁ to cancel the αβψ elements
  grw [eq_of_h_eq αβψ (i + j) (by linarith), h₁]
  rw [neg_mul, ←inv_of_αβψ (by linarith)]
  nth_rewrite 2 [eq_of_h_eq αβψ (i + j) (by linarith)]
  grw [rfl]

-- 8.185
theorem partial_comm_of_ψ_α2β2ψ :
    ∀ (t u : F), ⁅{ψ, 1, t}, {α2β2ψ, 0, u}⁆ = 1 := by
  apply sufficient_conditions_for_comm_of_ψ_and_α2β2ψ Fchar (i := 1) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial)
  · intro t u
    rw [triv_comm_symm, lift_hom_comm_of_β2ψ_αβψ (i := 1) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial)]
  · intro t u
    rw [triv_comm_symm, partial_comm_of_β2ψ_αβ2ψ_b (by trivial)]

/- ### ψ and α + 2β + 2ψ commute -/

private lemma comm_of_ψ_α2β2ψ_00 :
    ∀ (t u : F), ⁅{ψ, 0, t}, {α2β2ψ, 0, u}⁆ = 1 := by
  intro t u
  rw [eq_of_R_eq α2β2ψ (-u * -1) (by ring),
  expr_α2β2ψ_as_comm_of_αβ_β2ψ (i := 0) (j := 0) Fchar (by trivial) (by trivial),
  hom_lift_of_comm_ψ_αβ_β2ψ (i := 0) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial)]

private lemma comm_of_ψ_α2β2ψ_01 :
    ∀ (t u : F), ⁅{ψ, 0, t}, {α2β2ψ, 1, u}⁆ = 1 := by
  intro t u
  rw [eq_of_R_eq α2β2ψ (-u * -1) (by ring),
  expr_α2β2ψ_as_comm_of_αβ_β2ψ (i := 1) (j := 0) Fchar (by trivial) (by trivial),
  hom_lift_of_comm_ψ_αβ_β2ψ (i := 1) (j := 0) (k := 0) (by trivial) (by trivial) (by trivial)]

private lemma comm_of_ψ_α2β2ψ_02 :
    ∀ (t u : F), ⁅{ψ, 0, t}, {α2β2ψ, 2, u}⁆ = 1 := by
  intro t u
  rw [eq_of_R_eq α2β2ψ (-u * -1) (by ring),
  expr_α2β2ψ_as_comm_of_αβ_β2ψ (i := 1) (j := 1) Fchar (by trivial) (by trivial),
  hom_lift_of_comm_ψ_αβ_β2ψ (i := 0) (j := 1) (k := 0) (by trivial) (by trivial) (by trivial)]

private lemma comm_of_ψ_α2β2ψ_03 :
    ∀ (t u : F), ⁅{ψ, 0, t}, {α2β2ψ, 3, u}⁆ = 1 := by
  intro t u
  rw [eq_of_R_eq α2β2ψ (-u * -1) (by ring),
  expr_α2β2ψ_as_comm_of_αβ_β2ψ (i := 2) (j := 1) Fchar (by trivial) (by trivial),
  hom_lift_of_comm_ψ_αβ_β2ψ (i := 1) (j := 1) (k := 0) (by trivial) (by trivial) (by trivial)]

private lemma comm_of_ψ_α2β2ψ_10 :
    ∀ (t u : F), ⁅{ψ, 1, t}, {α2β2ψ, 0, u}⁆ = 1 :=
  partial_comm_of_ψ_α2β2ψ Fchar

private lemma comm_of_ψ_α2β2ψ_11 :
    ∀ (t u : F), ⁅{ψ, 1, t}, {α2β2ψ, 1, u}⁆ = 1 := by
  intro t u
  rw [eq_of_R_eq α2β2ψ (-u * -1) (by ring),
  expr_α2β2ψ_as_comm_of_αβ2ψ_β (i := 1) (j := 0) Fchar (by trivial) (by trivial),
  partial_comm_of_ψ_αβ2ψ_β (by trivial)]

-- reflected theorems
declare_B3Large_triv_comm_reflected_thm F b3large_valid ψ α2β2ψ heights 0 4 to 1 1
declare_B3Large_triv_comm_reflected_thm F b3large_valid ψ α2β2ψ heights 0 5 to 1 0
declare_B3Large_triv_comm_reflected_thm F b3large_valid ψ α2β2ψ heights 1 2 to 0 3
declare_B3Large_triv_comm_reflected_thm F b3large_valid ψ α2β2ψ heights 1 3 to 0 2
declare_B3Large_triv_comm_reflected_thm F b3large_valid ψ α2β2ψ heights 1 4 to 0 1
declare_B3Large_triv_comm_reflected_thm F b3large_valid ψ α2β2ψ heights 1 5 to 0 0

-- 8.186
theorem comm_of_ψ_α2β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk ψ α2β2ψ := by
  intro i j hi hj
  match i, j with
  | 0, 0 => exact comm_of_ψ_α2β2ψ_00 Fchar
  | 0, 1 => exact comm_of_ψ_α2β2ψ_01 Fchar
  | 0, 2 => exact comm_of_ψ_α2β2ψ_02 Fchar
  | 0, 3 => exact comm_of_ψ_α2β2ψ_03 Fchar
  | 0, 4 => exact comm_of_ψ_α2β2ψ_04 Fchar
  | 0, 5 => exact comm_of_ψ_α2β2ψ_05 Fchar
  | 1, 0 => exact comm_of_ψ_α2β2ψ_10 Fchar
  | 1, 1 => exact comm_of_ψ_α2β2ψ_11 Fchar
  | 1, 2 => exact comm_of_ψ_α2β2ψ_12 Fchar
  | 1, 3 => exact comm_of_ψ_α2β2ψ_13 Fchar
  | 1, 4 => exact comm_of_ψ_α2β2ψ_14 Fchar
  | 1, 5 => exact comm_of_ψ_α2β2ψ_15 Fchar
declare_B3Large_triv_expr_thm F ψ α2β2ψ

-- 8.187
theorem comm_of_β2ψ_α2β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk β2ψ α2β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [eq_of_R_eq β2ψ (2 * t * (1 / 2)) (by field_simp), expr_β2ψ_as_ψ_βψ_ψ_βψ]
  grw [expr_βψ_α2β2ψ_as_α2β2ψ_βψ Fchar hi₂, expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar hi₁,
  expr_βψ_α2β2ψ_as_α2β2ψ_βψ Fchar hi₂, expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar hi₁]
declare_B3Large_triv_expr_thm F β2ψ α2β2ψ

-- 8.188
theorem comm_of_αβψ_α2β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβψ α2β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 2 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [←mul_one t, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  grw [expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar, expr_αβ_α2β2ψ_as_α2β2ψ_αβ Fchar,
  expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar, expr_αβ_α2β2ψ_as_α2β2ψ_αβ Fchar, expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar]
declare_B3Large_triv_expr_thm F αβψ α2β2ψ

-- 8.189
theorem comm_of_αβ2ψ_α2β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ2ψ α2β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 3 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [eq_of_R_eq αβ2ψ (-2 * t * (-1 / 2)) (by field_simp), expr_αβ2ψ_as_αβψ_ψ_αβψ_ψ Fchar hi₁ hi₂]
  grw [expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar, expr_αβψ_α2β2ψ_as_α2β2ψ_αβψ Fchar,
  expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar, expr_αβψ_α2β2ψ_as_α2β2ψ_αβψ Fchar]
declare_B3Large_triv_expr_thm F αβ2ψ α2β2ψ

-- 8.190
theorem comm_of_α2β2ψ :
    mixed_commutes_of_root (weakB3Large F).pres_mk α2β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 4 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [eq_of_R_eq α2β2ψ (-t * (-1)) (by ring), expr_α2β2ψ_as_comm_of_αβ2ψ_β Fchar hi₁ hi₂,
  commutatorElement_def, inv_of_β, inv_of_αβ2ψ Fchar hi₁]
  grw [expr_β_α2β2ψ_as_α2β2ψ_β Fchar, expr_αβ2ψ_α2β2ψ_as_α2β2ψ_αβ2ψ Fchar,
  expr_β_α2β2ψ_as_α2β2ψ_β Fchar, expr_αβ2ψ_α2β2ψ_as_α2β2ψ_αβ2ψ Fchar]
declare_B3Large_mixed_expr_thm F α2β2ψ

-- 8.191
theorem comm_of_αβψ_β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβψ β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  -- expand αβψ into product of αβ and ψ elements (work on LHS)
  rcases decompose 2 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [eq_of_R_eq αβψ (-2 * (-t / 2) * 1) (by ring_nf; field_simp), expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  -- move β2ψ from the right to the left
  grw [expr_ψ_β2ψ_as_β2ψ_ψ, expr_αβ_β2ψ_as_β2ψ_α2β2ψ_αβ Fchar hi₁ hj, expr_ψ_β2ψ_as_β2ψ_ψ,
  expr_αβ_β2ψ_as_β2ψ_αβ_α2β2ψ Fchar hi₁ hj, expr_ψ_β2ψ_as_β2ψ_ψ]
  -- commute α2β2ψ across ψ and cancel
  grw [expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar]
  rw [eq_of_R_eq α2β2ψ (-(t * u)) (by ring_nf; field_simp)]
  nth_rewrite 2 [eq_of_R_eq α2β2ψ (t * u) (by ring_nf; field_simp)]
  rw [←inv_of_α2β2ψ Fchar (add_le_add hi₁ hj), inv_mul_cancel, one_mul]
declare_B3Large_triv_expr_thm F αβψ β2ψ

-- 8.192
theorem comm_of_βψ_αβ2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk βψ αβ2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  -- expand βψ as a product of ψ and β elements (work on LHS)
  rcases decompose 1 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [eq_of_R_eq βψ (-2 * (-1 / 2) * t) (by ring_nf; field_simp), expr_βψ_as_ψ_β_ψ_β_ψ Fchar hi₁ hi₂]
  -- move αβ2ψ fully to the left
  grw [expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar, expr_β_αβ2ψ_as_αβ2ψ_α2β2ψ_β Fchar hi₂ hj,
  expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar, expr_β_αβ2ψ_as_αβ2ψ_β_α2β2ψ Fchar hi₂ hj, expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar]
  -- commute α2β2ψ across ψ and cancel
  grw [expr_ψ_α2β2ψ_as_α2β2ψ_ψ Fchar]
  rw [neg_mul, ←inv_of_α2β2ψ Fchar (add_le_add hi₂ hj), mul_inv_cancel, one_mul]
declare_B3Large_triv_expr_thm F βψ αβ2ψ

-- 8.193
theorem comm_of_β2ψ_αβ2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk β2ψ αβ2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [eq_of_R_eq β2ψ (2 * t * (1 / 2)) (by field_simp), expr_β2ψ_as_ψ_βψ_ψ_βψ hi₁ hi₂]
  grw [expr_βψ_αβ2ψ_as_αβ2ψ_βψ Fchar, expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar,
  expr_βψ_αβ2ψ_as_αβ2ψ_βψ Fchar, expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar]
declare_B3Large_triv_expr_thm F β2ψ αβ2ψ

-- 8.194
theorem comm_of_αβψ_αβ2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβψ αβ2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [←mul_one t, expr_αβψ_as_βψ_α_βψ_α_βψ hi₁ hi₂]
  grw [expr_βψ_αβ2ψ_as_αβ2ψ_βψ Fchar, expr_α_αβ2ψ_as_αβ2ψ_α Fchar, expr_βψ_αβ2ψ_as_αβ2ψ_βψ Fchar,
  expr_α_αβ2ψ_as_αβ2ψ_α Fchar, expr_βψ_αβ2ψ_as_αβ2ψ_βψ Fchar]
declare_B3Large_triv_expr_thm F αβψ αβ2ψ

-- 8.195
theorem comm_of_αβ2ψ :
    mixed_commutes_of_root (weakB3Large F).pres_mk αβ2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 3 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [eq_of_R_eq αβ2ψ (-2 * t * (-1 / 2)) (by ring_nf; field_simp), expr_αβ2ψ_as_ψ_αβψ_ψ_αβψ Fchar hi₁ hi₂]
  grw [expr_αβψ_αβ2ψ_as_αβ2ψ_αβψ Fchar, expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar,
  expr_αβψ_αβ2ψ_as_αβ2ψ_αβψ Fchar, expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar]
declare_B3Large_mixed_expr_thm F αβ2ψ

-- 8.196
@[simp, chev_simps]
theorem lin_of_αβ2ψ : lin_of_root((weakB3Large F).pres_mk, αβ2ψ) := by
  intro i hi t u
  rcases decompose 1 3 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  -- expand one αβ2ψ as product of α and β2ψ elements (work on LHS)
  rw [←mul_one t, expr_αβ2ψ_as_α_β2ψ_α_β2ψ Fchar hi₁ hi₂]
  -- move the αβ2ψ to the left but not all the way
  grw [expr_β2ψ_αβ2ψ_as_αβ2ψ_β2ψ Fchar, expr_α_αβ2ψ_as_αβ2ψ_α Fchar, expr_β2ψ_αβ2ψ_as_αβ2ψ_β2ψ Fchar]
  -- expand αβ2ψ as product of α and β2ψ elements
  rw [←mul_one u, expr_αβ2ψ_as_α_β2ψ_α_β2ψ Fchar hi₁ hi₂, ←inv_of_β2ψ]
  -- collect back into an αβ2ψ term
  grw [rfl]
  rw [←mul_one (t + u), expr_αβ2ψ_as_α_β2ψ_α_β2ψ Fchar hi₁ hi₂]
  group

-- 8.197
@[simp, chev_simps]
theorem lin_of_α2β2ψ : lin_of_root((weakB3Large F).pres_mk, α2β2ψ) := by
  intro i hi t u
  rcases decompose 2 3 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  -- expand one α2β2ψ as product of αβ and β2ψ elements (work on LHS)
  rw [eq_of_R_eq α2β2ψ (-t * -1) (by ring), expr_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ Fchar hi₁ hi₂, neg_neg]
  -- move the α2β2ψ to the left but not all the way
  grw [expr_β2ψ_α2β2ψ_as_α2β2ψ_β2ψ Fchar, expr_αβ_α2β2ψ_as_α2β2ψ_αβ Fchar, expr_β2ψ_α2β2ψ_as_α2β2ψ_β2ψ Fchar]
  -- expand α2β2ψ as product of αβ and β2ψ elements
  rw [eq_of_R_eq α2β2ψ (-u * -1) (by ring), expr_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ Fchar hi₁ hi₂, neg_neg, ←inv_of_β2ψ]
  -- collect back into α2β2ψ term
  grw [rfl]
  rw [eq_of_R_eq α2β2ψ (-(t + u) * -1) (by ring), expr_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ Fchar hi₁ hi₂]
  group

-- 8.198
theorem hom_lift_of_comm_of_α_α2β2ψ_square : forall_ijk_tu α β ψ,
    ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 2 * k, -t * u^2}⁆ = 1 := by
  intro i j k hi hj hk t u
  have hi : i ≤ 1 := by ht
  have hj : j ≤ 1 := by ht
  have hk : k ≤ 1 := by ht
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
  have aux₁ : {α, i, t} = {α, 1, t₁} * {α, 0, t₀} := by
    fin_cases hf_i, hf_j, hf_k
    <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
  have aux₂ : {αβ, i + j, t} = {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} := by
    fin_cases hf_i, hf_j, hf_k
    <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
  have aux₃ : {β2ψ, j + 2 * k, u^2} = {β2ψ, 3, u₁ * v₁^2} * {β2ψ, 2, u₀ * v₁^2 + 2 * u₁ * v₀ * v₁}
          * {β2ψ, 1, u₁ * v₀^2 + 2 * u₀ * v₀ * v₁} * {β2ψ, 0, u₀ * v₀^2} := by
    fin_cases hf_i, hf_j, hf_k
    <;> chev_simp [pow_two, t₀, t₁, u₀, u₁, v₀, v₁]
  rw [eq_of_h_eq α2β2ψ ((i + j) + (j + 2 * k)) (by linarith),
  expr_α2β2ψ_as_comm_of_αβ_β2ψ Fchar (add_le_add hi hj) (by linarith), aux₁, aux₂, aux₃,
  raw_nonhomog_lift_of_comm_of_α_α2β2ψ]


-- 8.199
include F_sum_of_squares

-- 8.200
theorem hom_lift_of_comm_of_α_α2β2ψ : forall_ijk_tu α β ψ,
    ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 2 * k, u}⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_α]; group
  rcases F_sum_of_squares (-u / t) with ⟨r, s, hrs⟩
  have := (mul_left_inj' ht).2 hrs
  ring_nf at this
  field_simp at this
  have hu : u = (-t * r^2) + (-t * s^2) := by
    rw [neg_mul, neg_mul, ←neg_add]
    exact neg_eq_iff_eq_neg.1 this
  have h₁ := triv_comm_iff_commutes.1 (hom_lift_of_comm_of_α_α2β2ψ_square Fchar hi hj hk t r)
  have h₂ :=  triv_comm_iff_commutes.1 (hom_lift_of_comm_of_α_α2β2ψ_square Fchar hi hj hk t s)
  apply triv_comm_iff_commutes.2
  rw [hu, ←lin_of_α2β2ψ Fchar]
  grw [h₁, h₂]

-- 8.201
theorem nonhomog_lift_of_comm_of_α_α2β2ψ : forall_ij_tu α β,
    ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 1, u}⁆ = 1 := by
  intro i j hi hj t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_α]; group
  have hi : i ≤ 1 := by ht
  have hj : j ≤ 1 := by ht
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
  let v₁ : F := 1
  let v₀ : F := u / (2 * t)
  have hf_i : i ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
  have hf_j : j ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
  have aux₁ : 2 * (u / (2 * t)) = u / t := by ring_nf; field_simp; group
  have aux₂ : (u / (2 * t))^2 = u^2 / (4 * t^2) := by sorry
  have hα : {α, 1, t₁} * {α, 0, t₀} = {α, i, t} := by
    fin_cases hf_i, hf_j
    <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
  have hαβ : {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} = {αβ, i + j, t} := by
    fin_cases hf_i, hf_j
    <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
  have hβ2ψ : {β2ψ, 3, u₁ * v₁^2} * {β2ψ, 2, u₀ * v₁^2 + 2 * u₁ * v₀ * v₁}
          * {β2ψ, 1, u₁ * v₀^2 + 2 * u₀ * v₀ * v₁} * {β2ψ, 0, u₀ * v₀^2}
          = {β2ψ, j + 2, 1} * {β2ψ, j + 1, u / t} * {β2ψ, j, u^2 / (4 * t^2)} := by
    fin_cases hf_i, hf_j
    <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁, aux₁, aux₂, pow_two, one_mul]
  rw [←raw_nonhomog_lift_of_comm_of_α_α2β2ψ t₁ t₀ u₁ u₀ v₁ v₀, hα, hαβ, hβ2ψ, commutatorElement_def,
  commutatorElement_def, commutatorElement_def]
  sorry

-- 8.202
omit F_sum_of_squares in
theorem sufficient_conditions_for_comm_of_αβ_and_αβ2ψ :
    ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 4)
    (hyp : ∀ (t u : F), ⁅{α, i, t}, {α2β2ψ, j + k, u}⁆ = 1),
    ∀ (t u : F), ⁅{αβ, i + j, t}, {αβ2ψ, k, u}⁆ = 1 := by
  intro i j k hi hj hk hyp t u
  have hyp' := fun t u ↦ triv_comm_iff_commutes.1 (hyp t u)
  apply triv_comm_iff_commutes.2
  -- expand αβ into product of α and β elements (work on LHS)
  rw [←one_mul t, expr_αβ_as_α_β_α_β]
  -- move αβ2ψ to the left
  grw [expr_β_αβ2ψ_as_αβ2ψ_α2β2ψ_β Fchar hj hk, expr_α_αβ2ψ_as_αβ2ψ_α Fchar hi,
  expr_β_αβ2ψ_as_αβ2ψ_β_α2β2ψ Fchar hj hk, expr_α_αβ2ψ_as_αβ2ψ_α Fchar hi]
  -- use hyp to cancel the αβ2ψ elements
  grw [hyp' (-1)]
  rw [neg_mul, ←inv_of_α2β2ψ Fchar (by linarith), mul_inv_cancel, one_mul]

-- 8.203
theorem partial_comm_of_αβ_α2β2ψ :
    ∀ (t u : F), ⁅{αβ, 0, t}, {αβ2ψ, 1, u}⁆ = 1 := by
  apply sufficient_conditions_for_comm_of_αβ_and_αβ2ψ (i := 0) (j := 0) (k := 1) Fchar (by trivial) (by trivial) (by trivial)
  intro t u
  rw [nonhomog_lift_of_comm_of_α_α2β2ψ (i := 0) (j := 0) (by trivial) (by trivial) (by trivial) (by trivial)]

-- 8.204
omit F_sum_of_squares in
theorem sufficient_conditions_for_comm_of_α_and_α2β2ψ :
    ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
    (hyp : ∀ (t u : F), ⁅{αβ, j, t}, {αβ2ψ, i + k, u}⁆ = 1),
    ∀ (t u : F), ⁅{α, i, t}, {α2β2ψ, j + k, u}⁆ = 1 := by
  intro i j k hi hj hk hyp t u
  have hyp' := fun t u ↦ triv_comm_iff_commutes.1 (hyp t u)
  apply triv_comm_iff_commutes.2
  -- expand α2β2ψ as product of αβ and β2ψ elements (work on LHS)
  rw [eq_of_R_eq α2β2ψ (-u * (-1)) (by ring), expr_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ Fchar hj hk, neg_neg]
  -- move the α element fully to the right
  grw [expr_α_αβ_as_αβ_α, expr_α_β2ψ_as_β2ψ_αβ2ψ_α Fchar hi hk, expr_α_αβ_as_αβ_α, expr_α_β2ψ_as_αβ2ψ_β2ψ_α Fchar hi hk]
  -- use hyp to cancel to the αβ2ψ elements
  grw [hyp' (-u)]
  rw [←inv_of_αβ2ψ Fchar (by linarith), inv_mul_cancel, one_mul]


-- 8.205
theorem partial_comm_of_α_α2β2ψ :
    ∀ (t u : F), ⁅{α, 1, t}, {α2β2ψ, 0, u}⁆ = 1 := by
  apply sufficient_conditions_for_comm_of_α_and_α2β2ψ (i := 1) (j := 0) (k := 0) Fchar (by trivial) (by trivial) (by trivial)
  exact partial_comm_of_αβ_α2β2ψ Fchar F_sum_of_squares

/- ### α and α + 2β + 2ψ commute -/

private lemma comm_of_α_α2β2ψ_00 :
    ∀ (t u : F), ⁅{α, 0, t}, {α2β2ψ, 0, u}⁆ = 1 :=
  @hom_lift_of_comm_of_α_α2β2ψ F _ Fchar F_sum_of_squares 0 0 0 (by trivial) (by trivial) (by trivial)

private lemma comm_of_α_α2β2ψ_01 :
    ∀ (t u : F), ⁅{α, 0, t}, {α2β2ψ, 1, u}⁆ = 1 :=
  @nonhomog_lift_of_comm_of_α_α2β2ψ F _ Fchar F_sum_of_squares 0 0 (by trivial) (by trivial)

private lemma comm_of_α_α2β2ψ_02 :
    ∀ (t u : F), ⁅{α, 0, t}, {α2β2ψ, 2, u}⁆ = 1 :=
  @hom_lift_of_comm_of_α_α2β2ψ F _ Fchar F_sum_of_squares 0 1 0 (by trivial) (by trivial) (by trivial)

private lemma comm_of_α_α2β2ψ_03 :
    ∀ (t u : F), ⁅{α, 0, t}, {α2β2ψ, 3, u}⁆ = 1 :=
  @nonhomog_lift_of_comm_of_α_α2β2ψ F _ Fchar F_sum_of_squares 0 1 (by trivial) (by trivial)

private lemma comm_of_α_α2β2ψ_04 :
    ∀ (t u : F), ⁅{α, 0, t}, {α2β2ψ, 4, u}⁆ = 1 :=
  @hom_lift_of_comm_of_α_α2β2ψ F _ Fchar F_sum_of_squares 0 1 1 (by trivial) (by trivial) (by trivial)

private lemma comm_of_α_α2β2ψ_10 :
    ∀ (t u : F), ⁅{α, 1, t}, {α2β2ψ, 0, u}⁆ = 1 :=
  partial_comm_of_α_α2β2ψ Fchar F_sum_of_squares

-- reflected theorems
declare_B3Large_triv_comm_reflected_thm F b3large_valid α α2β2ψ heights 0 5 to 1 0
declare_B3Large_triv_comm_reflected_thm F b3large_valid α α2β2ψ heights 1 1 to 0 4
declare_B3Large_triv_comm_reflected_thm F b3large_valid α α2β2ψ heights 1 2 to 0 3
declare_B3Large_triv_comm_reflected_thm F b3large_valid α α2β2ψ heights 1 3 to 0 2
declare_B3Large_triv_comm_reflected_thm F b3large_valid α α2β2ψ heights 1 4 to 0 1
declare_B3Large_triv_comm_reflected_thm F b3large_valid α α2β2ψ heights 1 5 to 0 0

-- 8.206
theorem comm_of_α_α2β2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk α α2β2ψ := by
  intro i j hi hj
  match i, j with
  | 0, 0 => exact comm_of_α_α2β2ψ_00 Fchar F_sum_of_squares
  | 0, 1 => exact comm_of_α_α2β2ψ_01 Fchar F_sum_of_squares
  | 0, 2 => exact comm_of_α_α2β2ψ_02 Fchar F_sum_of_squares
  | 0, 3 => exact comm_of_α_α2β2ψ_03 Fchar F_sum_of_squares
  | 0, 4 => exact comm_of_α_α2β2ψ_04 Fchar F_sum_of_squares
  | 0, 5 => exact comm_of_α_α2β2ψ_05 Fchar F_sum_of_squares
  | 1, 0 => exact comm_of_α_α2β2ψ_10 Fchar F_sum_of_squares
  | 1, 1 => exact comm_of_α_α2β2ψ_11 Fchar F_sum_of_squares
  | 1, 2 => exact comm_of_α_α2β2ψ_12 Fchar F_sum_of_squares
  | 1, 3 => exact comm_of_α_α2β2ψ_13 Fchar F_sum_of_squares
  | 1, 4 => exact comm_of_α_α2β2ψ_14 Fchar F_sum_of_squares
  | 1, 5 => exact comm_of_α_α2β2ψ_15 Fchar F_sum_of_squares

-- 8.207
theorem comm_of_αβ_αβ2ψ :
    trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ αβ2ψ := by
  intro i j hi hj
  rcases decompose 1 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  apply sufficient_conditions_for_comm_of_αβ_and_αβ2ψ Fchar (by trivial) (by trivial) (by trivial)
  intro t u
  apply comm_of_α_α2β2ψ Fchar F_sum_of_squares hi₁
declare_B3Large_triv_expr_thm F αβ αβ2ψ

-- 8.208
theorem comm_of_αβψ :
    mixed_commutes_of_root (weakB3Large F).pres_mk αβψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  -- expand the left αβψ as a product of αβ and ψ elements (work on the LHS)
  rcases decompose 2 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [←mul_one t, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  -- move αβψ to the left
  grw [expr_ψ_αβψ_as_αβψ_αβ2ψ_ψ Fchar hi₂ hj, expr_αβ_αβψ_as_αβψ_αβ, expr_ψ_αβψ_as_αβψ_αβ2ψ_ψ Fchar hi₂ hj,
  expr_αβ_αβψ_as_αβψ_αβ, expr_ψ_αβψ_as_αβψ_ψ_αβ2ψ Fchar hi₂ hj]
  -- cancel the α2β2ψ terms
  grw [←expr_αβ_αβ2ψ_as_αβ2ψ_αβ Fchar F_sum_of_squares, expr_αβ_αβ2ψ_as_αβ2ψ_αβ Fchar F_sum_of_squares,
  expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar]
  rw [lin_of_αβ2ψ Fchar, lin_of_αβ2ψ Fchar]
  ring_nf; field_simp; ring_nf
  rw [id_of_αβ2ψ Fchar]
declare_B3Large_mixed_expr_thm F αβψ

-- 8.209
@[simp, chev_simps]
theorem lin_of_αβψ : lin_of_root((weakB3Large F).pres_mk, αβψ) := by
  intro i hi t u
  rcases decompose 2 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  -- expand one αβψ element into a product of ψ and αβ elements (work on LHS)
  rw [←mul_one t, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  -- move αβψ from right to middle
  grw [expr_ψ_αβψ_as_αβψ_ψ_αβ2ψ Fchar hi₂ (add_le_add hi₁ hi₂), expr_αβ_αβψ_as_αβψ_αβ]
  -- expand the other αβψ element in the same way as before
  rw [←mul_one u, expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  -- simplify the product of ψ elements using linearity
  grw [rfl]
  -- commute ψ and αβ elements
  grw [expr_ψ_αβ_as_αβ_αβ2ψ_αβψ_ψ Fchar hi₁ hi₂ (t := u), expr_αβ_ψ_as_ψ_αβψ_αβ2ψ_αβ Fchar hi₁ hi₂ (t := -u)]
  -- commute αβψ across ψ and cancel
  grw [expr_ψ_αβψ_as_αβψ_αβ2ψ_ψ Fchar hi₂ (add_le_add hi₁ hi₂)]
  rw [eq_of_R_eq αβψ (-(u / 2)) (by ring_nf; field_simp; group)]
  nth_rewrite 2 [eq_of_R_eq αβψ (u / 2) (by ring_nf)]
  rw [←inv_of_αβψ (add_le_add hi₁ hi₂)]
  grw [expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar, expr_αβ_αβ2ψ_as_αβ2ψ_αβ Fchar F_sum_of_squares]
  nth_rewrite 2 [eq_of_h_eq αβ2ψ (i₁ + 2 * i₂) (by linarith)]
  nth_rewrite 4 [eq_of_h_eq αβ2ψ (i₁ + 2 * i₂) (by linarith)]
  grw [lin_of_αβ2ψ Fchar, expr_ψ_αβ2ψ_as_αβ2ψ_ψ Fchar, lin_of_αβ2ψ Fchar, lin_of_αβ2ψ Fchar]
  rw [eq_of_R_eq αβ2ψ 0 (by ring_nf; field_simp; ring_nf), id_of_αβ2ψ Fchar, mul_one]
  -- collect back into an αβψ term
  rw [←mul_one (t + u), expr_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  ring_nf; field_simp; ring_nf

end Steinberg.B3Large
