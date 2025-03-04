/-

LICENSE goes here.

-/

import Steinberg.B3Small.Basic

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

import Steinberg.Defs.Deg
import Steinberg.Defs.Commutator
import Steinberg.Defs.ReflDeg

import Steinberg.Upstream.FreeGroup

namespace Steinberg.B3Small

open Steinberg B3SmallPosRoot GradedGen ReflDeg

variable {F : Type TF} [Field F] (Fchar : (2 : F) ≠ 0)

/-! ### Double commutator theorem -/

theorem comm_of_β_ψ : double_commutator_of_root_pair (weakB3Small F).pres_mk β ψ βψ β2ψ 1 1 (by rfl) (by rfl) :=
  (weakB3Small F).double_commutator_helper β ψ βψ β2ψ 1 1 (by rfl) (by rfl)
    (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Nonhomogeneous lift -/
theorem nonhomog_lift_of_comm_of_βψ_ψω :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀}
    , {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} ⁆
    = 1 := by
  hom_tac rels_of_nonhomog_lift_of_comm_of_βψ_ψω [t₁, t₀, u₁, u₀, v₁, v₀]

/-! ### Definition of missing root -/
theorem def_of_βψω :
  forall_i_t βψω,
    ⁅ {β, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1
    , {ψω, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
      = {βψω, i, t} := by
  intro t i hi
  apply WeakChevalley.helper
  apply (weakB3Small F).def_helper rels_of_def_of_βψω
  · simp only [weakB3Small, def_sets, Set.mem_singleton_iff]
  · exists t, i, hi

theorem refl_of_nonhomog :
  ∀ S ∈ nonhomog_sets F,
    ∀ r ∈ S, (weakB3Small F).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [nonhomog_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_βψ_ψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, rfl ⟩
  simp only [free_mk_mk, map_commutatorElement, map_mul, FreeGroup.map.of, refl_deg_of_gen,
    PosRootSys.height, height, tsub_self, Nat.add_one_sub_one, tsub_zero]
  repeat rw [← free_mk_mk]
  rw [add_comm, add_comm (u₁ * v₀)]
  grw [expr_βψ_βψ_as_βψ_βψ, expr_βψ_βψ_as_βψ_βψ (i := 0), expr_βψ_βψ_as_βψ_βψ,
    expr_ψω_ψω_as_ψω_ψω, expr_ψω_ψω_as_ψω_ψω (i := 0), expr_ψω_ψω_as_ψω_ψω]
  exact nonhomog_lift_of_comm_of_βψ_ψω t₀ t₁ u₀ u₁ v₀ v₁

-- def relations are preserved under reflection
theorem refl_of_def : ∀ S ∈ def_sets F, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  simp only [def_sets, Set.mem_singleton_iff, forall_eq, rels_of_def_of_βψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ i, hi, t, rfl ⟩
  chev_simp [split_3_into_1_2]
  exists (βψω.height - i), (by omega), t
  split <;> congr

theorem b3small_valid : ReflDeg.refl_valid (weakB3Small F) :=
  ⟨refl_of_nonhomog, refl_of_def⟩

/-! ### 8.37 -/

theorem expr_βψ_as_ψ_β_ψ_β_ψ :
  forall_ij_tu β ψ,
    {βψ, i + j, 2 * t * u} =
    {ψ, j, -u} * {β, i, t} * {ψ, j, 2 * u} * {β, i, -t} * {ψ, j, -u} := by
  intro i j hi hj t u
  have hi' : i ≤ βψ.height := by ht
  have hij : i + j ≤ βψ.height := by ht
  have hi2j : i + 2 * j ≤ PosRootSys.height β2ψ := by
    simp only [PosRootSys.height, height] at hi hj ⊢; omega
  rw [← mul_inv_eq_iff_eq_mul]
  mar; rw [← inv_mul_eq_iff_eq_mul]
  chev_simp; mal
  rw [expr_ψ_βψ_as_β2ψ_βψ_ψ (i := j) (j := i + j) hj hij u (2 * t * u)]
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ (i := j) (j := i + j) hj hij u (2 * t * u)]
  have h_comm := comm_of_β_ψ hi hj t (2 * u)
  chev_simp at h_comm
  rw [expr_βψ_β2ψ_as_β2ψ_βψ] at h_comm
  rw [eq_of_h_eq β2ψ (i + 2 * j) _ (j + (i + j)) (by omega)] at h_comm
  rw [eq_of_R_eq β2ψ _ _ _ (2 * u * (2 * t * u)) (by ring)] at h_comm
  clear hi2j
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ hj hij u (2 * t * u)] at h_comm
  grw [lin_of_βψ] at h_comm
  ring_nf at h_comm
  grw [id_of_βψ, commutatorElement_def] at h_comm
  rw [← inv_of_ψ _ (u * 2), mul_inv_eq_iff_eq_mul] at h_comm
  mar at h_comm
  rw [lin_of_ψ] at h_comm
  ring_nf at h_comm
  mal at h_comm
  rw [eq_of_R_eq βψ _ _ _ (2 * t * u)] at h_comm
  grw [← h_comm, mul_comm]
  ring

/-! ### Derive full commutator for βψ and ψω from nonhomogeneous lift -/

-- NS: this section should probably be abstracted for reuse

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) (via the previous theorem). -/
private lemma homog_lift_of_comm_of_βψ_ψω (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : F), ⁅ { βψ, i + j, t}, {ψω, j + k, u} ⁆ = 1 := by
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
    have hf_i : i ∈ [0,1] := mem_list_range_iff_le.mp hi
    have hf_j : j ∈ [0,1] := mem_list_range_iff_le.mp hj
    have hf_k : k ∈ [0,1] := mem_list_range_iff_le.mp hk
    have id₁ : {βψ, i + j, t} = {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp only [t₀, t₁, u₀, u₁, v₀, v₁]
        simp only [add_zero, mul_zero, zero_mul, mul_one, zero_add]
        repeat rw [id_of_βψ]
        simp only [one_mul, mul_one]
      )
    )
    have id₂ : {ψω, j + k, u} = {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp only [t₀, t₁, u₀, u₁, v₀, v₁]
        simp only [add_zero, mul_zero, zero_mul, one_mul, zero_add]
        repeat rw [id_of_ψω]
        simp only [one_mul, mul_one]
      )
    )
    rw [id₁, id₂, nonhomog_lift_of_comm_of_βψ_ψω]

private lemma image_of_homog_lift_of_comm_of_βψ_ψω {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ψω.height) :
  ((i, j) ∈ ij_jk_image) → ∀ (t u : F), ⁅ {βψ, i, t}, {ψω, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  have ⟨ ijk', ⟨ h_in_cube, h_f ⟩ ⟩ := this
  have ⟨ hi', hj', hk' ⟩ := mem_range_of_boolean_cube ijk' h_in_cube
  let ⟨ i', j', k' ⟩ := ijk'
  have h_f' : i = i' + j' ∧ j = j' + k' := by rw [← Prod.mk.injEq, ← h_f, f_ij_jk]
  rw [← homog_lift_of_comm_of_βψ_ψω i' j' k' hi' hj' hk' t u]
  simp only [h_f']

private lemma comm_of_βψ_ψω_20 : ∀ (t u : F), ⁅ {βψ, 2, t}, {ψω, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {ψω, 1, u} _ ({βψ, 1, t + 1} * {βψ, 0, 1})
  mul_assoc_l
  rw [← nonhomog_lift_of_comm_of_βψ_ψω t 1 1 1 0 u]
  simp only [one_mul, mul_one, mul_zero, add_zero]
  rw [id_of_ψω] -- NS: maybe should be a simp lemma? we can decide...
  rw [one_mul]
  rw [← homog_lift_of_comm_of_βψ_ψω 1 1 0 (by trivial) (by trivial) (by trivial) t u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_βψ_ψω 0 1 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_βψ_ψω 0 0 1 (by trivial) (by trivial) (by trivial) 1 u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_βψ_ψω 1 0 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_βψ_ψω 0 0 0 (by trivial) (by trivial) (by trivial) 1 u]

-- symmetric to proof of `comm_of_βψ_ψω_20`
private lemma comm_of_βψ_ψω_02 : ∀ (t u : F), ⁅ {βψ, 0, t}, {ψω, 2, u} ⁆ = 1 := by
  intro t u
  have : ⁅{βψ, 0, t}, {ψω, 2, u}⁆ = ReflDeg.refl_symm b3small_valid ⁅{βψ, 2, t}, {ψω, 0, u}⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, comm_of_βψ_ψω_20, map_one]

-- 8.42
theorem comm_of_βψ_ψω : trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψ ψω := by
  intro i j hi hj t u
  have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ ((i, j) ∈ ij_jk_image) := by
    rw [ij_jk_image]
    simp only [PosRootSys.height] at *
    simp only [B3SmallPosRoot.height] at *
    simp -- should fix
    omega
  rcases this with hij | hij | hij
  ·
    let ⟨ hd_i, hd_j ⟩ := hij
    simp_rw [hd_i, hd_j]
    rw [← comm_of_βψ_ψω_02 t u]
  ·
    let ⟨ hd_i, hd_j ⟩ := hij
    simp_rw [hd_i, hd_j]
    rw [← comm_of_βψ_ψω_20 t u]
  ·
    apply image_of_homog_lift_of_comm_of_βψ_ψω hi hj
    exact hij

declare_B3Small_triv_expr_thm F βψ ψω

/-! ### Further useful identities (roughly GENERIC) -/

-- 8.39 a

theorem expr_ψ_ω_as_ω_ψω_ψ :
  forall_ij_tu ψ ω,
    {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψω, i + j, 2 * t * u} * {ψ, i, t} := by
  intro i j hi hj t u
  grw [expr_ψ_ω_as_ψω_ω_ψ]
  stop
  done

-- 8.39 b

theorem expr_ψ_ω_as_ω_ψ_ψω :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : F),
      {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψ, i, t} * {ψω, i + j, 2 * (t * u)} := by sorry

-- 8.40 a

theorem expr_β_ψ_as_ψ_βψ_β2ψ_β :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : F),
      {β, i, t} * {ψ, j, u} = {ψ, j, u} * {βψ, i + j, t * u} *
      {β2ψ, i + 2 * j, -(t * u^2)} * {β, i, t} := by sorry

-- 8.40 b

theorem expr_β_ψ_as_ψ_β_β2ψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : F),
      {β, i, t} * {ψ, j, u} = {ψ, j, u}  * {β, i, t} * {β2ψ, i + 2 * j, -(t * u^2)}
      * {βψ, i + j, t * u} := by sorry

-- 8.41

theorem expr_ψ_β_as_βψ_β2ψ_β_ψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ β.height) (t u : F),
      {ψ, j, u} * {β, i, t} =
      {βψ, i + j, -(t * u)} * {β2ψ, i + 2 * j, -(t * u^2)} * {β, i, t} *
      {ψ, j, u} := by sorry

/-! ### Establishing βψω -/

-- 8.43
theorem comm_of_β2ψ_ψω :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk β2ψ ψω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  sorry

declare_B3Small_triv_expr_thm F β2ψ ψω

-- 8.44
theorem Interchange :
    ∀ {i j k : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψ.height) (hk : k ≤ ω.height) (t u v : F),
      ⁅ {βψ, i + j, t * u}, {ω, k, v} ⁆ = ⁅ {β, i , t}, {ψω, j + k, 2 * u * v} ⁆ := by sorry

private lemma βt_ψω2u_to_βψt_ωu :
  forall_ijk_tu 1 1 1, ⁅{β, i, t}, {ψω, j + k, 2 * u}⁆ = ⁅{βψ, i + j, t}, {ω, k, u}⁆ := by
  intro i j k hi hj hk t u
  have := Interchange hi hj hk t 1 u
  field_simp at this
  exact this.symm

include Fchar in
private lemma βtu_ψω1_to_βt_ψωu :
  forall_ijk_tu 1 1 1, ⁅{β, i, t * u}, {ψω, j + k, 1}⁆ = ⁅{β, i, t}, {ψω, j + k, u}⁆ := by
  intro i j k hi hj hk t u
  have aux₁ := Interchange hi hj hk (t * u) 1 (1 / 2)
  have aux₂ := Interchange hi hj hk t u (1 / 2)
  field_simp at aux₁
  field_simp at aux₂
  rwa [aux₁] at aux₂

private lemma rewrite_2tu (t u : F) : 2 * t * u = t * (2 * u) := by ring
include Fchar
private lemma rewrite_tu (t u : F) : t * u = 2 * t * (u / 2) := by ring_nf; field_simp

-- height 0
private lemma expand_βψω_as_commutator_of_β_ψω_00 :
  ∀ t u : F, {βψω, 0, t * u} = ⁅{β, 0, t}, {ψω, 0, u}⁆ := by
  intro t u
  have := @def_of_βψω _ _ 0 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, @βtu_ψω1_to_βt_ψωu _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_βψω_as_commutator_of_βψ_ω_00 :
  ∀ t u : F, {βψω, 0, 2 * t * u} = ⁅{βψ, 0, t}, {ω, 0, u}⁆ := by
  intro t u
  rw [rewrite_2tu, expand_βψω_as_commutator_of_β_ψω_00 Fchar, @βt_ψω2u_to_βψt_ωu _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]

-- height 1
private lemma expand_βψω_as_commutator_of_β_ψω_01 :
  ∀ t u : F, {βψω, 1, t * u} = ⁅{β, 0, t}, {ψω, 1, u}⁆ := by
  intro t u
  have := @def_of_βψω _ _ 1 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, @βtu_ψω1_to_βt_ψωu _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_βψω_as_commutator_of_βψ_ω_01 :
  ∀ t u : F, {βψω, 1, 2 * t * u} = ⁅{βψ, 0, t}, {ω, 1, u}⁆ := by
  intro t u
  rw [rewrite_2tu, expand_βψω_as_commutator_of_β_ψω_01 Fchar, @βt_ψω2u_to_βψt_ωu _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expand_βψω_as_commutator_of_βψ_ω_10 :
  ∀ t u : F, {βψω, 1, 2 * t * u} = ⁅{βψ, 1, t}, {ω, 0, u}⁆ := by
  intro t u
  rw [rewrite_2tu, expand_βψω_as_commutator_of_β_ψω_01 Fchar, @βt_ψω2u_to_βψt_ωu _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_βψω_as_commutator_of_β_ψω_10 :
  ∀ t u : F, {βψω, 1, t * u} = ⁅{β, 1, t}, {ψω, 0, u}⁆ := by
  intro t u
  rw [rewrite_tu Fchar, expand_βψω_as_commutator_of_βψ_ω_10 Fchar, ←@βt_ψω2u_to_βψt_ωu _ _ 1 0 0 (by trivial) (by trivial) (by trivial)]
  field_simp

-- height 2 (reflection of height 1)
private lemma expand_βψω_as_commutator_of_β_ψω_11 :
  ∀ t u : F, {βψω, 2, t * u} = ⁅{β, 1, t}, {ψω, 1, u}⁆ := by
  sorry

private lemma expand_βψω_as_commutator_of_β_ψω_02 :
  ∀ t u : F, {βψω, 2, t * u} = ⁅{β, 0, t}, {ψω, 2, u}⁆ := by
  sorry

private lemma expand_βψω_as_commutator_of_βψ_ω_20 :
  ∀ t u : F, {βψω, 2, 2 * t * u} = ⁅{βψ, 2, t}, {ω, 0, u}⁆ := by
  sorry

private lemma expand_βψω_as_commutator_of_βψ_ω_11 :
  ∀ t u : F, {βψω, 2, 2 * t * u} = ⁅{βψ, 1, t}, {ω, 1, u}⁆ := by
  sorry

-- height 3 (reflection of height 0)
private lemma expand_βψω_as_commutator_of_β_ψω_12 :
  ∀ t u : F, {βψω, 3, t * u} = ⁅{β, 1, t}, {ψω, 2, u}⁆ := by
  sorry

private lemma expand_βψω_as_commutator_of_βψ_ω_21 :
  ∀ t u : F, {βψω, 3, 2 * t * u} = ⁅{βψ, 2, t}, {ω, 1, u}⁆ := by
  sorry

-- 8.45a
theorem expand_βψω_as_commutator_of_βψ_ω :
  forall_ij_tu 2 1, {βψω, i + j, 2 * t * u} = ⁅{βψ, i, t}, {ω, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expand_βψω_as_commutator_of_βψ_ω_00 Fchar]
  | 0, 1 => rw [expand_βψω_as_commutator_of_βψ_ω_01 Fchar]
  | 1, 0 => rw [expand_βψω_as_commutator_of_βψ_ω_10 Fchar]
  | 1, 1 => rw [expand_βψω_as_commutator_of_βψ_ω_11 Fchar]
  | 2, 0 => rw [expand_βψω_as_commutator_of_βψ_ω_20 Fchar]
  | 2, 1 => rw [expand_βψω_as_commutator_of_βψ_ω_21 Fchar]

-- 8.45b
theorem expand_βψω_as_commutator_of_β_ψω :
  forall_ij_tu 1 2, {βψω, i + j, t * u} = ⁅{β, i, t}, {ψω, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expand_βψω_as_commutator_of_β_ψω_00 Fchar]
  | 0, 1 => rw [expand_βψω_as_commutator_of_β_ψω_01 Fchar]
  | 0, 2 => rw [expand_βψω_as_commutator_of_β_ψω_02 Fchar]
  | 1, 0 => rw [expand_βψω_as_commutator_of_β_ψω_10 Fchar]
  | 1, 1 => rw [expand_βψω_as_commutator_of_β_ψω_11 Fchar]
  | 1, 2 => rw [expand_βψω_as_commutator_of_β_ψω_12 Fchar]

-- 8.46
theorem expr_βψω_as_βψ_ω_βψ_ω :
  forall_ij_tu 2 1, {βψω, i + j, 2 * t * u} = {βψ, i, t} * {ω, j, u} * {βψ, i, -t} * {ω, j, -u} := by
  intro i j hi hj t u
  rw [expand_βψω_as_commutator_of_βψ_ω Fchar hi hj, ←inv_of_βψ, ←inv_of_ω, commutatorElement_def]

-- 8.47
theorem expr_βψω_as_β_ψω_β_ψω :
  forall_ij_tu 1 2, {βψω, i + j, t * u} = {β, i, t} * {ψω, j, u} * {β, i, -t} * {ψω, j, -u} := by
  intro i j hi hj t u
  rw [expand_βψω_as_commutator_of_β_ψω Fchar hi hj, ←inv_of_β, ←inv_of_ψω, commutatorElement_def]

/-! ### Remaining commutation relations -/

private lemma write_t_as_2tu (t : F) : ∃ (x y : F), t = 2 * x * y := ⟨1/2, t, by field_simp⟩

-- 8.48
theorem comm_of_βψω_ω :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω ω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [←one_mul t, expr_βψω_as_β_ψω_β_ψω Fchar hi₁ hi₂]
  grw [←expr_ω_ψω_as_ψω_ω, expr_β_ω_as_ω_β, ←expr_ω_ψω_as_ψω_ω, expr_β_ω_as_ω_β]
declare_B3Small_triv_expr_thm F βψω ω

-- 8.49
theorem comm_of_βψω_β :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω β := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 2 1 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rcases write_t_as_2tu Fchar t with ⟨x, y, rfl⟩
  rw [expr_βψω_as_βψ_ω_βψ_ω Fchar hi₁ hi₂]
  grw [←expr_β_ω_as_ω_β, expr_β_βψ_as_βψ_β, ←expr_β_βψ_as_βψ_β, expr_β_ω_as_ω_β]
declare_B3Small_triv_expr_thm F βψω β

-- 8.50
theorem comm_of_βψω_ψ :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [←mul_one t, expr_βψω_as_β_ψω_β_ψω Fchar hi₁ hi₂]
  grw [←expr_ψ_ψω_as_ψω_ψ, expr_β_ψ_as_ψ_β_β2ψ_βψ hi₁ hj, ←expr_ψ_ψω_as_ψω_ψ, expr_β_ψ_as_ψ_β_β2ψ_βψ hi₁ hj,
  ←expr_βψ_β2ψ_as_β2ψ_βψ, expr_β2ψ_ψω_as_ψω_β2ψ, expr_β_β2ψ_as_β2ψ_β]
  field_simp
  grw [expr_βψ_ψω_as_ψω_βψ, expr_β_βψ_as_βψ_β]
declare_B3Small_triv_expr_thm F βψω ψ

-- 8.51
theorem comm_of_βψω_ψω :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω ψω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 1 j hj with ⟨j₁, j₂, rfl, hj₁, hj₂⟩
  rcases write_t_as_2tu Fchar u with ⟨x, y, rfl⟩
  grw [expr_ψω_as_ψ_ω_ψ_ω hj₁ hj₂, expr_βψω_ψ_as_ψ_βψω Fchar hi hj₁, expr_βψω_ω_as_ω_βψω Fchar hi hj₂,
  expr_βψω_ψ_as_ψ_βψω Fchar hi hj₁, expr_βψω_ω_as_ω_βψω Fchar]
declare_B3Small_triv_expr_thm F βψω ψω

-- 8.52
theorem comm_of_βψω_βψ :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω βψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 1 j hj with ⟨j₁, j₂, rfl, hj₁, hj₂⟩
  rcases write_t_as_2tu Fchar u with ⟨x, y, rfl⟩
  grw [expr_βψ_as_ψ_β_ψ_β_ψ hj₁ hj₂, expr_βψω_ψ_as_ψ_βψω Fchar, expr_βψω_β_as_β_βψω Fchar, expr_βψω_ψ_as_ψ_βψω Fchar,
  expr_βψω_β_as_β_βψω Fchar, expr_βψω_ψ_as_ψ_βψω Fchar]
declare_B3Small_triv_expr_thm F βψω βψ

-- 8.53
theorem comm_of_βψω_β2ψ :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω β2ψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 j hj with ⟨j₁, j₂, rfl, hj₁, hj₂⟩
  rcases write_t_as_2tu Fchar u with ⟨x, y, rfl⟩
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ hj₁ hj₂, expr_βψω_ψ_as_ψ_βψω Fchar, expr_βψω_βψ_as_βψ_βψω Fchar, expr_βψω_ψ_as_ψ_βψω Fchar,
  expr_βψω_βψ_as_βψ_βψω Fchar]
declare_B3Small_triv_expr_thm F βψω β2ψ

-- 8.54
theorem self_comm_of_βψω :
  mixed_commutes_of_root (weakB3Small F).pres_mk βψω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rcases decompose 1 2 j hj with ⟨j₁, j₂, rfl, hj₁, hj₂⟩
  rw [←mul_one t]
  grw [expr_βψω_as_β_ψω_β_ψω Fchar hi₁ hi₂, expr_βψω_β_as_β_βψω Fchar, ←expr_βψω_ψω_as_ψω_βψω Fchar,
  expr_βψω_ψω_as_ψω_βψω Fchar, expr_βψω_β_as_β_βψω Fchar]

-- 8.55
theorem lin_of_βψω : lin_of_root((weakB3Small F).pres_mk, βψω) := by
  intro i hi t u
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rw [←mul_one t, expr_βψω_as_β_ψω_β_ψω Fchar hi₁ hi₂]
  grw [←expr_βψω_ψω_as_ψω_βψω Fchar, ←expr_βψω_β_as_β_βψω Fchar, ←expr_βψω_ψω_as_ψω_βψω Fchar]
  rw [←mul_one u]
  grw [expr_βψω_as_β_ψω_β_ψω Fchar hi₁ hi₂]
  rw [←mul_one (t + u)]
  grw [expr_βψω_as_β_ψω_β_ψω Fchar hi₁ hi₂]
  ring_nf

theorem id_of_βψω :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ βψω.height), {βψω, i, 0} = 1 := by sorry

-- 8.56
theorem inv_of_βψω : inv_of_root((weakB3Small F).pres_mk, βψω) := by
  intro i hi t
  apply inv_eq_iff_mul_eq_one.2
  grw [lin_of_βψω Fchar, id_of_βψω Fchar hi]

-- 8.57
theorem expr_βψ_ω_as_ω_βψ_βψω :
  forall_ij_tu 2 1, {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψ, i, t} * {βψω, i + j, 2 * t * u} := by
  intro i j hi hj t u
  have : 2 * t * u = 2 * (-t) * (-u) := by ring
  rw [this, expand_βψω_as_commutator_of_βψ_ω Fchar hi hj, ←inv_of_βψ, ←inv_of_ω]
  group

theorem expr_βψ_ω_as_ω_βψω_βψ :
  forall_ij_tu 2 1, {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψω, i + j, 2 * t * u} * {βψ, i, t} := by
  intro i j hi hj t u
  grw [expr_βψ_ω_as_ω_βψ_βψω Fchar hi hj, expr_βψω_βψ_as_βψ_βψω Fchar]

-- 8.58
theorem trivial_comm_of_β2ψ_ω :
  trivial_commutator_of_root_pair (weakB3Small F).pres_mk β2ψ ω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rcases write_t_as_2tu Fchar t with ⟨x, t, rfl⟩
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ hi₁ hi₂, expr_βψ_ω_as_ω_βψ_βψω Fchar hi₂ hj, expr_ψ_ω_as_ω_ψω_ψ hi₁ hj, ←expr_ω_ψω_as_ψω_ω,
  expr_βψ_ω_as_ω_βψ_βψω Fchar hi₂ hj, expr_ψ_ω_as_ω_ψ_ψω hi₁ hj, expr_βψω_ψω_as_ψω_βψω Fchar, expr_βψω_ψ_as_ψ_βψω Fchar,
  expr_βψω_βψ_as_βψ_βψω Fchar, lin_of_βψω Fchar]
  field_simp
  grw [id_of_βψω Fchar (add_le_add hi₂ hj), expr_βψ_ψω_as_ψω_βψ]

end Steinberg.B3Small
