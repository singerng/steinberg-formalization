/-

LICENSE goes here.

-/

import Steinberg.B3Small.Basic

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

import Steinberg.Defs.Lattice
import Steinberg.Defs.Commutator
import Steinberg.Defs.ReflDeg

import Steinberg.Upstream.FreeGroup

namespace Steinberg.B3Small

open Steinberg B3SmallPosRoot GradedPartialChevalley GradedPartialChevalleyGroup GradedChevalleyGenerator ReflDeg

variable {F : Type TF} [Field F] (Fchar : (2 : F) ≠ 0)

/-! ### Double commutator theorem -/

theorem comm_of_β_ψ : double_commutator_of_root_pair (weakB3Small F).pres_mk β ψ βψ β2ψ 1 1 (by rfl) (by rfl) :=
  (weakB3Small F).double_commutator_helper β ψ βψ β2ψ 1 1 (by rfl) (by rfl)
    (by simp only [weakB3Small, trivial_commutator_pairs]; tauto)

/-! ### Nonhomogeneous lift -/
theorem nonhomog_lift_of_comm_of_βψ_ψω :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀}
    , {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} ⁆
    = 1 := by
  hom_tac rels_of_nonhomog_lift_of_comm_of_βψ_ψω [t₁, t₀, u₁, u₀, v₁, v₀]

/-! ### Definition of missing root -/
theorem def_of_βψω : forall_i_t βψω,
    ⁅ {β, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1
    , {ψω, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
      = {βψω, i, t} := by
  intro t i hi
  apply GradedPartialChevalleyGroup.helper
  apply (weakB3Small F).def_helper rels_of_def_of_βψω
  · simp only [weakB3Small, def_sets, Set.mem_singleton_iff]
  · exists t, i, hi

theorem refl_of_lifted :
  ∀ S ∈ lifted_sets F,
    ∀ r ∈ S, (weakB3Small F).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [lifted_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_βψ_ψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, rfl ⟩
  simp only [free_mk, map_commutatorElement, map_mul, FreeGroup.map.of, refl_deg_of_gen,
    PositiveRootSystem.height, height, tsub_self, Nat.add_one_sub_one, tsub_zero]
  repeat rw [← free_mk]
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
  ⟨refl_of_lifted, refl_of_def⟩

/-! ### 8.37 -/

theorem expr_βψ_as_ψ_β_ψ_β_ψ : forall_ij_tu β ψ,
    {βψ, i + j, 2 * t * u}
      = {ψ, j, -u} * {β, i, t} * {ψ, j, 2 * u} * {β, i, -t} * {ψ, j, -u} := by
  intro i j hi hj t u
  have hij : i + j ≤ βψ.height := by ht
  rw [← mul_inv_eq_iff_eq_mul]
  mar; rw [← inv_mul_eq_iff_eq_mul]; mal
  apply mul_right_cancel (b := {ψ, j, 2 * u}⁻¹)
  rw [← inv_of_β, ← commutatorElement_def]
  grw [comm_of_β_ψ, expr_βψ_β2ψ_as_β2ψ_βψ]
  rw [eq_of_hR_eq β2ψ (j + (i + j)) (by omega) (2 * u * (2 * t * u)) (by ring)]
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ hj hij]
  ring_nf
  chev_simp

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
    have hf_i : i ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have hf_j : j ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have hf_k : k ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have id₁ : {βψ, i + j, t} = {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    have id₂ : {ψω, j + k, u} = {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    rw [id₁, id₂, nonhomog_lift_of_comm_of_βψ_ψω]

private lemma image_of_homog_lift_of_comm_of_βψ_ψω {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ψω.height)
    : ((i, j) ∈ ij_jk_image) → ∀ (t u : F), ⁅ {βψ, i, t}, {ψω, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  simp [f_ij_jk] at this
  rcases this with ⟨ i', j', k', ⟨ hi', hj', hk' ⟩, rfl, rfl ⟩
  rw [← homog_lift_of_comm_of_βψ_ψω i' j' k' hi' hj' hk' t u]

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
    simp only [PositiveRootSystem.height] at *
    simp only [B3SmallPosRoot.height] at *
    simp -- should fix
    omega
  rcases this with ( ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hij )
  · rw [← comm_of_βψ_ψω_02 t u]
  · rw [← comm_of_βψ_ψω_20 t u]
  · apply image_of_homog_lift_of_comm_of_βψ_ψω hi hj hij

declare_B3Small_triv_expr_thm F βψ ψω

/-! ### Further useful identities (roughly GENERIC) -/

-- 8.39
theorem expr_ψ_ω_as_ω_ψ_ψω : forall_ij_tu ψ ω,
    {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψ, i, t} * {ψω, i + j, 2 * t * u} := by
  intro i j hi hj t u
  rw [comm_right]
  mul_inj
  rw [inv_of_ω, inv_of_ψ, comm_of_ψ_ω]
  ring_nf

theorem expr_ψ_ω_as_ω_ψω_ψ : forall_ij_tu ψ ω,
    {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψω, i + j, 2 * t * u} * {ψ, i, t} := by
  intro i j hi hj t u
  grw [expr_ψ_ω_as_ω_ψ_ψω hi hj, expr_ψ_ψω_as_ψω_ψ]

-- 8.40
theorem expr_β_ψ_as_ψ_β_β2ψ_βψ : forall_ij_tu β ψ,
    {β, i, t} * {ψ, j, u} = {ψ, j, u} * {β, i, t} * {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, t * u} := by
  intro i j hi hj t u
  have := comm_of_β_ψ hi hj (-t) (-u)
  chev_simp at this
  grw [← expr_βψ_β2ψ_as_β2ψ_βψ, ← mul_assoc, ← this]

-- 8.40 a

theorem expr_β_ψ_as_ψ_βψ_β2ψ_β : forall_ij_tu β ψ,
    {β, i, t} * {ψ, j, u} = {ψ, j, u} * {βψ, i + j, t * u} * {β2ψ, i + 2 * j, -(t * u^2)} * {β, i, t} := by
  intro i j hi hj t u
  grw [expr_β_ψ_as_ψ_β_β2ψ_βψ hi hj, ← expr_βψ_β2ψ_as_β2ψ_βψ,
        expr_β_βψ_as_βψ_β, expr_β_β2ψ_as_β2ψ_β]

-- 8.41
theorem expr_ψ_β_as_βψ_β2ψ_β_ψ : forall_ij_tu β ψ,
    {ψ, j, u} * {β, i, t} = {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, -t * u^2} * {β, i, t} * {ψ, j, u} := by
  intro i j hi hj t u
  apply reorder_left_of_eq_comm
  rw [← commutatorElement_inv, comm_of_β_ψ hi hj, expr_βψ_β2ψ_as_β2ψ_βψ,
    neg_mul, ←inv_of_βψ, neg_mul, ←inv_of_β2ψ]
  group

/-! ### Establishing βψω -/

include Fchar

private lemma write_t_as_2tu (t : F) : ∃ (x y : F), t = 2 * x * y := ⟨1/2, t, by field_simp⟩

-- 8.43
theorem comm_of_β2ψ_ψω :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk β2ψ ψω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases write_t_as_2tu Fchar t with ⟨x, y, rfl⟩
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ hi₁ hi₂, expr_βψ_ψω_as_ψω_βψ,
    expr_ψ_ψω_as_ψω_ψ, expr_βψ_ψω_as_ψω_βψ, expr_ψ_ψω_as_ψω_ψ]

declare_B3Small_triv_expr_thm F β2ψ ψω

-- 8.44
theorem Interchange : forall_ijk_tuv β ψ ω,
    ⁅ {βψ, i + j, t * u}, {ω, k, v} ⁆ = ⁅ {β, i , t}, {ψω, j + k, 2 * u * v} ⁆ := by
  intro i j k hi hj hk t u v
  apply eq_comm_of_reorder_left
  have write_tu : t * u = 2 * t * (u / 2) := by ring_nf; field_simp
  have : 2 * 2 * u * v / 2 = 2 * u * v := by field_simp; ring
  have write_βψ : {βψ, i + j, t * u} * {ω, k, v} = {ω, k, v} * {ψω, j + k, -u * v} * {ψ, j, -u/2} * {β, i, t}
      * {ψ, j, u} * {ψω, j + k, 2 * u * v} * {β, i, -t} * {ψ, j, -u/2} *
      {ψω, j + k, -u * v} := by
    -- express βψ as ψ and β elements
    rw [write_tu, expr_βψ_as_ψ_β_ψ_β_ψ hi hj]
    -- move ω all the way to the left
    grw [expr_ψ_ω_as_ω_ψ_ψω, expr_β_ω_as_ω_β, expr_ψ_ω_as_ω_ψ_ψω, expr_β_ω_as_ω_β, expr_ψ_ω_as_ω_ψω_ψ]
    field_simp; rw [this]
  -- cyclically combine the left ψω with the right ψω
  rw [expr_ω_ψω_as_ψω_ω] at write_βψ
  have write_βψ_left := (mul_right_inj ({ψω, j + k, -u * v}'(add_le_add hj hk))⁻¹).2 write_βψ
  rw [neg_mul, inv_of_ψω, neg_neg, ←mul_assoc, ←expr_βψ_ψω_as_ψω_βψ, mul_assoc, ←expr_ω_ψω_as_ψω_ω] at write_βψ_left
  have write_βψ_right := (mul_left_inj ({ψω, j + k, u * v}'(add_le_add hj hk))⁻¹).2 write_βψ_left
  grw [rfl] at write_βψ_right
  -- move ψ elements together across β elements
  grw [write_βψ_right, expr_ψ_β_as_βψ_β2ψ_β_ψ, expr_β_ψ_as_ψ_β_β2ψ_βψ]
  -- commute ψ elements together across ψω elements and cancel them
  grw [expr_ψ_ψω_as_ψω_ψ]
  have : -(u / 2) + u + -(u / 2) = 0 := by ring_nf; field_simp
  rw [this, id_of_ψ]
  -- move β2ψ elements together and cancel them
  grw [expr_β_β2ψ_as_β2ψ_β, ←expr_β2ψ_ψω_as_ψω_β2ψ Fchar, expr_β_β2ψ_as_β2ψ_β]
  -- collect βψ elements on the right
  grw [expr_βψ_ψω_as_ψω_βψ, ← expr_β_βψ_as_βψ_β,
        expr_βψ_ψω_as_ψω_βψ, ← expr_β_βψ_as_βψ_β,
        expr_βψ_ψω_as_ψω_βψ]
  -- bring ω as far right as possible
  grw [commutatorElement_def, ← expr_β_ω_as_ω_β,
        expr_ω_ψω_as_ψω_ω, ← expr_β_ω_as_ω_β, expr_ω_ψω_as_ψω_ω]
  ring_nf
  field_simp

private lemma βt_ψω2u_to_βψt_ωu : forall_ijk_tu β ψ ω,
    ⁅ {β, i, t}, {ψω, j + k, 2 * u} ⁆ = ⁅{βψ, i + j, t}, {ω, k, u} ⁆ := by
  intro i j k hi hj hk t u
  have := Interchange Fchar hi hj hk t 1 u
  field_simp at this
  exact this.symm

private lemma βtu_ψω1_to_βt_ψωu : forall_ijk_tu β ψ ω,
    ⁅ {β, i, t * u}, {ψω, j + k, 1} ⁆ = ⁅ {β, i, t}, {ψω, j + k, u} ⁆ := by
  intro i j k hi hj hk t u
  have aux₁ := Interchange Fchar hi hj hk (t * u) 1 (1 / 2)
  have aux₂ := Interchange Fchar hi hj hk t u (1 / 2)
  field_simp at aux₁
  field_simp at aux₂
  rwa [aux₁] at aux₂

omit Fchar in
private lemma rewrite_2tu (t u : F) : 2 * t * u = t * (2 * u) := by ring
private lemma rewrite_tu (t u : F) : t * u = 2 * t * (u / 2) := by ring_nf; field_simp

-- height 0
private lemma expr_βψω_as_comm_of_β_ψω_00 :
  ∀ t u : F, {βψω, 0, t * u} = ⁅{β, 0, t}, {ψω, 0, u}⁆ := by
  intro t u
  have := @def_of_βψω _ _ 0 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, @βtu_ψω1_to_βt_ψωu _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_βψω_as_comm_of_βψ_ω_00 :
  ∀ t u : F, {βψω, 0, 2 * t * u} = ⁅{βψ, 0, t}, {ω, 0, u}⁆ := by
  intro t u
  rw [rewrite_2tu, expr_βψω_as_comm_of_β_ψω_00 Fchar,
    @βt_ψω2u_to_βψt_ωu _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial)]

-- height 1
private lemma expr_βψω_as_comm_of_β_ψω_01 :
    ∀ (t u : F), {βψω, 1, t * u} = ⁅{β, 0, t}, {ψω, 1, u}⁆ := by
  intro t u
  have := @def_of_βψω _ _ 1 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, @βtu_ψω1_to_βt_ψωu _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_βψω_as_comm_of_βψ_ω_01 :
    ∀ (t u : F), {βψω, 1, 2 * t * u} = ⁅{βψ, 0, t}, {ω, 1, u}⁆ := by
  intro t u
  rw [rewrite_2tu, expr_βψω_as_comm_of_β_ψω_01 Fchar,
    @βt_ψω2u_to_βψt_ωu _ _ Fchar 0 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expr_βψω_as_comm_of_βψ_ω_10 :
    ∀ (t u : F), {βψω, 1, 2 * t * u} = ⁅{βψ, 1, t}, {ω, 0, u}⁆ := by
  intro t u
  rw [rewrite_2tu, expr_βψω_as_comm_of_β_ψω_01 Fchar,
    @βt_ψω2u_to_βψt_ωu _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expr_βψω_as_comm_of_β_ψω_10 :
    ∀ (t u : F), {βψω, 1, t * u} = ⁅{β, 1, t}, {ψω, 0, u}⁆ := by
  intro t u
  rw [rewrite_tu Fchar, expr_βψω_as_comm_of_βψ_ω_10 Fchar,
    ← @βt_ψω2u_to_βψt_ωu _ _ Fchar 1 0 0 (by trivial) (by trivial) (by trivial)]
  field_simp

-- height 2 (reflection of height 1)
declare_B3Small_reflected_thm F b3small_valid βψω β ψω const 1 heights 2 1 1 to 1 0 1
declare_B3Small_reflected_thm F b3small_valid βψω β ψω const 1 heights 2 0 2 to 1 1 0
declare_B3Small_reflected_thm F b3small_valid βψω βψ ω const 2 heights 2 2 0 to 1 0 1
declare_B3Small_reflected_thm F b3small_valid βψω βψ ω const 2 heights 2 1 1 to 1 1 0
declare_B3Small_reflected_thm F b3small_valid βψω β ψω const 1 heights 3 1 2 to 0 0 0
declare_B3Small_reflected_thm F b3small_valid βψω βψ ω const 2 heights 3 2 1 to 0 0 0

-- 8.45a
theorem expand_βψω_as_commutator_of_βψ_ω :
  forall_ij_tu 2 1, {βψω, i + j, 2 * t * u} = ⁅{βψ, i, t}, {ω, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_βψω_as_comm_of_βψ_ω_00 Fchar]
  | 0, 1 => rw [expr_βψω_as_comm_of_βψ_ω_01 Fchar]
  | 1, 0 => rw [expr_βψω_as_comm_of_βψ_ω_10 Fchar]
  | 1, 1 => rw [expr_βψω_as_comm_of_βψ_ω_11 Fchar]
  | 2, 0 => rw [expr_βψω_as_comm_of_βψ_ω_20 Fchar]
  | 2, 1 => rw [expr_βψω_as_comm_of_βψ_ω_21 Fchar]

-- 8.45b
theorem expand_βψω_as_commutator_of_β_ψω :
  forall_ij_tu 1 2, {βψω, i + j, t * u} = ⁅{β, i, t}, {ψω, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expr_βψω_as_comm_of_β_ψω_00 Fchar]
  | 0, 1 => rw [expr_βψω_as_comm_of_β_ψω_01 Fchar]
  | 0, 2 => rw [expr_βψω_as_comm_of_β_ψω_02 Fchar]
  | 1, 0 => rw [expr_βψω_as_comm_of_β_ψω_10 Fchar]
  | 1, 1 => rw [expr_βψω_as_comm_of_β_ψω_11 Fchar]
  | 1, 2 => rw [expr_βψω_as_comm_of_β_ψω_12 Fchar]

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
  grw [←expr_ψ_ψω_as_ψω_ψ, expr_β_ψ_as_ψ_β_β2ψ_βψ hi₁ hj,
    ← expr_ψ_ψω_as_ψω_ψ, expr_β_ψ_as_ψ_β_β2ψ_βψ hi₁ hj,
    ← expr_βψ_β2ψ_as_β2ψ_βψ, expr_β2ψ_ψω_as_ψω_β2ψ Fchar,
    expr_β_β2ψ_as_β2ψ_β,
    expr_βψ_ψω_as_ψω_βψ, expr_β_βψ_as_βψ_β]
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
  grw [expr_βψ_as_ψ_β_ψ_β_ψ hj₁ hj₂, expr_βψω_ψ_as_ψ_βψω Fchar,
    expr_βψω_β_as_β_βψω Fchar, expr_βψω_ψ_as_ψ_βψω Fchar,
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
theorem comm_of_βψω :
    mixed_commutes_of_root (weakB3Small F).pres_mk βψω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rcases decompose 1 2 j hj with ⟨j₁, j₂, rfl, hj₁, hj₂⟩
  rw [←mul_one t]
  grw [expr_βψω_as_β_ψω_β_ψω Fchar hi₁ hi₂, expr_βψω_β_as_β_βψω Fchar, ←expr_βψω_ψω_as_ψω_βψω Fchar,
  expr_βψω_ψω_as_ψω_βψω Fchar, expr_βψω_β_as_β_βψω Fchar]
declare_B3Small_mixed_expr_thm F βψω

-- 8.55
@[simp, chev_simps]
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

theorem id_of_βψω : ∀ ⦃i : ℕ⦄ (hi : i ≤ βψω.height), {βψω, i, 0} = 1 :=
  fun i hi ↦ mul_right_eq_self.mp (by rw [lin_of_βψω Fchar hi 0 0, zero_add])

-- 8.56
@[simp, chev_simps]
theorem inv_of_βψω : inv_of_root((weakB3Small F).pres_mk, βψω) := by
  intro i hi t
  apply inv_eq_iff_mul_eq_one.2
  grw [lin_of_βψω Fchar, id_of_βψω Fchar hi]

-- 8.57
theorem expr_βψ_ω_as_ω_βψ_βψω : forall_ij_tu βψ ω,
    {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψ, i, t} * {βψω, i + j, 2 * t * u} := by
  intro i j hi hj t u
  have : 2 * t * u = 2 * (-t) * (-u) := by ring
  rw [this, expand_βψω_as_commutator_of_βψ_ω Fchar hi hj, ←inv_of_βψ, ←inv_of_ω]
  group

theorem expr_βψ_ω_as_ω_βψω_βψ : forall_ij_tu βψ ω,
    {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψω, i + j, 2 * t * u} * {βψ, i, t} := by
  intro i j hi hj t u
  grw [expr_βψ_ω_as_ω_βψ_βψω Fchar hi hj, expr_βψω_βψ_as_βψ_βψω Fchar]

-- 8.58
theorem comm_of_β2ψ_ω :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk β2ψ ω := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.2
  rcases decompose 1 2 i hi with ⟨i₁, i₂, rfl, hi₁, hi₂⟩
  rcases write_t_as_2tu Fchar t with ⟨x, t, rfl⟩
  grw [expr_β2ψ_as_ψ_βψ_ψ_βψ hi₁ hi₂, expr_βψ_ω_as_ω_βψ_βψω Fchar hi₂ hj,
        expr_ψ_ω_as_ω_ψω_ψ hi₁ hj, ← expr_ω_ψω_as_ψω_ω,
        expr_βψ_ω_as_ω_βψ_βψω Fchar hi₂ hj, expr_ψ_ω_as_ω_ψ_ψω hi₁ hj,
        expr_βψω_ψω_as_ψω_βψω Fchar, expr_βψω_ψ_as_ψ_βψω Fchar,
        expr_βψω_βψ_as_βψ_βψω Fchar, lin_of_βψω Fchar,
        id_of_βψω Fchar (add_le_add hi₂ hj), expr_βψ_ψω_as_ψω_βψ]
declare_B3Small_triv_expr_thm F β2ψ ω

theorem full_rels_satisfied_in_weak_group :
  ∀ r ∈ (fullB3Small F).all_rels, (weakB3Small F).pres_mk r = 1 := by
  simp only [fullB3Small, weakB3Small]
  apply GradedPartialChevalleyGroup.graded_injection
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
      rcases h_r with ⟨ i, j, hi, hj, t, u, goal ⟩
      rcases h_new with h_βψ_ψω|h_β_βψω|h_ψ_βψω|h_ω_βψω|h_βψ_βψω|h_β2ψ_βψω|h_ψω_βψω|h_ω_β2ψ
      all_goals (
        subst p r
        simp only
      )
      · exact comm_of_βψ_ψω hi hj t u
      · exact comm_of_βψω_β Fchar hi hj t u
      · exact comm_of_βψω_ψ Fchar hi hj t u
      · exact comm_of_βψω_ω Fchar hi hj t u
      · exact comm_of_βψω_βψ Fchar hi hj t u
      · exact comm_of_βψω_β2ψ Fchar hi hj t u
      · exact comm_of_βψω_ψω Fchar hi hj t u
      · apply triv_comm_symm.1
        exact comm_of_β2ψ_ω Fchar hj hi u t
  · rcases h with h_old|h_new
    · tauto
    · right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_new
      intro r h_r
      simp only [rels_of_single_commutator_of_root_pair] at h_r
      rcases h_r with ⟨ i, j, hi, hj, t, u, goal ⟩
      rcases h_new with h_β_ψω|h_βψ_ω
      all_goals (
        subst p r
        simp only [map_mul, map_inv, mul_inv_eq_one]
      )
      · have : t * u = 1 * t * u := by ring_nf
        rw [← this]
        exact (expand_βψω_as_commutator_of_β_ψω Fchar hi hj t u).symm
      · exact (expand_βψω_as_commutator_of_βψ_ω Fchar hi hj t u).symm
  · tauto
  · rcases h with h_old|h_new
    · tauto
    · right
      simp_all only [Set.mem_singleton_iff]
      intro r h_r
      simp only [rels_of_mixed_commutes_of_root] at h_r
      rcases h_r with ⟨ i, j, hi, hj, t, u, goal ⟩
      subst r
      exact comm_of_βψω Fchar hi hj t u
  · rcases h with h_old|h_new
    · tauto
    · right
      simp_all only [Set.mem_singleton_iff]
      intro r h_r
      simp only [rels_of_lin_of_root] at h_r
      rcases h_r with ⟨ i, hi, t, u, goal ⟩
      subst r
      simp only [map_mul, map_inv, mul_inv_eq_one]
      exact lin_of_βψω Fchar hi t u
  · tauto
  · tauto

end Steinberg.B3Small
