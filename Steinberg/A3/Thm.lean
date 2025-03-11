/-

LICENSE goes here.

-/

import Steinberg.A3.Basic

import Mathlib.Algebra.Group.Basic

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

import Steinberg.Defs.Lattice
import Steinberg.Defs.ReflDeg

import Steinberg.Upstream.FreeGroup

/-!

  File dox.

-/

namespace Steinberg.A3

open Steinberg A3PosRoot GradedChevalleyGenerator ReflDeg

variable {R : Type TR} [Ring R]

/-! ### Nonhomogeneous lift -/

theorem nonhomog_lift_of_comm_of_αβ_βγ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R),
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}
    , {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} ⁆
    = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply PartialChevalley.helper
  apply (weakA3 R).lifted_helper rels_of_nonhomog_lift_of_comm_of_αβ_βγ
  · simp only [weakA3, lifted_sets, Set.mem_singleton_iff]
  · exists t₁, t₀, u₁, u₀, v₁, v₀

/-! ### Definition of missing root -/
theorem def_of_αβγ :
  forall_i_t αβγ,
    ⁅ {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1
    , {βγ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
    = {αβγ, i, t} := by
  intro t i hi
  apply PartialChevalley.helper
  apply (weakA3 R).def_helper rels_of_def_of_αβγ
  · simp only [weakA3, def_sets, Set.mem_singleton_iff]
  · exists t, i, hi

theorem refl_of_lifted :
  ∀ S ∈ lifted_sets R,
    ∀ r ∈ S, (weakA3 R).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [lifted_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_αβ_βγ, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, rfl ⟩
  simp only [map_mul, map_commutatorElement, free_mk, FreeGroup.map.of, refl_deg_of_gen, PosRootSys.height, height]
  simp_arith
  repeat rw [← free_mk]
  rw [add_comm (t₁ * u₀), add_comm (u₁ * v₀)]
  grw [expr_αβ_αβ_as_αβ_αβ, expr_αβ_αβ_as_αβ_αβ (i := 0), expr_αβ_αβ_as_αβ_αβ,
       expr_βγ_βγ_as_βγ_βγ, expr_βγ_βγ_as_βγ_βγ (i := 0), expr_βγ_βγ_as_βγ_βγ]
  exact nonhomog_lift_of_comm_of_αβ_βγ t₀ t₁ u₀ u₁ v₀ v₁

-- def relations are preserved under reflection
theorem refl_of_def : ∀ S ∈ def_sets R, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  simp only [def_sets, Set.mem_singleton_iff, forall_eq, rels_of_def_of_αβγ, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ i, hi, t, rfl ⟩
  simp only [map_mul, map_commutatorElement, split_3_into_1_2]
  exists (αβγ.height - i), (by omega), t
  split
  all_goals (simp only; congr)

theorem a3_valid : ReflDeg.refl_valid (R := R) (weakA3 R) :=
  ⟨refl_of_lifted, refl_of_def⟩

/-! ### Derive full commutator for αβ and βγ from nonhomogeneous lift -/

-- NS: this section should probably be abstracted for reuse

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) (via the previous theorem). -/
private lemma homog_lift_of_comm_of_αβ_βγ (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : R), ⁅ { αβ, i + j, t}, {βγ, j + k, u} ⁆ = 1 := by
    intro t u
    let t₁ : R := match i with
      | 1 => t
      | 0 => 0
    let t₀ : R := match i with
      | 1 => 0
      | 0 => t
    let u₁ : R := match j with
      | 1 => 1
      | 0 => 0
    let u₀ : R := match j with
      | 1 => 0
      | 0 => 1
    let v₁ : R := match k with
      | 1 => u
      | 0 => 0
    let v₀ : R := match k with
      | 1 => 0
      | 0 => u
    have hf_i : i ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have hf_j : j ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have hf_k : k ∈ [0,1] := by simp only [List.mem_cons, List.mem_singleton]; omega
    have id₁ : {αβ, i + j, t} = {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    have id₂ : {βγ, j + k, u} = {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    rw [id₁, id₂, nonhomog_lift_of_comm_of_αβ_βγ]

private lemma image_of_homog_lift_of_comm_of_αβ_βγ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ βγ.height)
    : ((i, j) ∈ ij_jk_image) → ∀ (t u : R), ⁅ {αβ, i, t}, {βγ, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  simp [f_ij_jk] at this
  rcases this with ⟨ i', j', k', ⟨ hi', hj', hk' ⟩, rfl, rfl ⟩
  rw [← homog_lift_of_comm_of_αβ_βγ i' j' k' hi' hj' hk' t u]

private lemma comm_of_αβ_βγ_20 : ∀ (t u : R), ⁅ {αβ, 2, t}, {βγ, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {βγ, 1, u} _ ({αβ, 1, t + 1} * {αβ, 0, 1})
  grw [← nonhomog_lift_of_comm_of_αβ_βγ t 1 1 1 0 u]
  rw [← homog_lift_of_comm_of_αβ_βγ 1 1 0 (by trivial) (by trivial) (by trivial) t u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_αβ_βγ 0 1 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_αβ_βγ 0 0 1 (by trivial) (by trivial) (by trivial) 1 u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_αβ_βγ 1 0 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_αβ_βγ 0 0 0 (by trivial) (by trivial) (by trivial) 1 u]

-- symmetric to proof of `comm_of_αβ_βγ_20`
private lemma comm_of_αβ_βγ_02 : ∀ (t u : R), ⁅ {αβ, 0, t}, {βγ, 2, u} ⁆ = 1 := by
  intro t u
  have : ⁅ {αβ, 0, t}, {βγ, 2, u} ⁆ = ReflDeg.refl_symm a3_valid ⁅ {αβ, 2, t}, {βγ, 0, u} ⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, comm_of_αβ_βγ_20, map_one]

theorem comm_of_αβ_βγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk αβ βγ := by
  intro i j hi hj t u
  by_cases hij : (i, j) ∈ ij_jk_image
  · apply image_of_homog_lift_of_comm_of_αβ_βγ hi hj hij
  · have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
      simp [ij_jk_image] at hij
      height_simp at hi hj
      omega
    rcases this with ( ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
    · rw [← comm_of_αβ_βγ_02 t u]
    · rw [← comm_of_αβ_βγ_20 t u]

declare_A3_triv_expr_thm R αβ βγ

/-! ### Further useful identities (roughly GENERIC) -/

/- Rewrite β⬝γ as γ⬝βγ⬝β. -/
@[group_reassoc]
theorem expr_β_γ_as_γ_βγ_β :
  forall_ij_tu β γ,
    reorder_mid({β, i, t}, {γ, j, u}, {βγ, i + j, t * u}) := by
  intro i j hi hj t u
  have := comm_of_β_γ hi hj t u
  rw [one_mul] at this
  rw [← this, comm_mid, inv_of_γ, comm_of_β_γ]
  grw [comm_of_β_γ]

/-! ### Interchange theorems between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms -/

/- Interchange between ⁅α, βγ⁆ and ⁅αβ, γ⁆, "trading" a single degree j : Deg 1 and scalar u : R. -/
theorem Interchange : forall_ijk_tuv α β γ,
     ⁅ {α, i, t}, {βγ, j + k, u * v} ⁆ = ⁅ {αβ, i + j, t * u}, {γ, k, v} ⁆ := by
  intro i j k hi hj hk t u v
  apply eq_comm_of_reorder_left
  have hij : i + j ≤ αβ.height := by ht
  have hjk : j + k ≤ βγ.height := by ht
  grw [expr_βγ_as_β_γ_β_γ hj hk,
    expr_α_β_as_αβ_β_α hi hj, expr_α_γ_as_γ_α hi hk,
    expr_α_β_as_αβ_β_α hi hj, expr_α_γ_as_γ_α hi hk,
    expr_β_γ_as_βγ_γ_β hj hk,
    expr_β_αβ_as_αβ_β hj hij,
    ← expr_γ_βγ_as_βγ_γ hk hjk,
    ← expr_αβ_βγ_as_βγ_αβ hij hjk,
    commutatorElement_def,
    expr_β_γ_as_βγ_γ_β hj hk,
    ← expr_γ_βγ_as_βγ_γ hk hjk]

/- Pass between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms (specializes `Interchange` to the case `u=1`). -/
theorem InterchangeTrans : forall_ijk_tu α β γ,
    ⁅ {α, i, t}, {βγ, j + k, u} ⁆ = ⁅ {αβ, i + j, t}, {γ, k, u} ⁆ := by
  intro i j k hi hj hk t u
  have := Interchange hi hj hk t 1 u
  rwa [one_mul, mul_one] at this

/- ⁅α,βγ⁆ forms depend only on product of coefficients. Applies `Interchange` twice. -/
theorem InterchangeRefl : forall_ijk_tu α β γ,
    ⁅ {α, i, t * u}, {βγ, j + k, 1} ⁆ = ⁅ {α, i, t}, {βγ, j + k, u} ⁆ := by
  intro i j k hi hj hk t u
  nth_rewrite 2 [← mul_one u]
  rw [Interchange hi hj hk, InterchangeTrans hi hj hk]

/-! ### Commutator relations for (α,βγ) and (αβ,γ) via interchange relations -/

-- NS: Really need to figure out a more sane way to write this section.

-- height 0
private lemma comm_of_α_βγ_00 (t u : R) :
    ⁅ {α, 0, t}, {βγ, 0, u} ⁆ = {αβγ, 0, t * u} := by
  rw [← @InterchangeRefl _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
  rw [← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_00 (t u : R) :
    ⁅ {αβ, 0, t}, {γ, 0, u} ⁆ = {αβγ, 0, t * u} := by
  rw [← @InterchangeTrans _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
  rw [comm_of_α_βγ_00]

-- height 1
private lemma comm_of_α_βγ_01 (t u : R) :
    ⁅ {α, 0, t}, {βγ, 1, u} ⁆ = {αβγ, 1, t * u} := by
  rw [← @InterchangeRefl _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]
  rw [← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_10 (t u : R) : ⁅ {αβ, 1, t}, {γ, 0, u} ⁆ = {αβγ, 1, t * u} := by
  rw [← @InterchangeTrans _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]
  simp only [add_zero, comm_of_α_βγ_01, zero_add, one_mul]

private lemma comm_of_α_βγ_10 (t u : R) : ⁅ {α, 1, t}, {βγ, 0, u} ⁆ = {αβγ, 1, t * u} := by
  rw [@InterchangeTrans _ _ 1 0 0 (by trivial) (by trivial) (by trivial),
        comm_of_αβ_γ_10]

private lemma comm_of_αβ_γ_01 (t u : R) : ⁅ {αβ, 0, t}, {γ, 1, u} ⁆ = {αβγ, 1, t * u} := by
  rw [← @InterchangeTrans _ _ 0 0 1 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_01]

-- height 2
private lemma comm_of_α_βγ_11 (t u : R) : ⁅ {α, 1, t}, {βγ, 1, u} ⁆ = {αβγ, 2, t * u} := by
  rw [← @InterchangeRefl _ _ 1 0 1 (by trivial) (by trivial) (by trivial),
        ← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_11 (t u : R) : ⁅ {αβ, 1, t}, {γ, 1, u} ⁆ = {αβγ, 2, t * u} := by
  rw [← @InterchangeTrans _ _ 1 0 1 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_11]

private lemma comm_of_α_βγ_02 (t u : R) : ⁅ {α, 0, t}, {βγ, 2, u} ⁆ = {αβγ, 2, t * u} := by
  rw [@InterchangeTrans _ _ 0 1 1 (by trivial) (by trivial) (by trivial),
        comm_of_αβ_γ_11]

private lemma comm_of_αβ_γ_20 (t u : R) : ⁅ {αβ, 2, t}, {γ, 0, u} ⁆ = {αβγ, 2, t * u} := by
  rw [← @InterchangeTrans _ _ 1 1 0 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_11]

-- height 3
private lemma comm_of_α_βγ_12 (t u : R) : ⁅ {α, 1, t}, {βγ, 2, u} ⁆ = {αβγ, 3, t * u} := by
  rw [← @InterchangeRefl _ _ 1 1 1 (by trivial) (by trivial) (by trivial),
        ← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_21 (t u : R) : ⁅ {αβ, 2, t}, {γ, 1, u} ⁆ = {αβγ, 3, t * u} := by
  rw [← @InterchangeTrans _ _ 1 1 1 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_12]

/- Commutator relation for α and βγ. -/
theorem comm_of_α_βγ : single_commutator_of_root_pair (weakA3 R).pres_mk α βγ αβγ 1 (by ht) := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => simp only [comm_of_α_βγ_00 t u, add_zero, one_mul]
  | 0, 1 => simp only [comm_of_α_βγ_01 t u, zero_add, one_mul]
  | 0, 2 => simp only [comm_of_α_βγ_02 t u, zero_add, one_mul]
  | 1, 0 => simp only [comm_of_α_βγ_10 t u, add_zero, one_mul]
  | 1, 1 => simp only [comm_of_α_βγ_11 t u, Nat.reduceAdd, one_mul]
  | 1, 2 => simp only [comm_of_α_βγ_12 t u, Nat.reduceAdd, one_mul]

/- Commutator relation for αβ and γ. -/
theorem comm_of_αβ_γ : single_commutator_of_root_pair (weakA3 R).pres_mk αβ γ αβγ 1 (by ht) := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => simp only [comm_of_αβ_γ_00 t u, add_zero, one_mul]
  | 1, 0 => simp only [comm_of_αβ_γ_10 t u, add_zero, one_mul]
  | 2, 0 => simp only [comm_of_αβ_γ_20 t u, add_zero, one_mul]
  | 0, 1 => simp only [comm_of_αβ_γ_01 t u, zero_add, one_mul]
  | 1, 1 => simp only [comm_of_αβ_γ_11 t u, Nat.reduceAdd, one_mul]
  | 2, 1 => simp only [comm_of_αβ_γ_21 t u, Nat.reduceAdd, one_mul]

declare_A3_single_expr_thms R α βγ αβγ
declare_A3_single_expr_thms R αβ γ αβγ

/-! ### More rewriting theorems -/

theorem expr_αβγ_as_α_βγ_α_βγ_one_mul : forall_ij_t α βγ,
    {αβγ, i + j, t} = {α, i, 1} * {βγ, j, t} * {α, i, -1} * {βγ, j, -t} := by
  intro i j hi hj u
  have := expr_αβγ_as_α_βγ_α_βγ hi hj 1 u
  rwa [one_mul] at this

theorem expr_αβγ_as_α_βγ_α_βγ_mul_one : forall_ij_t α βγ,
    {αβγ, i + j, t} = {α, i, t} * {βγ, j, 1} * {α, i, -t} * {βγ, j, -1} := by
  intro i j hi hj t
  have := expr_αβγ_as_α_βγ_α_βγ hi hj t 1
  rwa [mul_one] at this

theorem expr_αβγ_as_αβ_γ_αβ_γ_one_mul : forall_ij_t αβ γ,
    {αβγ, i + j, t} = {αβ, i, 1} * {γ, j, t} * {αβ, i, -1} * {γ, j, -t} := by
  intro i j hi hj u
  have := expr_αβγ_as_αβ_γ_αβ_γ hi hj 1 u
  rwa [one_mul] at this

theorem expand_αβγ_as_αβ_γ_αβ_γ_mul_one : forall_ij_t αβ γ,
    {αβγ, i + j, t} = {αβ, i, t} * {γ, j, 1} * {αβ, i, -t} * {γ, j, -1} := by
  intro i j hi hj t
  have := expr_αβγ_as_αβ_γ_αβ_γ hi hj t 1
  rwa [mul_one] at this

/-! ### Commutators of αβγ with other roots -/

/- α and αβγ commute. -/
theorem comm_of_α_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk α αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height γ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul hj₁ hj₂,
      expr_α_αβ_as_αβ_α hi hj₁, expr_α_γ_as_γ_α hi hj₂,
      expr_α_αβ_as_αβ_α hi hj₁, expr_α_γ_as_γ_α hi hj₂]

/- β and αβγ commute. -/
-- the only commutator proof where we have to do something 'interesting'
theorem comm_of_β_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk β αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height γ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul hj₁ hj₂,
      expr_β_αβ_as_αβ_β hi hj₁, expr_β_γ_as_γ_βγ_β hi hj₂,
      expr_β_αβ_as_αβ_β hi hj₁, expr_β_γ_as_βγ_γ_β hi hj₂,
      ← expr_αβ_βγ_as_βγ_αβ hj₁]

/- γ and αβγ commute. -/
theorem comm_of_γ_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk γ αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose α.height βγ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expr_αβγ_as_α_βγ_α_βγ_one_mul hj₁ hj₂,
    ← expr_α_γ_as_γ_α hj₁ hi, expr_γ_βγ_as_βγ_γ hi hj₂,
    ← expr_α_γ_as_γ_α hj₁ hi, expr_γ_βγ_as_βγ_γ hi hj₂]

/- αβ and αβγ commute. -/
theorem comm_of_αβ_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk αβ αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose α.height βγ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expr_αβγ_as_α_βγ_α_βγ_one_mul hj₁ hj₂,
    ← expr_α_αβ_as_αβ_α hj₁ hi, expr_αβ_βγ_as_βγ_αβ hi hj₂,
    ← expr_α_αβ_as_αβ_α hj₁ hi, expr_αβ_βγ_as_βγ_αβ hi hj₂]

/- βγ and αβγ commute. -/
theorem comm_of_βγ_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk βγ αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height γ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expr_αβγ_as_αβ_γ_αβ_γ_one_mul hj₁ hj₂,
    ← expr_αβ_βγ_as_βγ_αβ hj₁ hi, ← expr_γ_βγ_as_βγ_γ hj₂ hi,
    ← expr_αβ_βγ_as_βγ_αβ hj₁ hi, ← expr_γ_βγ_as_βγ_γ hj₂ hi]

declare_A3_triv_expr_thm R α αβγ
declare_A3_triv_expr_thm R β αβγ
declare_A3_triv_expr_thm R γ αβγ
declare_A3_triv_expr_thm R αβ αβγ
declare_A3_triv_expr_thm R βγ αβγ

/- αβγ commutes with itself. -/
theorem comm_of_αβγ_αβγ : mixed_commutes_of_root (weakA3 R).pres_mk αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose α.height βγ.height j (by trivial) with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expr_αβγ_as_α_βγ_α_βγ_one_mul hj₁ hj₂,
    ← expr_α_αβγ_as_αβγ_α hj₁ hi, ← expr_βγ_αβγ_as_αβγ_βγ hj₂ hi,
    ← expr_α_αβγ_as_αβγ_α hj₁ hi, ← expr_βγ_αβγ_as_αβγ_βγ hj₂ hi]

declare_A3_triv_expr_thm R αβγ αβγ

/- Linearity for αβγ. -/
@[group_reassoc (attr := simp, chev_simps)]
theorem lin_of_αβγ : lin_of_root((weakA3 R).pres_mk, αβγ) := by
  intro i hi t u
  rcases decompose α.height βγ.height i (by trivial) with ⟨ i₁, i₂, ⟨ rfl, hi₁, hi₂ ⟩ ⟩
  have h_eq' : i₁ + i₂ ≤ PosRootSys.height αβγ := by omega
  grw [expr_αβγ_as_α_βγ_α_βγ_mul_one hi₁ hi₂,
    expr_βγ_αβγ_as_αβγ_βγ hi₂ h_eq',
    expr_α_αβγ_as_αβγ_α hi₁ h_eq',
    expr_βγ_αβγ_as_αβγ_βγ hi₂ h_eq',
    expr_αβγ_as_α_βγ_α_βγ_mul_one hi₁ hi₂,
    ← neg_add, add_comm u t,
    ← expr_αβγ_as_α_βγ_α_βγ hi₁ hi₂]

theorem full_rels_satisfied_in_weak_group :
  ∀ r ∈ (fullA3 R).all_rels, (weakA3 R).pres_mk r = 1 := by
  simp only [fullA3, weakA3]
  apply PartialChevalley.graded_injection
  · intro p h
    simp only [full_trivial_commutator_pairs] at h
    rcases h with h_old|h_new
    · tauto
    · right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_new
      intro r h_r
      simp only [rels_of_trivial_commutator_of_root_pair] at h_r
      rcases h_r with ⟨ i, j, hi, hj, t, u, goal ⟩
      rcases h_new with h_αβ_βγ|h_α_αβγ|h_β_αβγ|h_γ_αβγ|h_αβ_αβγ|h_βγ_αβγ
      all_goals subst p r
      · exact comm_of_αβ_βγ hi hj t u
      · exact comm_of_α_αβγ hi hj t u
      · exact comm_of_β_αβγ hi hj t u
      · exact comm_of_γ_αβγ hi hj t u
      · exact comm_of_αβ_αβγ hi hj t u
      · exact comm_of_βγ_αβγ hi hj t u
  · intro p h
    simp only [full_single_commutator_pairs] at h
    rcases h with h_old|h_new
    · tauto
    · right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_new
      intro r h_r
      simp only [rels_of_single_commutator_of_root_pair] at h_r
      rcases h_r with ⟨ i, j, hi, hj, t, u, goal ⟩
      rcases h_new with h_α_βγ|h_αβ_γ
      all_goals (
        subst p r
        simp only [map_mul, map_inv, mul_inv_eq_one]
      )
      · exact comm_of_α_βγ hi hj t u
      · exact comm_of_αβ_γ hi hj t u
  · tauto
  · intro p h
    simp only [full_mixed_commutes_roots] at h
    rcases h with h_old|h_new
    · tauto
    · right
      simp_all only [Set.mem_singleton_iff]
      intro r h_r
      simp only [rels_of_mixed_commutes_of_root] at h_r
      rcases h_r with ⟨ i, j, hi, hj, t, u, goal ⟩
      subst r
      exact comm_of_αβγ_αβγ hi hj t u
  · intro p h
    simp only [full_lin_roots] at h
    rcases h with h_old|h_new
    · tauto
    · right
      simp_all only [Set.mem_singleton_iff]
      intro r h_r
      simp only [rels_of_lin_of_root] at h_r
      rcases h_r with ⟨ i, hi, t, u, goal ⟩
      subst r
      simp only [map_mul, map_inv, mul_inv_eq_one]
      exact lin_of_αβγ hi t u
  · tauto
  · tauto

end Steinberg.A3
