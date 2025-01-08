import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Ring.Defs

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PresentedGroup

import Steinberg.Defs.Root
import Steinberg.Defs.Chevalley
import Steinberg.Defs.Deg
import Steinberg.Defs.Commutator
import Steinberg.Defs.WeakChevalley
import Steinberg.Defs.ReflDegB3Small

import Steinberg.Macro.Group

import Steinberg.Upstream.FreeGroup
import Steinberg.Upstream.PresentedGroup

namespace Steinberg

open Steinberg.Macro

variable {R : Type TR} [Ring R]

/-! ### Defining the B3 small positive root system -/

inductive B3SmallPosRoot
  | β | ψ | ω | βψ | ψω | β2ψ | βψω deriving Fintype, DecidableEq

namespace B3SmallPosRoot

@[reducible]
def height : B3SmallPosRoot → Nat
  | β | ψ | ω => 1
  | βψ | ψω => 2
  | βψω | β2ψ => 3

def toString : B3SmallPosRoot → String
  | β => "β"
  | ψ => "ψ"
  | ω => "ω"
  | βψ => "β+ψ"
  | ψω => "ψ+ω"
  | βψω => "β+ψ+ω"
  | β2ψ => "β+2ψ"

-- def add : A3PosRoot → A3PosRoot → Option A3PosRoot
--   | β, ψ => some βψ | ψ, ω => some ψω | β, ψω => some βψω | βψ, ω => some βψω
--   | _, _ => none

-- def mul : PNat → A3PosRoot → Option A3PosRoot := fun _ _ => none

-- theorem h_add {ζ η θ : A3PosRoot} :
--   (add ζ η = some θ) → height θ = height ζ + height η := by sorry

-- theorem h_mul {c : PNat} {r r' : A3PosRoot} :
--   (mul c r = r') → height r' = c * height r := by sorry

instance : PosRootSys B3SmallPosRoot where
  height := height
  -- add := add
  -- mul := mul
  toString := toString
  -- h_add := h_add
  -- h_mul := h_mul

end B3SmallPosRoot

namespace B3SmallProof

open B3SmallPosRoot GradedGen ReflDeg

/-! ### Bundle together assumptions about the B3 small generators -/

/-
The specific relation arises from "nonhomogeneously lifting" the commutator of βψ and ψω elements. (There is no analogue
of this relation for other root-pairs, since all other present pairs lie in a common two-dimensional subspace.)
-/
def rels_of_nonhomog_lift_of_comm_of_βψ_ψω :=
   { ⁅ (free_mk_mk βψ 2 (by trivial) (t₁ * u₁)) * (free_mk_mk βψ 1 (by trivial) (t₁ * u₀ + t₀ * u₁)) * (free_mk_mk βψ 0 (by trivial) (t₀ * u₀)),
       (free_mk_mk ψω 2 (by trivial) (u₁ * v₁)) * (free_mk_mk ψω 1 (by trivial) (u₁ * v₀ + u₀ * v₁)) * (free_mk_mk ψω 0 (by trivial) (u₀ * v₀)) ⁆ |
    (t₁ : R) (t₀ : R) (u₁ : R) (u₀ : R) (v₁ : R) (v₀ : R) }

def split_3_into_1_2 (i : ℕ) (hi : i ≤ 3) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)

theorem correct_of_split_3_into_1_2 (i : ℕ) (hi : i ≤ 3) :
  (split_3_into_1_2 i hi).1 ≤ 1 ∧ (split_3_into_1_2 i hi).2 ≤ 2 := by
  simp only [split_3_into_1_2]
  split
  all_goals trivial

-- There's also an alternative definition for βψω

def rels_of_def_of_βψω :=
  { ⁅ (free_mk_mk β (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 t),
      (free_mk_mk ψω (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (1 : R)) ⁆
      * (free_mk_mk βψω i hi t)⁻¹ | (i : ℕ) (hi : i ≤ βψω.height) (t : R)
  }

-- Don't know yet which category does relation 8.2 fit into

abbrev trivial_commutator_pairs : Set (B3SmallPosRoot × B3SmallPosRoot) := {(β, βψ), (β, β2ψ), (ψ, β2ψ), (βψ, β2ψ), (β, ω), (ψ, ψω), (ω, ψω)}
abbrev single_commutator_pairs : Set ((ζ : B3SmallPosRoot) × (η : B3SmallPosRoot) × (θ : B3SmallPosRoot) × R ×' (θ.height = ζ.height + η.height))
   := {⟨ ψ, βψ, β2ψ, 2, (by simp only [height])⟩, ⟨ψ, ω, ψω, 2, (by simp only [height])⟩}

abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3SmallPosRoot R) :=
    {⟨β, ψ, βψ, β2ψ, 1, 1, (by exact rfl), (by exact rfl)⟩}

abbrev mixed_commutes_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}
abbrev lin_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}
-- lifted commutator of βψ and ψω
def nonhomog_sets (R : Type TR) [Ring R] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot R)) := {
  rels_of_nonhomog_lift_of_comm_of_βψ_ψω
}
-- definition of βψω
def def_sets (R : Type TR) [Ring R] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot R)) := {
  rels_of_def_of_βψω
}

def weakB3Small := WeakChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  mixed_commutes_roots
  double_commutator_pairs
  lin_roots
  (nonhomog_sets R)
  (def_sets R)

abbrev weakB3Small_rels (R : Type TR) [Ring R] := @weakB3Small.all_rels B3SmallPosRoot _ R _

abbrev WeakChevalleyB3SmallGroup (R : Type TR) [Ring R] := PresentedGroup (@weakB3Small.all_rels B3SmallPosRoot _ R _)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" => weakB3Small.pres_mk (free_mk_mk ζ i (by (try simp only [PosRootSys.height] at *; try simp only [B3SmallPosRoot.height] at *; first | trivial | omega)) t)

section UnpackingPresentation

theorem comm_of_β_βψ : trivial_commutator_of_root_pair R weakB3Small.pres_mk β βψ :=
  weakB3Small.trivial_commutator_helper β βψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_β2ψ : trivial_commutator_of_root_pair R weakB3Small.pres_mk β β2ψ :=
  weakB3Small.trivial_commutator_helper β β2ψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_β2ψ : trivial_commutator_of_root_pair R weakB3Small.pres_mk ψ β2ψ :=
  weakB3Small.trivial_commutator_helper ψ β2ψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_βψ_β2ψ : trivial_commutator_of_root_pair R weakB3Small.pres_mk βψ β2ψ :=
  weakB3Small.trivial_commutator_helper βψ β2ψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_ω : trivial_commutator_of_root_pair R weakB3Small.pres_mk β ω :=
  weakB3Small.trivial_commutator_helper β ω (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_ψω : trivial_commutator_of_root_pair R weakB3Small.pres_mk ψ ψω :=
  weakB3Small.trivial_commutator_helper ψ ψω (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ω_ψω : trivial_commutator_of_root_pair R weakB3Small.pres_mk ω ψω :=
  weakB3Small.trivial_commutator_helper ω ψω (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_ω : single_commutator_of_root_pair weakB3Small.pres_mk ψ ω ψω (2 : R) (by rfl) :=
  weakB3Small.single_commutator_helper ψ ω ψω (2 : R) (by rfl) (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_βψ : single_commutator_of_root_pair weakB3Small.pres_mk ψ βψ β2ψ (2 : R) (by rfl) :=
  weakB3Small.single_commutator_helper ψ βψ β2ψ (2 : R) (by rfl) (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Linearity theorems for specific roots -/

theorem lin_of_β : lin_of_root R weakB3Small.pres_mk β :=
  weakB3Small.lin_helper β (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_ψ : lin_of_root R weakB3Small.pres_mk ψ :=
  weakB3Small.lin_helper ψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_ω : lin_of_root R weakB3Small.pres_mk ω :=
  weakB3Small.lin_helper ω (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_βψ : lin_of_root R weakB3Small.pres_mk βψ :=
  weakB3Small.lin_helper βψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_ψω : lin_of_root R weakB3Small.pres_mk ψω :=
  weakB3Small.lin_helper ψω (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_β2ψ : lin_of_root R weakB3Small.pres_mk β2ψ :=
  weakB3Small.lin_helper β2ψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Mixed-degree theorem for specific roots -/

theorem mixed_commutes_of_βψ : mixed_commutes_of_root R weakB3Small.pres_mk βψ :=
  weakB3Small.mixed_commutes_helper βψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_ψω : mixed_commutes_of_root R weakB3Small.pres_mk ψω :=
  weakB3Small.mixed_commutes_helper ψω (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_β2ψ : mixed_commutes_of_root R weakB3Small.pres_mk β2ψ :=
  weakB3Small.mixed_commutes_helper β2ψ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Nonhomogeneous lift -/

theorem nonhomog_lift_of_comm_of_βψ_ψω :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R), ⁅ {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀},
    {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} ⁆ = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply helper
  apply weakB3Small.nonhomog_helper rels_of_nonhomog_lift_of_comm_of_βψ_ψω
  · simp only [weakB3Small, nonhomog_sets, Set.mem_singleton_iff]
  · simp only
    exists t₁, t₀, u₁, u₀, v₁, v₀

/-! ### Definition of missing root -/
theorem def_of_βψω :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ βψω.height) (t : R), ⁅ weakB3Small.pres_mk (free_mk_mk β (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 t),
               weakB3Small.pres_mk (free_mk_mk ψω (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (1 : R)) ⁆
             = {βψω, i, t} := by
  intro t i hi
  apply helper
  apply weakB3Small.def_helper rels_of_def_of_βψω
  · simp only [weakB3Small, def_sets, Set.mem_singleton_iff]
  · simp only
    exists t, i, hi

@[group_reassoc]
theorem expr_βψ_βψ_as_βψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ βψ.height) (t u : R), commutes({βψ, i, t}, {βψ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [mixed_commutes_of_βψ]

@[group_reassoc]
theorem expr_ψω_ψω_as_ψω_ψω :
    ∀ {i j : ℕ} (hi : i ≤ ψω.height) (hj : j ≤ ψω.height) (t u : R), commutes({ψω, i, t}, {ψω, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [mixed_commutes_of_ψω]

theorem refl_of_nonhomog :
  ∀ S ∈ nonhomog_sets R,
    ∀r ∈ S, weakB3Small.pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [nonhomog_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_βψ_ψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, h' ⟩
  simp only [← h', map_mul, map_commutatorElement]
  rcases h'
  simp only [free_mk_mk, FreeGroup.map.of, refl_deg_of_gen, PosRootSys.height, height]
  simp_arith
  repeat rw [← free_mk_mk]
  rw [expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω, mul_assoc, mul_assoc,
    expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω, ← mul_assoc, ← mul_assoc,
    expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω]
  nth_rewrite 1 [add_comm]
  nth_rewrite 2 [add_comm]
  exact nonhomog_lift_of_comm_of_βψ_ψω t₀ t₁ u₀ u₁ v₀ v₁
  all_goals trivial

-- def relations are preserved under reflection
theorem refl_of_def :
  ∀ S ∈ def_sets R, ∀ r ∈ S,
    FreeGroup.map refl_deg_of_gen r ∈ S := by
  simp only [def_sets, Set.mem_singleton_iff, forall_eq, rels_of_def_of_βψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ i, hi, t, h' ⟩
  simp only [← h', map_mul, map_commutatorElement, split_3_into_1_2]
  rcases h'
  exists (βψω.height - i), (by omega), t
  -- can this be simplified?
  match i with
  | 0 => (simp only; congr)
  | 1 => (simp only; congr)
  | 2 => (simp only; congr)
  | 3 => (simp only; congr)

end UnpackingPresentation

/-! ### Identity theorems for specific roots -/

theorem id_of_βψ : id_of_root R weakB3Small.pres_mk βψ := by
  apply id_of_lin_of_root R lin_of_βψ

theorem id_of_ψω : id_of_root R weakB3Small.pres_mk ψω := by
  apply id_of_lin_of_root R lin_of_ψω

theorem id_of_β2ψ : id_of_root R weakB3Small.pres_mk β2ψ := by
  apply id_of_lin_of_root R lin_of_β2ψ

/-! ### Inverse theorems for specific roots -/

theorem inv_of_β : inv_of_root R weakB3Small.pres_mk β := by
  apply inv_of_lin_of_root R lin_of_β

theorem inv_of_ψ : inv_of_root R weakB3Small.pres_mk ψ := by
  apply inv_of_lin_of_root R lin_of_ψ

theorem inv_of_ω : inv_of_root R weakB3Small.pres_mk ω := by
  apply inv_of_lin_of_root R lin_of_ω

theorem inv_of_βψ : inv_of_root R weakB3Small.pres_mk βψ := by
  apply inv_of_lin_of_root R lin_of_βψ

theorem inv_of_ψω : inv_of_root R weakB3Small.pres_mk ψω := by
  apply inv_of_lin_of_root R lin_of_ψω

theorem inv_of_β2ψ : inv_of_root R weakB3Small.pres_mk β2ψ := by
  apply inv_of_lin_of_root R lin_of_β2ψ

/-! ### Derive full commutator for βψ and ψω from nonhomogeneous lift -/

-- NS: this section should probably be abstracted for reuse

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) (via the previous theorem). -/
private lemma homog_lift_of_comm_of_βψ_ψω (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : R), ⁅ { βψ, i + j, t}, {ψω, j + k, u} ⁆ = 1 := by
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
  ((i, j) ∈ ij_jk_image) → ∀ (t u : R), ⁅ {βψ, i, t}, {ψω, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  have ⟨ ijk', ⟨ h_in_cube, h_f ⟩ ⟩ := this
  have ⟨ hi', hj', hk' ⟩ := mem_range_of_boolean_cube ijk' h_in_cube
  let ⟨ i', j', k' ⟩ := ijk'
  have h_f' : i = i' + j' ∧ j = j' + k' := by rw [← Prod.mk.injEq, ← h_f, f_ij_jk]
  rw [← homog_lift_of_comm_of_βψ_ψω i' j' k' hi' hj' hk' t u]
  simp only [h_f']

private lemma comm_of_βψ_ψω_20 : ∀ (t u : R), ⁅ {βψ, 2, t}, {ψω, 0, u} ⁆ = 1 := by
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
private lemma comm_of_βψ_ψω_02 : ∀ (t u : R), ⁅ {βψ, 0, t}, {ψω, 2, u} ⁆ = 1 := by
  intro t u
  have : ⁅ {βψ, 0, t}, {ψω, 2, u} ⁆ = ReflDeg.refl_symm ⁅ {βψ, 2, t}, {ψω, 0, u} ⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, comm_of_βψ_ψω_20, map_one]

theorem comm_of_βψ_ψω : trivial_commutator_of_root_pair R weakB3Small.pres_mk βψ ψω := by
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

/-! ### Further useful identities (roughly GENERIC) -/

-- 8.37

theorem expand_βψ_as_ψ_β_ψ_β_ψ :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
      {βψ, i + j, 2 * (t * u)} = {ψ, j, (-u)} * {β, i, t} * {ψ, j, 2 * u} *
      {β, i, (-t)} * {ψ, j, (-u)} := by sorry

-- 8.38

theorem expand_β2ψ_as_ψ_βψ_ψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ 2 * ψ.height) (t u : R),
      {β2ψ, i + j, 2 * (t * u)} = {ψ, i, t} * {βψ, j, u} * {ψ, i, (-t)} *
      {βψ, j, (-u)} := by sorry

-- 8.39 a

theorem expr_ψ_ω_as_ω_ψω_ψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : R),
      {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψω, i + j, 2 * (t * u)} * {ψ, i, t} := by sorry

-- 8.39 b

theorem expr_ψ_ω_as_ω_ψ_ψω :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : R),
      {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψ, i, t} * {ψω, i + j, 2 * (t * u)} := by sorry

-- 8.40 a

theorem expr_β_ψ_as_ψ_βψ_β2ψ_β :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : R),
      {β, i, t} * {ψ, j, u} = {ψ, j, u} * {βψ, i + j, t * u} *
      {β2ψ, i + 2 * j, -(t * u^2)} * {β, i, t} := by sorry

-- 8.40 b

theorem expr_β_ψ_as_ψ_β_β2ψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : R),
      {β, i, t} * {ψ, j, u} = {ψ, j, u}  * {β, i, t} * {β2ψ, i + 2 * j, -(t * u^2)}
      * {βψ, i + j, t * u} := by sorry

-- 8.41

theorem expr_ψ_β_as_βψ_β2ψ_β_ψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ β.height) (t u : R),
      {ψ, j, u} * {β, i, t} =
      {βψ, i + j, -(t * u)} * {β2ψ, i + 2 * j, -(t * u^2)} * {β, i, t} *
      {ψ, j, u} := by sorry

/-! ### βψ and ψω commute -/

-- 8.42

theorem trivial_comm_of_βψ_ψω :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk βψ ψω := by sorry

/-! ### Establishing βψω -/

-- 8.43

theorem trivial_comm_of_β2ψ_ψω :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk β2ψ ψω := by sorry

-- 8.44

theorem Interchange :
    ∀ {i j k : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψ.height) (hk : k ≤ ω.height) (t u v : R),
      ⁅ {βψ, i + j, t * u}, {ω, k, v} ⁆ = ⁅ {β, i , t}, {ψω, j + k, 2 * (u * v)} ⁆ := by sorry

-- 8.46

theorem expr_βψω_as_βψ_ω_βψ_ω :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ω.height) (t u : R),
      {βψω, i + j, 2 * (t * u)} = {βψ, i, t} * {ω, j, u} * {βψ, i, -t} *
      {ω, j, -u} := by sorry

-- 8.47

theorem expr_βψω_as_β_ψω_β_ψω :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψω.height) (t u : R),
      {βψω, i + j, t * u} = {β, i, t} * {ψω, j, u} * {β, i, -t} * {ψω, j, -u} := by sorry

/-! ### Remaining commutation relations -/

-- 8.48

theorem trivial_comm_of_βψω_ω :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk βψω ω := by sorry

-- 8.49

theorem trivial_comm_of_βψω_β :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk βψω β := by sorry

-- 8.50

theorem trivial_comm_of_βψω_ψ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk βψω ψ := by sorry

-- 8.51

theorem trivial_comm_of_βψω_ψω :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk βψω ψω := by sorry

-- 8.52

theorem trivial_comm_of_βψω_βψ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk βψω βψ := by sorry

-- 8.53

theorem trivial_comm_of_βψω_β2ψ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk βψω β2ψ := by sorry

-- 8.54

theorem self_comm_of_βψω :
    mixed_commutes_of_root R weakB3Small.pres_mk βψω := by sorry

-- 8.55

theorem lin_of_βψω : lin_of_root R weakB3Small.pres_mk βψω := by sorry

-- 8.56

theorem inv_of_βψω : inv_of_root R weakB3Small.pres_mk βψω := by sorry

-- 8.57 a

theorem expr_βψ_ω_as_ω_βψω_βψ :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ω.height) (t u : R),
      {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψω, i + j, 2 * (t * u)} *
      {βψ, i, t} := by sorry

-- 8.57 b

theorem expr_βψ_ω_as_ω_βψ_βψω :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ω.height) (t u : R),
      {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψ, i, t} *
      {βψω, i + j, 2 * (t * u)} := by sorry

-- 8.58

theorem trivial_comm_of_β2ψ_ω :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk β2ψ ω := by sorry

-- /- Rewrite β⬝ω as ω⬝β. -/
-- @[group_reassoc]
-- theorem expr_β_ω_as_ω_β :
--     ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ ω.height) (t u : R), commutes({β, i, t}, {ω, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_β_ω]

-- /- Rewrite β⬝βψ as βψ⬝β. -/
-- @[group_reassoc]
-- theorem expr_β_βψ_as_βψ_β :
--     ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ βψ.height) (t u : R), commutes({β, i, t}, {βψ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_β_βψ]

-- /- Rewrite ψ⬝βψ as βψ⬝ψ. -/
-- @[group_reassoc]
-- theorem expr_ψ_βψ_as_βψ_ψ :
--     ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ βψ.height) (t u : R), commutes({ψ, i, t}, {βψ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_ψ_βψ]

-- /- Rewrite ω⬝ψω as ψω⬝ω. -/
-- @[group_reassoc]
-- theorem expr_ω_ψω_as_ψω_ω :
--     ∀ {i j : ℕ} (hi : i ≤ ω.height) (hj : j ≤ ψω.height) (t u : R), commutes({ω, i, t}, {ψω, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_ω_ψω]

-- /- Rewrite βψ⬝ψω as ψω⬝βψ. -/
-- @[group_reassoc]
-- theorem expr_βψ_ψω_as_ψω_βψ :
--   ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ψω.height) (t u : R), commutes({βψ, i, t}, {ψω, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_βψ_ψω]

-- /-! ### Interchange theorems between ⁅β,ψω⁆ and ⁅βψ,ω⁆ forms -/

-- /- Interchange between ⁅β, ψω⁆ and ⁅βψ, ω⁆, "trading" a single degree j : Deg 1 and scalar u : R. -/
-- theorem Interchange {i j k : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψ.height) (hk : k ≤ ω.height) :
--     ∀ (t u v : R), ⁅ {β, i, t}, {ψω, j + k, u * v} ⁆ = ⁅ {βψ, i + j, t * u}, {ω, k, v} ⁆ := by
--   intro t u v
--   apply eq_comm_of_reorder_left
--   have hij : i + j ≤ βψ.height := by simp only [height] at *; omega
--   have hjk : j + k ≤ ψω.height := by simp only [height] at *; omega
--   -- phase I: push β to right
--   grw [expand_ψω_as_ψ_ω_ψ_ω hj hk,
--     expr_β_ψ_as_βψ_ψ_β hi hj,
--     expr_β_ω_as_ω_β hi hk,
--     expr_β_ψ_as_βψ_ψ_β hi hj,
--     mul_neg,
--     expr_β_ω_as_ω_β hi hk,
--     expr_ψ_ω_as_ψω_ω_ψ hj hk,
--     expr_ψ_βψ_as_βψ_ψ hj hij,
--     inv_of_ψ,
--     ← expr_ω_ψω_as_ψω_ω hk hjk,
--     ← expr_βψ_ψω_as_ψω_βψ hij hjk]
--   group
--   grw [expr_ψ_ω_as_ψω_ω_ψ hj hk,
--       ← expr_ω_ψω_as_ψω_ω hk hjk,
--       inv_of_βψ]
--   simp

-- /- Pass between ⁅β,ψω⁆ and ⁅βψ,ω⁆ forms (specializes `Interchange` to the case `u=1`). -/
-- theorem InterchangeTrans {i j k : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψ.height) (hk : k ≤ ω.height) :
--     ∀ (t u : R), ⁅ {β, i, t}, {ψω, (j + k), u} ⁆ = ⁅ {βψ, (i + j), t}, {ω, k, u} ⁆ := by
--   intro t u
--   nth_rewrite 1 [← one_mul u]
--   nth_rewrite 2 [← mul_one t]
--   rw [Interchange hi hj hk]

-- /- ⁅β,ψω⁆ forms depend only on product of coefficients. Applies `Interchange` twice. -/
-- theorem InterchangeRefl {i j k : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψ.height) (hk : k ≤ ω.height) :
--     ∀ (t u : R), ⁅ {β, i, 1 * (t * u)}, {ψω, (j + k), 1} ⁆ = ⁅ {β, i, t}, {ψω, (j + k), u} ⁆ := by
--   intro t u
--   nth_rewrite 2 [← mul_one u]
--   rw [Interchange hi hj hk]
--   rw [InterchangeTrans hi hj hk]
--   rw [one_mul]

-- /-! ### Commutator relations for (β,ψω) and (βψ,ω) via interchange relations -/

-- -- NS: Really need to figure out a more sane way to write this section.

-- -- height 0
-- private lemma comm_of_β_ψω_00 (t u : R) :
--     ⁅ {β, 0, t}, {ψω, 0, u} ⁆ = {βψω, 0 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_βψω (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]

-- private lemma comm_of_βψ_ω_00 (t u : R) :
--     ⁅ {βψ, 0, t}, {ω, 0, u} ⁆ = {βψω, 0 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_β_ψω_00]

-- -- height 1
-- private lemma comm_of_β_ψω_01 (t u : R) :
--     ⁅ {β, 0, t}, {ψω, 1, u} ⁆ = {βψω, 0 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_βψω (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]

-- private lemma comm_of_βψ_ω_10 (t u : R) : ⁅ {βψ, 1, t}, {ω, 0, u} ⁆ = {βψω, 1 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]
--   simp only [add_zero, comm_of_β_ψω_01, zero_add, one_mul]

-- private lemma comm_of_β_ψω_10 (t u : R) : ⁅ {β, 1, t}, {ψω, 0, u} ⁆ = {βψω, 1 + 0, 1 * (t * u)} := by
--   rw [@InterchangeTrans _ _ 1 0 0 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_βψ_ω_10]

-- private lemma comm_of_βψ_ω_01 (t u : R) : ⁅ {βψ, 0, t}, {ω, 1, u} ⁆ = {βψω, 0 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_β_ψω_01]

-- -- height 2
-- private lemma comm_of_β_ψω_11 (t u : R) :
--     ⁅ {β, 1, t}, {ψω, 1, u} ⁆ = {βψω, 1 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_βψω (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]

-- private lemma comm_of_βψ_ω_11 (t u : R) : ⁅ {βψ, 1, t}, {ω, 1, u} ⁆ = {βψω, 1 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_β_ψω_11]

-- private lemma comm_of_β_ψω_02 (t u : R) : ⁅ {β, 0, t}, {ψω, 2, u} ⁆ = {βψω, 0 + 2, 1 * (t * u)} := by
--   rw [@InterchangeTrans _ _ 0 1 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_βψ_ω_11]

-- private lemma comm_of_βψ_ω_20 (t u : R) : ⁅ {βψ, 2, t}, {ω, 0, u} ⁆ = {βψω, 2 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_β_ψω_11]

-- -- height 3
-- private lemma comm_of_β_ψω_12 (t u : R) : ⁅ {β, 1, t}, {ψω, 2, u} ⁆ = {βψω, 1 + 2, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_βψω (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]
-- private lemma comm_of_βψ_ω_21 (t u : R) : ⁅ {βψ, 2, t}, {ω, 1, u} ⁆ = {βψω, 2 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_β_ψω_12]

-- /- Commutator relation for β and ψω. -/
-- theorem comm_of_β_ψω : single_commutator_of_root_pair weakA3.pres_mk β ψω βψω (1 : R) (by simp only [PosRootSys.height] at *; simp only [B3SmallPosRoot.height] at *) := by
--   intro i j hi hj t u
--   match i, j with
--   | 0, 0 => exact comm_of_β_ψω_00 t u
--   | 0, 1 => exact comm_of_β_ψω_01 t u
--   | 0, 2 => exact comm_of_β_ψω_02 t u
--   | 1, 0 => exact comm_of_β_ψω_10 t u
--   | 1, 1 => exact comm_of_β_ψω_11 t u
--   | 1, 2 => exact comm_of_β_ψω_12 t u

-- /- Commutator relation for βψ and ω. -/
-- theorem comm_of_βψ_ω : single_commutator_of_root_pair weakA3.pres_mk βψ ω βψω (1 : R) (by simp only [PosRootSys.height] at *; simp only [B3SmallPosRoot.height] at *) := by
--   intro i j hi hj t u
--   match i, j with
--   | 0, 0 => exact comm_of_βψ_ω_00 t u
--   | 1, 0 => exact comm_of_βψ_ω_10 t u
--   | 2, 0 => exact comm_of_βψ_ω_20 t u
--   | 0, 1 => exact comm_of_βψ_ω_01 t u
--   | 1, 1 => exact comm_of_βψ_ω_11 t u
--   | 2, 1 => exact comm_of_βψ_ω_21 t u

-- /-! ### More rewriting theorems -/

-- /- Expand βψω as β⬝ψω⬝β⬝ψω. -/
-- theorem expand_βψω_as_β_ψω_β_ψω :
--     ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψω.height) (t u : R),
--       {βψω, (i + j), (t * u)} = {β, i, t} * {ψω, j, u} * {β, i, (-t)} * {ψω, j, (-u)} := by
--   intro i j hi hj t u
--   rw [inv_of_β, inv_of_ψω, ← commutatorElement_def, ← one_mul (t * u), ← comm_of_β_ψω]

-- /- Expand βψω as βψ⬝ω⬝βψ⬝ω. -/
-- theorem expand_βψω_as_βψ_ω_βψ_ω :
--     ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ω.height) (t u : R),
--       {βψω, (i + j), (t * u)} = {βψ, i, t} * {ω, j, u} * {βψ, i, (-t)} * {ω, j, (-u)} := by
--   intro i j hi hj t u
--   rw [inv_of_βψ, inv_of_ω, ← commutatorElement_def, ← one_mul (t * u), ← comm_of_βψ_ω]

-- /-! ### Commutators of βψω with other roots -/

-- /- β and βψω commute. -/
-- /- NS: One should be able to prove this quite simply:  simple proof: we know βψω is expressible as a product of βψ's and ω's (expand_βψω_as_βψ_ω_βψ_ω), and we know that β's
--    commute with βψ's (expr_β_βψ_as_βψ_β) and ω's (expr_β_ω_as_ω_β) -/
-- theorem comm_of_β_βψω : trivial_commutator_of_root_pair R weakA3.pres_mk β βψω := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose βψ.height ω.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_βψω_as_βψ_ω_βψ_ω hj₁ hj₂,
--       expr_β_βψ_as_βψ_β hi hj₁,
--       expr_β_ω_as_ω_β hi hj₂,
--       expr_β_βψ_as_βψ_β hi hj₁,
--       expr_β_ω_as_ω_β hi hj₂]

-- /- ω and βψω commute. -/
-- theorem comm_of_ω_βψω : trivial_commutator_of_root_pair R weakA3.pres_mk ω βψω := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose β.height ψω.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_βψω_as_β_ψω_β_ψω hj₁ hj₂,
--     ← expr_β_ω_as_ω_β hj₁ hi,
--     expr_ω_ψω_as_ψω_ω hi hj₂,
--     ← expr_β_ω_as_ω_β hj₁ hi,
--     expr_ω_ψω_as_ψω_ω hi hj₂]

-- /- ψ and βψω commute. -/
-- -- the only commutator proof where we have to do something 'interesting'
-- theorem comm_of_ψ_βψω : trivial_commutator_of_root_pair R weakA3.pres_mk ψ βψω := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose βψ.height ω.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_βψω_as_βψ_ω_βψ_ω hj₁ hj₂,
--       expr_ψ_βψ_as_βψ_ψ hi hj₁,
--       expr_ψ_ω_as_ω_ψω_ψ hi hj₂,
--       expr_ψ_βψ_as_βψ_ψ hi hj₁,
--       expr_ψ_ω_as_ψω_ω_ψ hi hj₂,
--       ← expr_βψ_ψω_as_ψω_βψ hj₁ (by simp only [PosRootSys.height, height] at *; omega),
--       mul_neg, inv_of_ψω]
--   group

-- /- βψ and βψω commute. -/
-- theorem comm_of_βψ_βψω : trivial_commutator_of_root_pair R weakA3.pres_mk βψ βψω := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose β.height ψω.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_βψω_as_β_ψω_β_ψω hj₁ hj₂,
--     ← expr_β_βψ_as_βψ_β hj₁ hi,
--     expr_βψ_ψω_as_ψω_βψ hi hj₂,
--     ← expr_β_βψ_as_βψ_β hj₁ hi,
--     expr_βψ_ψω_as_ψω_βψ hi hj₂]

-- /- ψω and βψω commute. -/
-- theorem comm_of_ψω_βψω : trivial_commutator_of_root_pair R weakA3.pres_mk ψω βψω := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose βψ.height ω.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_βψω_as_βψ_ω_βψ_ω hj₁ hj₂,
--     ← expr_βψ_ψω_as_ψω_βψ hj₁ hi,
--     ← expr_ω_ψω_as_ψω_ω hj₂ hi,
--     ← expr_βψ_ψω_as_ψω_βψ hj₁ hi,
--     ← expr_ω_ψω_as_ψω_ω hj₂ hi]

-- /- Rewrite β⬝βψω as βψω⬝β. -/
-- @[group_reassoc]
-- theorem expr_β_βψω_as_βψω_β :
--     ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ βψω.height) (t u : R), commutes({β, i, t}, {βψω, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_β_βψω]

-- /- Rewrite ψω⬝βψω as βψω⬝ψω. -/
-- @[group_reassoc]
-- theorem expr_ψω_βψω_as_βψω_ψω :
--     ∀ {i j : ℕ} (hi : i ≤ ψω.height) (hj : j ≤ βψω.height) (t u : R), commutes({ψω, i, t}, {βψω, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_ψω_βψω]

-- /- βψω commutes with itself. -/
-- theorem mixed_commutes_of_βψω : trivial_commutator_of_root_pair R weakA3.pres_mk βψω βψω := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose β.height ψω.height j (by trivial)
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_βψω_as_β_ψω_β_ψω hj₁ hj₂,
--     ← expr_β_βψω_as_βψω_β hj₁ hi,
--     ← expr_ψω_βψω_as_βψω_ψω hj₂ hi,
--     ← expr_β_βψω_as_βψω_β hj₁ hi,
--     ← expr_ψω_βψω_as_βψω_ψω hj₂ hi]

-- /- Linearity for βψω. -/
-- theorem lin_of_βψω : lin_of_root R weakA3.pres_mk βψω := by
--   intro i hi t u
--   let ⟨ i₁, i₂, ⟨ h_eq, hi₁, hi₂ ⟩ ⟩ := decompose β.height ψω.height i (by trivial)
--   have h_eq' : i₁ + i₂ ≤ PosRootSys.height βψω := by omega
--   simp_rw [h_eq]
--   nth_rewrite 1 [← mul_one t]
--   grw [expand_βψω_as_β_ψω_β_ψω hi₁ hi₂,
--     expr_ψω_βψω_as_βψω_ψω hi₂ h_eq',
--     expr_β_βψω_as_βψω_β hi₁ h_eq',
--     expr_ψω_βψω_as_βψω_ψω hi₂ h_eq']
--   nth_rewrite 1 [← mul_one u]
--   grw [expand_βψω_as_β_ψω_β_ψω hi₁ hi₂, lin_of_β]
--   nth_rewrite 1 [inv_of_ψω]
--   group

--   rw [mul_assoc _ {β, i₁, -u}, lin_of_β, ← neg_add u t, add_comm u t, ← expand_βψω_as_β_ψω_β_ψω hi₁ hi₂, mul_one]

-- end A3Proof
