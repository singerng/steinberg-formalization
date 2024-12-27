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
  | α | β | γ | αβ | βγ | α2β | αβγ deriving Fintype, DecidableEq

namespace B3SmallPosRoot

@[reducible]
def height : B3SmallPosRoot → Nat
  | α | β | γ => 1
  | αβ | βγ => 2
  | αβγ | α2β => 3

def toString : B3SmallPosRoot → String
  | α => "α"
  | β => "β"
  | γ => "γ"
  | αβ => "α+β"
  | βγ => "β+γ"
  | αβγ => "α+β+γ"
  | α2β => "α+2β"

-- def add : A3PosRoot → A3PosRoot → Option A3PosRoot
--   | α, β => some αβ | β, γ => some βγ | α, βγ => some αβγ | αβ, γ => some αβγ
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
The specific relation arises from "nonhomogeneously lifting" the commutator of αβ and βγ elements. (There is no analogue
of this relation for other root-pairs, since all other present pairs lie in a common two-dimensional subspace.)
-/
def rels_of_nonhomog_lift_of_comm_of_αβ_βγ :=
   { ⁅ (free_mk_mk αβ 2 (by trivial) (t₁ * u₁)) * (free_mk_mk αβ 1 (by trivial) (t₁ * u₀ + t₀ * u₁)) * (free_mk_mk αβ 0 (by trivial) (t₀ * u₀)),
       (free_mk_mk βγ 2 (by trivial) (u₁ * v₁)) * (free_mk_mk βγ 1 (by trivial) (u₁ * v₀ + u₀ * v₁)) * (free_mk_mk βγ 0 (by trivial) (u₀ * v₀)) ⁆ |
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

-- There's also an alternative definition for αβγ

def rels_of_def_of_αβγ :=
  { ⁅ (free_mk_mk α (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 t),
      (free_mk_mk βγ (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (1 : R)) ⁆
      * (free_mk_mk αβγ i hi t)⁻¹ | (i : ℕ) (hi : i ≤ αβγ.height) (t : R)
  }

-- Don't know yet which category does relation 8.2 fit into

abbrev trivial_commutator_pairs : Set (B3SmallPosRoot × B3SmallPosRoot) := {(α, αβ), (α, α2β), (β, α2β), (αβ, α2β), (α, γ), (β, βγ), (γ, βγ)}
abbrev single_commutator_pairs : Set ((ζ : B3SmallPosRoot) × (η : B3SmallPosRoot) × (θ : B3SmallPosRoot) × R ×' (θ.height = ζ.height + η.height))
   := {⟨ β, αβ, α2β, 2, (by simp only [height])⟩, ⟨β, γ, βγ, 2, (by simp only [height])⟩}

abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3SmallPosRoot R) :=
    {⟨α, β, αβ, α2β, 1, 1, (by exact rfl), (by exact rfl)⟩}

abbrev mixed_commutes_roots : Set (B3SmallPosRoot) := {α, β, γ, αβ, βγ, α2β}
abbrev lin_roots : Set (B3SmallPosRoot) := {α, β, γ, αβ, βγ, α2β}
-- lifted commutator of αβ and βγ
def nonhomog_sets (R : Type TR) [Ring R] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot R)) := {
  rels_of_nonhomog_lift_of_comm_of_αβ_βγ
}
-- definition of αβγ
def def_sets (R : Type TR) [Ring R] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot R)) := {
  rels_of_def_of_αβγ
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

theorem comm_of_α_αβ : trivial_commutator_of_root_pair R weakB3Small.pres_mk α αβ :=
  weakB3Small.trivial_commutator_helper α αβ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_α_α2β : trivial_commutator_of_root_pair R weakB3Small.pres_mk α α2β :=
  weakB3Small.trivial_commutator_helper α α2β (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_α2β : trivial_commutator_of_root_pair R weakB3Small.pres_mk β α2β :=
  weakB3Small.trivial_commutator_helper β α2β (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_αβ_α2β : trivial_commutator_of_root_pair R weakB3Small.pres_mk αβ α2β :=
  weakB3Small.trivial_commutator_helper αβ α2β (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_α_γ : trivial_commutator_of_root_pair R weakB3Small.pres_mk α γ :=
  weakB3Small.trivial_commutator_helper α γ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_βγ : trivial_commutator_of_root_pair R weakB3Small.pres_mk β βγ :=
  weakB3Small.trivial_commutator_helper β βγ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_γ_βγ : trivial_commutator_of_root_pair R weakB3Small.pres_mk γ βγ :=
  weakB3Small.trivial_commutator_helper γ βγ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_γ : single_commutator_of_root_pair weakB3Small.pres_mk β γ βγ (2 : R) (by rfl) :=
  weakB3Small.single_commutator_helper β γ βγ (2 : R) (by rfl) (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_αβ : single_commutator_of_root_pair weakB3Small.pres_mk β αβ α2β (2 : R) (by rfl) :=
  weakB3Small.single_commutator_helper β αβ α2β (2 : R) (by rfl) (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Linearity theorems for specific roots -/

theorem lin_of_α : lin_of_root R weakB3Small.pres_mk α :=
  weakB3Small.lin_helper α (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_β : lin_of_root R weakB3Small.pres_mk β :=
  weakB3Small.lin_helper β (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_γ : lin_of_root R weakB3Small.pres_mk γ :=
  weakB3Small.lin_helper γ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_αβ : lin_of_root R weakB3Small.pres_mk αβ :=
  weakB3Small.lin_helper αβ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_βγ : lin_of_root R weakB3Small.pres_mk βγ :=
  weakB3Small.lin_helper βγ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_α2β : lin_of_root R weakB3Small.pres_mk α2β :=
  weakB3Small.lin_helper α2β (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Mixed-degree theorem for specific roots -/

theorem mixed_commutes_of_αβ : mixed_commutes_of_root R weakB3Small.pres_mk αβ :=
  weakB3Small.mixed_commutes_helper αβ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_βγ : mixed_commutes_of_root R weakB3Small.pres_mk βγ :=
  weakB3Small.mixed_commutes_helper βγ (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_α2β : mixed_commutes_of_root R weakB3Small.pres_mk α2β :=
  weakB3Small.mixed_commutes_helper α2β (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Nonhomogeneous lift -/

theorem nonhomog_lift_of_comm_of_αβ_βγ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R), ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
    {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} ⁆ = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply helper
  apply weakB3Small.nonhomog_helper rels_of_nonhomog_lift_of_comm_of_αβ_βγ
  · simp only [weakB3Small, nonhomog_sets, Set.mem_singleton_iff]
  · simp only
    exists t₁, t₀, u₁, u₀, v₁, v₀

/-! ### Definition of missing root -/
theorem def_of_αβγ :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ αβγ.height) (t : R), ⁅ weakB3Small.pres_mk (free_mk_mk α (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 t),
               weakB3Small.pres_mk (free_mk_mk βγ (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (1 : R)) ⁆
             = {αβγ, i, t} := by
  intro t i hi
  apply helper
  apply weakB3Small.def_helper rels_of_def_of_αβγ
  · simp only [weakB3Small, def_sets, Set.mem_singleton_iff]
  · simp only
    exists t, i, hi

@[group_reassoc]
theorem expr_αβ_αβ_as_αβ_αβ :
    ∀ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ αβ.height) (t u : R), commutes({αβ, i, t}, {αβ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [mixed_commutes_of_αβ]

@[group_reassoc]
theorem expr_βγ_βγ_as_βγ_βγ :
    ∀ {i j : ℕ} (hi : i ≤ βγ.height) (hj : j ≤ βγ.height) (t u : R), commutes({βγ, i, t}, {βγ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [mixed_commutes_of_βγ]

theorem refl_of_nonhomog :
  ∀ S ∈ nonhomog_sets R,
    ∀r ∈ S, weakB3Small.pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [nonhomog_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_αβ_βγ, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, h' ⟩
  simp only [← h', map_mul, map_commutatorElement]
  rcases h'
  simp only [free_mk_mk, FreeGroup.map.of, refl_deg_of_gen, PosRootSys.height, height]
  simp_arith
  repeat rw [← free_mk_mk]
  rw [expr_αβ_αβ_as_αβ_αβ, expr_βγ_βγ_as_βγ_βγ, mul_assoc, mul_assoc,
    expr_αβ_αβ_as_αβ_αβ, expr_βγ_βγ_as_βγ_βγ, ← mul_assoc, ← mul_assoc,
    expr_αβ_αβ_as_αβ_αβ, expr_βγ_βγ_as_βγ_βγ]
  nth_rewrite 1 [add_comm]
  nth_rewrite 2 [add_comm]
  exact nonhomog_lift_of_comm_of_αβ_βγ t₀ t₁ u₀ u₁ v₀ v₁
  all_goals trivial

-- def relations are preserved under reflection
theorem refl_of_def :
  ∀ S ∈ def_sets R, ∀ r ∈ S,
    FreeGroup.map refl_deg_of_gen r ∈ S := by
  simp only [def_sets, Set.mem_singleton_iff, forall_eq, rels_of_def_of_αβγ, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ i, hi, t, h' ⟩
  simp only [← h', map_mul, map_commutatorElement, split_3_into_1_2]
  rcases h'
  exists (αβγ.height - i), (by omega), t
  -- can this be simplified?
  match i with
  | 0 => (simp only; congr)
  | 1 => (simp only; congr)
  | 2 => (simp only; congr)
  | 3 => (simp only; congr)

end UnpackingPresentation

/-! ### Identity theorems for specific roots -/

theorem id_of_αβ : id_of_root R weakB3Small.pres_mk αβ := by
  apply id_of_lin_of_root R lin_of_αβ

theorem id_of_βγ : id_of_root R weakB3Small.pres_mk βγ := by
  apply id_of_lin_of_root R lin_of_βγ

theorem id_of_α2β : id_of_root R weakB3Small.pres_mk α2β := by
  apply id_of_lin_of_root R lin_of_α2β

/-! ### Inverse theorems for specific roots -/

theorem inv_of_α : inv_of_root R weakB3Small.pres_mk α := by
  apply inv_of_lin_of_root R lin_of_α

theorem inv_of_β : inv_of_root R weakB3Small.pres_mk β := by
  apply inv_of_lin_of_root R lin_of_β

theorem inv_of_γ : inv_of_root R weakB3Small.pres_mk γ := by
  apply inv_of_lin_of_root R lin_of_γ

theorem inv_of_αβ : inv_of_root R weakB3Small.pres_mk αβ := by
  apply inv_of_lin_of_root R lin_of_αβ

theorem inv_of_βγ : inv_of_root R weakB3Small.pres_mk βγ := by
  apply inv_of_lin_of_root R lin_of_βγ

theorem inv_of_α2β : inv_of_root R weakB3Small.pres_mk α2β := by
  apply inv_of_lin_of_root R lin_of_α2β

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
    have hf_i : i ∈ [0,1] := mem_list_range_iff_le.mp hi
    have hf_j : j ∈ [0,1] := mem_list_range_iff_le.mp hj
    have hf_k : k ∈ [0,1] := mem_list_range_iff_le.mp hk
    have id₁ : {αβ, i + j, t} = {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp only [t₀, t₁, u₀, u₁, v₀, v₁]
        simp only [add_zero, mul_zero, zero_mul, mul_one, zero_add]
        repeat rw [id_of_αβ]
        simp only [one_mul, mul_one]
      )
    )
    have id₂ : {βγ, j + k, u} = {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp only [t₀, t₁, u₀, u₁, v₀, v₁]
        simp only [add_zero, mul_zero, zero_mul, one_mul, zero_add]
        repeat rw [id_of_βγ]
        simp only [one_mul, mul_one]
      )
    )
    rw [id₁, id₂, nonhomog_lift_of_comm_of_αβ_βγ]

private lemma image_of_homog_lift_of_comm_of_αβ_βγ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ βγ.height) :
  ((i, j) ∈ ij_jk_image) → ∀ (t u : R), ⁅ {αβ, i, t}, {βγ, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  have ⟨ ijk', ⟨ h_in_cube, h_f ⟩ ⟩ := this
  have ⟨ hi', hj', hk' ⟩ := mem_range_of_boolean_cube ijk' h_in_cube
  let ⟨ i', j', k' ⟩ := ijk'
  have h_f' : i = i' + j' ∧ j = j' + k' := by rw [← Prod.mk.injEq, ← h_f, f_ij_jk]
  rw [← homog_lift_of_comm_of_αβ_βγ i' j' k' hi' hj' hk' t u]
  simp only [h_f']

private lemma comm_of_αβ_βγ_20 : ∀ (t u : R), ⁅ {αβ, 2, t}, {βγ, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {βγ, 1, u} _ ({αβ, 1, t + 1} * {αβ, 0, 1})
  mul_assoc_l
  rw [← nonhomog_lift_of_comm_of_αβ_βγ t 1 1 1 0 u]
  simp only [one_mul, mul_one, mul_zero, add_zero]
  rw [id_of_βγ] -- NS: maybe should be a simp lemma? we can decide...
  rw [one_mul]
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
  have : ⁅ {αβ, 0, t}, {βγ, 2, u} ⁆ = ReflDeg.refl_symm ⁅ {αβ, 2, t}, {βγ, 0, u} ⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, comm_of_αβ_βγ_20, map_one]

theorem comm_of_αβ_βγ : trivial_commutator_of_root_pair R weakB3Small.pres_mk αβ βγ := by
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
    rw [← comm_of_αβ_βγ_02 t u]
  ·
    let ⟨ hd_i, hd_j ⟩ := hij
    simp_rw [hd_i, hd_j]
    rw [← comm_of_αβ_βγ_20 t u]
  ·
    apply image_of_homog_lift_of_comm_of_αβ_βγ hi hj
    exact hij

/-! ### Further useful identities (roughly GENERIC) -/

-- 8.37

theorem expand_αβ_as_β_α_β_α_β :
    ∀ {i j : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (t u : R),
      {αβ, i + j, 2 * (t * u)} = {β, j, (-u)} * {α, i, t} * {β, j, 2 * u} *
      {α, i, (-t)} * {β, j, (-u)} := by sorry

-- 8.38

theorem expand_α2β_as_β_αβ_β_αβ :
    ∀ {i j : ℕ} (hi : i ≤ α.height) (hj : j ≤ 2 * β.height) (t u : R),
      {α2β, i + j, 2 * (t * u)} = {β, i, t} * {αβ, j, u} * {β, i, (-t)} *
      {αβ, j, (-u)} := by sorry

-- 8.39 a

theorem expr_β_γ_as_γ_βγ_β :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
      {β, i, t} * {γ, j, u} = {γ, j, u} * {βγ, i + j, 2 * (t * u)} * {β, i, t} := by sorry

-- 8.39 b

theorem expr_β_γ_as_γ_β_βγ :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
      {β, i, t} * {γ, j, u} = {γ, j, u} * {β, i, t} * {βγ, i + j, 2 * (t * u)} := by sorry

-- 8.40 a

theorem expr_α_β_as_β_αβ_α2β_α :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
      {α, i, t} * {β, j, u} = {β, j, u} * {αβ, i + j, t * u} *
      {α2β, i + 2 * j, -(t * u^2)} * {α, i, t} := by sorry

-- 8.40 b

theorem expr_α_β_as_β_α_α2β_αβ :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
      {α, i, t} * {β, j, u} = {β, j, u}  * {α, i, t} * {α2β, i + 2 * j, -(t * u^2)}
      * {αβ, i + j, t * u} := by sorry

-- 8.41

theorem expr_β_α_as_αβ_α2β_α_β :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ α.height) (t u : R),
      {β, j, u} * {α, i, t} =
      {αβ, i + j, -(t * u)} * {α2β, i + 2 * j, -(t * u^2)} * {α, i, t} *
      {β, j, u} := by sorry

/-! ### αβ and βγ commute -/

-- 8.42

theorem trivial_comm_of_αβ_βγ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk αβ βγ := by sorry

/-! ### Establishing αβγ -/

-- 8.43

theorem trivial_comm_of_α2β_βγ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk α2β βγ := by sorry

-- 8.44

theorem Interchange :
    ∀ {i j k : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) (t u v : R),
      ⁅ {αβ, i + j, t * u}, {γ, k, v} ⁆ = ⁅ {α, i , t}, {βγ, j + k, 2 * (u * v)} ⁆ := by sorry

-- 8.46

theorem expr_αβγ_as_αβ_γ_αβ_γ :
    ∀ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (t u : R),
      {αβγ, i + j, 2 * (t * u)} = {αβ, i, t} * {γ, j, u} * {αβ, i, -t} *
      {γ, j, -u} := by sorry

-- 8.47

theorem expr_αβγ_as_α_βγ_α_βγ :
    ∀ {i j : ℕ} (hi : i ≤ α.height) (hj : j ≤ βγ.height) (t u : R),
      {αβγ, i + j, t * u} = {α, i, t} * {βγ, j, u} * {α, i, -t} * {βγ, j, -u} := by sorry

/-! ### Remaining commutation relations -/

-- 8.48

theorem trivial_comm_of_αβγ_γ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk αβγ γ := by sorry

-- 8.49

theorem trivial_comm_of_αβγ_α :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk αβγ α := by sorry

-- 8.50

theorem trivial_comm_of_αβγ_β :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk αβγ β := by sorry

-- 8.51

theorem trivial_comm_of_αβγ_βγ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk αβγ βγ := by sorry

-- 8.52

theorem trivial_comm_of_αβγ_αβ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk αβγ αβ := by sorry

-- 8.53

theorem trivial_comm_of_αβγ_α2β :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk αβγ α2β := by sorry

-- 8.54

theorem self_comm_of_αβγ :
    mixed_commutes_of_root R weakB3Small.pres_mk αβγ := by sorry

-- 8.55

theorem lin_of_αβγ : lin_of_root R weakB3Small.pres_mk αβγ := by sorry

-- 8.56

theorem inv_of_αβγ : inv_of_root R weakB3Small.pres_mk αβγ := by sorry

-- 8.57 a

theorem expr_αβ_γ_as_γ_αβγ_αβ :
    ∀ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (t u : R),
      {αβ, i, t} * {γ, j, u} = {γ, j, u} * {αβγ, i + j, 2 * (t * u)} *
      {αβ, i, t} := by sorry

-- 8.57 b

theorem expr_αβ_γ_as_γ_αβ_αβγ :
    ∀ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (t u : R),
      {αβ, i, t} * {γ, j, u} = {γ, j, u} * {αβ, i, t} *
      {αβγ, i + j, 2 * (t * u)} := by sorry

-- 8.58

theorem trivial_comm_of_α2β_γ :
    trivial_commutator_of_root_pair R weakB3Small.pres_mk α2β γ := by sorry

-- /- Rewrite α⬝γ as γ⬝α. -/
-- @[group_reassoc]
-- theorem expr_α_γ_as_γ_α :
--     ∀ {i j : ℕ} (hi : i ≤ α.height) (hj : j ≤ γ.height) (t u : R), commutes({α, i, t}, {γ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_α_γ]

-- /- Rewrite α⬝αβ as αβ⬝α. -/
-- @[group_reassoc]
-- theorem expr_α_αβ_as_αβ_α :
--     ∀ {i j : ℕ} (hi : i ≤ α.height) (hj : j ≤ αβ.height) (t u : R), commutes({α, i, t}, {αβ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_α_αβ]

-- /- Rewrite β⬝αβ as αβ⬝β. -/
-- @[group_reassoc]
-- theorem expr_β_αβ_as_αβ_β :
--     ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ αβ.height) (t u : R), commutes({β, i, t}, {αβ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_β_αβ]

-- /- Rewrite γ⬝βγ as βγ⬝γ. -/
-- @[group_reassoc]
-- theorem expr_γ_βγ_as_βγ_γ :
--     ∀ {i j : ℕ} (hi : i ≤ γ.height) (hj : j ≤ βγ.height) (t u : R), commutes({γ, i, t}, {βγ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_γ_βγ]

-- /- Rewrite αβ⬝βγ as βγ⬝αβ. -/
-- @[group_reassoc]
-- theorem expr_αβ_βγ_as_βγ_αβ :
--   ∀ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ βγ.height) (t u : R), commutes({αβ, i, t}, {βγ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_αβ_βγ]

-- /-! ### Interchange theorems between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms -/

-- /- Interchange between ⁅α, βγ⁆ and ⁅αβ, γ⁆, "trading" a single degree j : Deg 1 and scalar u : R. -/
-- theorem Interchange {i j k : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
--     ∀ (t u v : R), ⁅ {α, i, t}, {βγ, j + k, u * v} ⁆ = ⁅ {αβ, i + j, t * u}, {γ, k, v} ⁆ := by
--   intro t u v
--   apply eq_comm_of_reorder_left
--   have hij : i + j ≤ αβ.height := by simp only [height] at *; omega
--   have hjk : j + k ≤ βγ.height := by simp only [height] at *; omega
--   -- phase I: push α to right
--   grw [expand_βγ_as_β_γ_β_γ hj hk,
--     expr_α_β_as_αβ_β_α hi hj,
--     expr_α_γ_as_γ_α hi hk,
--     expr_α_β_as_αβ_β_α hi hj,
--     mul_neg,
--     expr_α_γ_as_γ_α hi hk,
--     expr_β_γ_as_βγ_γ_β hj hk,
--     expr_β_αβ_as_αβ_β hj hij,
--     inv_of_β,
--     ← expr_γ_βγ_as_βγ_γ hk hjk,
--     ← expr_αβ_βγ_as_βγ_αβ hij hjk]
--   group
--   grw [expr_β_γ_as_βγ_γ_β hj hk,
--       ← expr_γ_βγ_as_βγ_γ hk hjk,
--       inv_of_αβ]
--   simp

-- /- Pass between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms (specializes `Interchange` to the case `u=1`). -/
-- theorem InterchangeTrans {i j k : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
--     ∀ (t u : R), ⁅ {α, i, t}, {βγ, (j + k), u} ⁆ = ⁅ {αβ, (i + j), t}, {γ, k, u} ⁆ := by
--   intro t u
--   nth_rewrite 1 [← one_mul u]
--   nth_rewrite 2 [← mul_one t]
--   rw [Interchange hi hj hk]

-- /- ⁅α,βγ⁆ forms depend only on product of coefficients. Applies `Interchange` twice. -/
-- theorem InterchangeRefl {i j k : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
--     ∀ (t u : R), ⁅ {α, i, 1 * (t * u)}, {βγ, (j + k), 1} ⁆ = ⁅ {α, i, t}, {βγ, (j + k), u} ⁆ := by
--   intro t u
--   nth_rewrite 2 [← mul_one u]
--   rw [Interchange hi hj hk]
--   rw [InterchangeTrans hi hj hk]
--   rw [one_mul]

-- /-! ### Commutator relations for (α,βγ) and (αβ,γ) via interchange relations -/

-- -- NS: Really need to figure out a more sane way to write this section.

-- -- height 0
-- private lemma comm_of_α_βγ_00 (t u : R) :
--     ⁅ {α, 0, t}, {βγ, 0, u} ⁆ = {αβγ, 0 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_αβγ (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]

-- private lemma comm_of_αβ_γ_00 (t u : R) :
--     ⁅ {αβ, 0, t}, {γ, 0, u} ⁆ = {αβγ, 0 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_α_βγ_00]

-- -- height 1
-- private lemma comm_of_α_βγ_01 (t u : R) :
--     ⁅ {α, 0, t}, {βγ, 1, u} ⁆ = {αβγ, 0 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_αβγ (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]

-- private lemma comm_of_αβ_γ_10 (t u : R) : ⁅ {αβ, 1, t}, {γ, 0, u} ⁆ = {αβγ, 1 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]
--   simp only [add_zero, comm_of_α_βγ_01, zero_add, one_mul]

-- private lemma comm_of_α_βγ_10 (t u : R) : ⁅ {α, 1, t}, {βγ, 0, u} ⁆ = {αβγ, 1 + 0, 1 * (t * u)} := by
--   rw [@InterchangeTrans _ _ 1 0 0 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_αβ_γ_10]

-- private lemma comm_of_αβ_γ_01 (t u : R) : ⁅ {αβ, 0, t}, {γ, 1, u} ⁆ = {αβγ, 0 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_α_βγ_01]

-- -- height 2
-- private lemma comm_of_α_βγ_11 (t u : R) :
--     ⁅ {α, 1, t}, {βγ, 1, u} ⁆ = {αβγ, 1 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_αβγ (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]

-- private lemma comm_of_αβ_γ_11 (t u : R) : ⁅ {αβ, 1, t}, {γ, 1, u} ⁆ = {αβγ, 1 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_α_βγ_11]

-- private lemma comm_of_α_βγ_02 (t u : R) : ⁅ {α, 0, t}, {βγ, 2, u} ⁆ = {αβγ, 0 + 2, 1 * (t * u)} := by
--   rw [@InterchangeTrans _ _ 0 1 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_αβ_γ_11]

-- private lemma comm_of_αβ_γ_20 (t u : R) : ⁅ {αβ, 2, t}, {γ, 0, u} ⁆ = {αβγ, 2 + 0, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_α_βγ_11]

-- -- height 3
-- private lemma comm_of_α_βγ_12 (t u : R) : ⁅ {α, 1, t}, {βγ, 2, u} ⁆ = {αβγ, 1 + 2, 1 * (t * u)} := by
--   rw [← @InterchangeRefl _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]
--   rw [← def_of_αβγ (by trivial) (1 * (t * u))]
--   simp only [split_3_into_1_2]
-- private lemma comm_of_αβ_γ_21 (t u : R) : ⁅ {αβ, 2, t}, {γ, 1, u} ⁆ = {αβγ, 2 + 1, 1 * (t * u)} := by
--   rw [← @InterchangeTrans _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]
--   rw [comm_of_α_βγ_12]

-- /- Commutator relation for α and βγ. -/
-- theorem comm_of_α_βγ : single_commutator_of_root_pair weakA3.pres_mk α βγ αβγ (1 : R) (by simp only [PosRootSys.height] at *; simp only [B3SmallPosRoot.height] at *) := by
--   intro i j hi hj t u
--   match i, j with
--   | 0, 0 => exact comm_of_α_βγ_00 t u
--   | 0, 1 => exact comm_of_α_βγ_01 t u
--   | 0, 2 => exact comm_of_α_βγ_02 t u
--   | 1, 0 => exact comm_of_α_βγ_10 t u
--   | 1, 1 => exact comm_of_α_βγ_11 t u
--   | 1, 2 => exact comm_of_α_βγ_12 t u

-- /- Commutator relation for αβ and γ. -/
-- theorem comm_of_αβ_γ : single_commutator_of_root_pair weakA3.pres_mk αβ γ αβγ (1 : R) (by simp only [PosRootSys.height] at *; simp only [B3SmallPosRoot.height] at *) := by
--   intro i j hi hj t u
--   match i, j with
--   | 0, 0 => exact comm_of_αβ_γ_00 t u
--   | 1, 0 => exact comm_of_αβ_γ_10 t u
--   | 2, 0 => exact comm_of_αβ_γ_20 t u
--   | 0, 1 => exact comm_of_αβ_γ_01 t u
--   | 1, 1 => exact comm_of_αβ_γ_11 t u
--   | 2, 1 => exact comm_of_αβ_γ_21 t u

-- /-! ### More rewriting theorems -/

-- /- Expand αβγ as α⬝βγ⬝α⬝βγ. -/
-- theorem expand_αβγ_as_α_βγ_α_βγ :
--     ∀ {i j : ℕ} (hi : i ≤ α.height) (hj : j ≤ βγ.height) (t u : R),
--       {αβγ, (i + j), (t * u)} = {α, i, t} * {βγ, j, u} * {α, i, (-t)} * {βγ, j, (-u)} := by
--   intro i j hi hj t u
--   rw [inv_of_α, inv_of_βγ, ← commutatorElement_def, ← one_mul (t * u), ← comm_of_α_βγ]

-- /- Expand αβγ as αβ⬝γ⬝αβ⬝γ. -/
-- theorem expand_αβγ_as_αβ_γ_αβ_γ :
--     ∀ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (t u : R),
--       {αβγ, (i + j), (t * u)} = {αβ, i, t} * {γ, j, u} * {αβ, i, (-t)} * {γ, j, (-u)} := by
--   intro i j hi hj t u
--   rw [inv_of_αβ, inv_of_γ, ← commutatorElement_def, ← one_mul (t * u), ← comm_of_αβ_γ]

-- /-! ### Commutators of αβγ with other roots -/

-- /- α and αβγ commute. -/
-- /- NS: One should be able to prove this quite simply:  simple proof: we know αβγ is expressible as a product of αβ's and γ's (expand_αβγ_as_αβ_γ_αβ_γ), and we know that α's
--    commute with αβ's (expr_α_αβ_as_αβ_α) and γ's (expr_α_γ_as_γ_α) -/
-- theorem comm_of_α_αβγ : trivial_commutator_of_root_pair R weakA3.pres_mk α αβγ := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose αβ.height γ.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_αβγ_as_αβ_γ_αβ_γ hj₁ hj₂,
--       expr_α_αβ_as_αβ_α hi hj₁,
--       expr_α_γ_as_γ_α hi hj₂,
--       expr_α_αβ_as_αβ_α hi hj₁,
--       expr_α_γ_as_γ_α hi hj₂]

-- /- γ and αβγ commute. -/
-- theorem comm_of_γ_αβγ : trivial_commutator_of_root_pair R weakA3.pres_mk γ αβγ := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose α.height βγ.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_αβγ_as_α_βγ_α_βγ hj₁ hj₂,
--     ← expr_α_γ_as_γ_α hj₁ hi,
--     expr_γ_βγ_as_βγ_γ hi hj₂,
--     ← expr_α_γ_as_γ_α hj₁ hi,
--     expr_γ_βγ_as_βγ_γ hi hj₂]

-- /- β and αβγ commute. -/
-- -- the only commutator proof where we have to do something 'interesting'
-- theorem comm_of_β_αβγ : trivial_commutator_of_root_pair R weakA3.pres_mk β αβγ := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose αβ.height γ.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_αβγ_as_αβ_γ_αβ_γ hj₁ hj₂,
--       expr_β_αβ_as_αβ_β hi hj₁,
--       expr_β_γ_as_γ_βγ_β hi hj₂,
--       expr_β_αβ_as_αβ_β hi hj₁,
--       expr_β_γ_as_βγ_γ_β hi hj₂,
--       ← expr_αβ_βγ_as_βγ_αβ hj₁ (by simp only [PosRootSys.height, height] at *; omega),
--       mul_neg, inv_of_βγ]
--   group

-- /- αβ and αβγ commute. -/
-- theorem comm_of_αβ_αβγ : trivial_commutator_of_root_pair R weakA3.pres_mk αβ αβγ := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose α.height βγ.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_αβγ_as_α_βγ_α_βγ hj₁ hj₂,
--     ← expr_α_αβ_as_αβ_α hj₁ hi,
--     expr_αβ_βγ_as_βγ_αβ hi hj₂,
--     ← expr_α_αβ_as_αβ_α hj₁ hi,
--     expr_αβ_βγ_as_βγ_αβ hi hj₂]

-- /- βγ and αβγ commute. -/
-- theorem comm_of_βγ_αβγ : trivial_commutator_of_root_pair R weakA3.pres_mk βγ αβγ := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose αβ.height γ.height j hj
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_αβγ_as_αβ_γ_αβ_γ hj₁ hj₂,
--     ← expr_αβ_βγ_as_βγ_αβ hj₁ hi,
--     ← expr_γ_βγ_as_βγ_γ hj₂ hi,
--     ← expr_αβ_βγ_as_βγ_αβ hj₁ hi,
--     ← expr_γ_βγ_as_βγ_γ hj₂ hi]

-- /- Rewrite α⬝αβγ as αβγ⬝α. -/
-- @[group_reassoc]
-- theorem expr_α_αβγ_as_αβγ_α :
--     ∀ {i j : ℕ} (hi : i ≤ α.height) (hj : j ≤ αβγ.height) (t u : R), commutes({α, i, t}, {αβγ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_α_αβγ]

-- /- Rewrite βγ⬝αβγ as αβγ⬝βγ. -/
-- @[group_reassoc]
-- theorem expr_βγ_αβγ_as_αβγ_βγ :
--     ∀ {i j : ℕ} (hi : i ≤ βγ.height) (hj : j ≤ αβγ.height) (t u : R), commutes({βγ, i, t}, {αβγ, j, u}) := by
--   intro i j hi hj t u
--   apply commutes_of_triv_comm
--   rw [comm_of_βγ_αβγ]

-- /- αβγ commutes with itself. -/
-- theorem mixed_commutes_of_αβγ : trivial_commutator_of_root_pair R weakA3.pres_mk αβγ αβγ := by
--   intro i j hi hj t u
--   apply triv_comm_of_commutes
--   let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose α.height βγ.height j (by trivial)
--   simp_rw [h_eq]
--   rw [← one_mul u]
--   grw [expand_αβγ_as_α_βγ_α_βγ hj₁ hj₂,
--     ← expr_α_αβγ_as_αβγ_α hj₁ hi,
--     ← expr_βγ_αβγ_as_αβγ_βγ hj₂ hi,
--     ← expr_α_αβγ_as_αβγ_α hj₁ hi,
--     ← expr_βγ_αβγ_as_αβγ_βγ hj₂ hi]

-- /- Linearity for αβγ. -/
-- theorem lin_of_αβγ : lin_of_root R weakA3.pres_mk αβγ := by
--   intro i hi t u
--   let ⟨ i₁, i₂, ⟨ h_eq, hi₁, hi₂ ⟩ ⟩ := decompose α.height βγ.height i (by trivial)
--   have h_eq' : i₁ + i₂ ≤ PosRootSys.height αβγ := by omega
--   simp_rw [h_eq]
--   nth_rewrite 1 [← mul_one t]
--   grw [expand_αβγ_as_α_βγ_α_βγ hi₁ hi₂,
--     expr_βγ_αβγ_as_αβγ_βγ hi₂ h_eq',
--     expr_α_αβγ_as_αβγ_α hi₁ h_eq',
--     expr_βγ_αβγ_as_αβγ_βγ hi₂ h_eq']
--   nth_rewrite 1 [← mul_one u]
--   grw [expand_αβγ_as_α_βγ_α_βγ hi₁ hi₂, lin_of_α]
--   nth_rewrite 1 [inv_of_βγ]
--   group

--   rw [mul_assoc _ {α, i₁, -u}, lin_of_α, ← neg_add u t, add_comm u t, ← expand_αβγ_as_α_βγ_α_βγ hi₁ hi₂, mul_one]

-- end A3Proof
