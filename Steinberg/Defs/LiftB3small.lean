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
import Steinberg.Defs.ReflDeg

import Steinberg.Macro.Group

import Steinberg.Upstream.FreeGroup
import Steinberg.Upstream.PresentedGroup

namespace Steinberg

open Steinberg.Macro

variable {R : Type TR} [Field R]

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

instance : PosRootSys B3SmallPosRoot where
  height := height
  toString := toString

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

/-! # These are the self-commutation relations -/
abbrev mixed_commutes_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}

abbrev lin_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}

abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3SmallPosRoot R) :=
    {⟨β, ψ, βψ, β2ψ, 1, 1, (by exact rfl), (by exact rfl)⟩}

-- lifted commutator of βψ and ψω
def nonhomog_sets (R : Type TR) [Field R] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot R)) := {
  rels_of_nonhomog_lift_of_comm_of_βψ_ψω
}

-- definition of βψω
def def_sets (R : Type TR) [Field R] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot R)) := {
  rels_of_def_of_βψω
}

def weakB3Small := WeakChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  double_commutator_pairs
  mixed_commutes_roots
  lin_roots
  (nonhomog_sets R)
  (def_sets R)

abbrev weakB3Small_rels (R : Type TR) [Field R] := @weakB3Small.all_rels B3SmallPosRoot _ R _

abbrev WeakChevalleyB3SmallGroup (R : Type TR) [Field R] := PresentedGroup (@weakB3Small.all_rels B3SmallPosRoot _ R _)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" => weakB3Small.pres_mk (free_mk_mk ζ i (by (try simp only [PosRootSys.height] at *; try simp only [B3SmallPosRoot.height] at *; first | trivial | omega)) t)

section UnpackingPresentation

theorem comm_of_β_βψ : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk β βψ :=
  weakB3Small.trivial_commutator_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_β2ψ : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk β β2ψ :=
  weakB3Small.trivial_commutator_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_β2ψ : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk ψ β2ψ :=
  weakB3Small.trivial_commutator_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_βψ_β2ψ : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψ β2ψ :=
  weakB3Small.trivial_commutator_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_β_ω : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk β ω :=
  weakB3Small.trivial_commutator_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_ψω : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk ψ ψω :=
  weakB3Small.trivial_commutator_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ω_ψω : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk ω ψω :=
  weakB3Small.trivial_commutator_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_ω : single_commutator_of_root_pair weakB3Small.pres_mk ψ ω ψω (2 : R) (by rfl) :=
  weakB3Small.single_commutator_helper ψ ω ψω (2 : R) (by rfl) (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_βψ : single_commutator_of_root_pair weakB3Small.pres_mk ψ βψ β2ψ (2 : R) (by rfl) :=
  weakB3Small.single_commutator_helper ψ βψ β2ψ (2 : R) (by rfl) (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Linearity theorems for specific roots -/

theorem lin_of_β : lin_of_root (R := R) weakB3Small.pres_mk β :=
  weakB3Small.lin_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_ψ : lin_of_root (R := R) weakB3Small.pres_mk ψ :=
  weakB3Small.lin_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_ω : lin_of_root (R := R) weakB3Small.pres_mk ω :=
  weakB3Small.lin_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_βψ : lin_of_root (R := R) weakB3Small.pres_mk βψ :=
  weakB3Small.lin_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_ψω : lin_of_root (R := R) weakB3Small.pres_mk ψω :=
  weakB3Small.lin_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem lin_of_β2ψ : lin_of_root (R := R) weakB3Small.pres_mk β2ψ :=
  weakB3Small.lin_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Mixed-degree theorem for specific roots -/

theorem mixed_commutes_of_βψ : mixed_commutes_of_root (R := R) weakB3Small.pres_mk βψ :=
  weakB3Small.mixed_commutes_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_ψω : mixed_commutes_of_root (R := R) weakB3Small.pres_mk ψω :=
  weakB3Small.mixed_commutes_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_β2ψ : mixed_commutes_of_root (R := R) weakB3Small.pres_mk β2ψ :=
  weakB3Small.mixed_commutes_helper (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Double commutator theorem -/

theorem comm_of_β_ψ : double_commutator_of_root_pair (R := R) weakB3Small.pres_mk β ψ βψ β2ψ (1 : R) (1 : R) (by rfl) (by rfl) :=
  weakB3Small.double_commutator_helper β ψ βψ β2ψ (1 : R) (1 : R) (by rfl) (by rfl) (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Nonhomogeneous lift -/
theorem nonhomog_lift_of_comm_of_βψ_ψω :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R),
    ⁅ {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀}
    , {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} ⁆
    = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply WeakChevalley.helper
  apply weakB3Small.nonhomog_helper rels_of_nonhomog_lift_of_comm_of_βψ_ψω
  · simp only [weakB3Small, nonhomog_sets, Set.mem_singleton_iff]
  · exists t₁, t₀, u₁, u₀, v₁, v₀

/-! ### Definition of missing root -/
theorem def_of_βψω :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ βψω.height) (t : R),
    ⁅ weakB3Small.pres_mk (free_mk_mk β (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 t)
    , weakB3Small.pres_mk (free_mk_mk ψω (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 1) ⁆
    = {βψω, i, t} := by
  intro t i hi
  apply WeakChevalley.helper
  apply weakB3Small.def_helper rels_of_def_of_βψω
  · simp only [weakB3Small, def_sets, Set.mem_singleton_iff]
  · exists t, i, hi

@[group_reassoc]
theorem expr_βψ_βψ_as_βψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ βψ.height) (t u : R), commutes({βψ, i, t}, {βψ, j, u}) := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mp
  rw [mixed_commutes_of_βψ]

@[group_reassoc]
theorem expr_ψω_ψω_as_ψω_ψω :
    ∀ {i j : ℕ} (hi : i ≤ ψω.height) (hj : j ≤ ψω.height) (t u : R), commutes({ψω, i, t}, {ψω, j, u}) := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mp
  rw [mixed_commutes_of_ψω]

theorem refl_of_nonhomog :
  ∀ S ∈ nonhomog_sets R,
    ∀ r ∈ S, weakB3Small.pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [nonhomog_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_βψ_ψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, rfl ⟩
  simp only [map_mul, map_commutatorElement, free_mk_mk, FreeGroup.map.of, refl_deg_of_gen, PosRootSys.height, height]
  simp_arith
  repeat rw [← free_mk_mk]
  rw [add_comm (t₁ * u₀), add_comm (u₁ * v₀)]
  rw [expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω, mul_assoc, mul_assoc,
    expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω, ← mul_assoc, ← mul_assoc,
    expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω]
  exact nonhomog_lift_of_comm_of_βψ_ψω t₀ t₁ u₀ u₁ v₀ v₁
  all_goals trivial

-- def relations are preserved under reflection
theorem refl_of_def : ∀ S ∈ def_sets R, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  simp only [def_sets, Set.mem_singleton_iff, forall_eq, rels_of_def_of_βψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ i, hi, t, rfl ⟩
  simp only [map_mul, map_commutatorElement, split_3_into_1_2]
  exists (βψω.height - i), (by omega), t
  split
  all_goals (simp only; congr)

theorem b3small_valid : ReflDeg.refl_valid (R := R) weakB3Small :=
  ⟨refl_of_nonhomog, refl_of_def⟩

end UnpackingPresentation /- section -/

/-! ### Identity theorems : 8.25 - 8.30 -/

/-! # 8.25 -/
theorem id_of_β : id_of_root (R := R) weakB3Small.pres_mk β :=
  id_of_lin_of_root lin_of_β

/-! # 8.26 -/
theorem id_of_ψ : id_of_root (R := R) weakB3Small.pres_mk ψ :=
  id_of_lin_of_root lin_of_ψ

/-! # 8.27 -/
theorem id_of_ω : id_of_root (R := R) weakB3Small.pres_mk ω :=
  id_of_lin_of_root lin_of_ω

/-! # 8.28 -/
theorem id_of_βψ : id_of_root (R := R) weakB3Small.pres_mk βψ :=
  id_of_lin_of_root lin_of_βψ

/-! # 8.29 -/
theorem id_of_ψω : id_of_root (R := R) weakB3Small.pres_mk ψω :=
  id_of_lin_of_root lin_of_ψω

/-! # 8.30 -/
theorem id_of_β2ψ : id_of_root (R := R) weakB3Small.pres_mk β2ψ :=
  id_of_lin_of_root lin_of_β2ψ


/-! ### Inverse theorems - 8.31 - 8.36 -/

/-! # 8.31 -/
theorem inv_of_β : inv_of_root (R := R) weakB3Small.pres_mk β :=
  inv_of_lin_of_root lin_of_β

/-! # 8.32 -/
theorem inv_of_ψ : inv_of_root (R := R) weakB3Small.pres_mk ψ :=
  inv_of_lin_of_root lin_of_ψ

/-! # 8.33 -/
theorem inv_of_ω : inv_of_root (R := R) weakB3Small.pres_mk ω :=
  inv_of_lin_of_root lin_of_ω

/-! # 8.34 -/
theorem inv_of_βψ : inv_of_root (R := R) weakB3Small.pres_mk βψ :=
  inv_of_lin_of_root lin_of_βψ

/-! # 8.35 -/
theorem inv_of_ψω : inv_of_root (R := R) weakB3Small.pres_mk ψω :=
  inv_of_lin_of_root lin_of_ψω

/-! # 8.36 -/
theorem inv_of_β2ψ : inv_of_root (R := R) weakB3Small.pres_mk β2ψ  :=
  inv_of_lin_of_root lin_of_β2ψ


/-! ### 8.37 -/

theorem expand_βψ_as_ψ_β_ψ_β_ψ :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
    {βψ, i + j, 2 * (t * u)} =
    {ψ, j, (-u)} * {β, i, t} * {ψ, j, 2 * u} * {β, i, (-t)} * {ψ, j, (-u)} := by
    intro i j hi hj t u
    -- start with relation 8.2
    have base := comm_of_β_ψ (R := R) hi hj t (2 * u)
    -- commute β + 2 ψ and β + ψ
    rw [comm_left, comm_of_βψ_β2ψ, one_mul] at base
    have this : (1 * (t * (2 * u * (2 * u)))) = 2 * (u * (2 * (t * u))) := by group
    rw [this] at base
    have this : (1 * (t * (2 * u))) = 2 * (t * u) := by group
    rw [this] at base
    -- replace β + 2 ψ with a commutator of ψ and β + ψ elements
    have this : i + 2 * j = j + (i + j) := by group
    simp only [this] at base
    have this := @comm_of_ψ_βψ (R := R) (by infer_instance) j (i + j) hj (
      by
      simp only [PosRootSys.height, height] at hi
      simp only [PosRootSys.height, height] at hj
      simp only [PosRootSys.height, height]
      omega
    ) u (2 * (t * u))
    rw [← this] at base
    -- expand the commutator, and cancel with the β + ψ element on the right
    conv at base =>
      rhs; rw [commutatorElement_def]
    rw [inv_mul_cancel_right] at base
    -- expanding the commutator on the LHS and conjugating by ψ elements gives the relation
    rw [commutatorElement_def] at base
    have base := congrArg (HMul.hMul (weakB3Small.pres_mk (free_mk_mk ψ j hj u))⁻¹) base
    conv at base =>
      rhs
      rw [mul_assoc, inv_mul_cancel_left]
    have base := congrArg (fun x => HMul.hMul x (weakB3Small.pres_mk (free_mk_mk ψ j hj u))) base
    dsimp at base
    conv at base =>
      rhs
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [← inv_of_β, ← inv_of_ψ, ← inv_of_ψ] at base
    conv at base =>
      lhs
      rw [mul_assoc, mul_assoc, lin_of_ψ (R := R) hj (-(2 * u)) u]
    have this : -(2 * u) + u = -u := by group
    rw [this] at base
    exact id (Eq.symm base)

/-! ### 8.38 -/

theorem expand_β2ψ_as_ψ_βψ_ψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ 2 * ψ.height) (t u : R),
      {β2ψ, i + j, 2 * (t * u)} = {ψ, i, t} * {βψ, j, u} * {ψ, i, (-t)} *
      {βψ, j, (-u)} := by sorry

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
  sorry

theorem comm_of_βψ_ψω : trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψ ψω := by
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
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψ ψω := by sorry

/-! ### Establishing βψω -/

-- 8.43

theorem trivial_comm_of_β2ψ_ψω :
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk β2ψ ψω := by sorry

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
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψω ω := by sorry

-- 8.49

theorem trivial_comm_of_βψω_β :
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψω β := by sorry

-- 8.50

theorem trivial_comm_of_βψω_ψ :
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψω ψ := by sorry

-- 8.51

theorem trivial_comm_of_βψω_ψω :
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψω ψω := by sorry

-- 8.52

theorem trivial_comm_of_βψω_βψ :
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψω βψ := by sorry

-- 8.53

theorem trivial_comm_of_βψω_β2ψ :
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk βψω β2ψ := by sorry

-- 8.54

theorem self_comm_of_βψω :
    mixed_commutes_of_root (R := R) weakB3Small.pres_mk βψω := by sorry

-- 8.55

theorem lin_of_βψω : lin_of_root (R := R) weakB3Small.pres_mk βψω := by sorry

-- 8.56

theorem inv_of_βψω : inv_of_root (R := R) weakB3Small.pres_mk βψω := by sorry

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
    trivial_commutator_of_root_pair (R := R) weakB3Small.pres_mk β2ψ ω := by sorry
