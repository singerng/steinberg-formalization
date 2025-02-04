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

-- abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3SmallPosRoot R) :=
--     {⟨β, ψ, βψ, β2ψ, 1, 1, (by exact rfl), (by exact rfl)⟩}

/-! # These are the self-commutation relations -/
abbrev mixed_commutes_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}

abbrev lin_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}

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
  -- double_commutator_pairs
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
