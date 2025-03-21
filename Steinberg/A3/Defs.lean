/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.Defs.GradedPartialChevalleyGroup
import Steinberg.Defs.PartialChevalleyGroup
import Steinberg.Defs.DecomposeFixed

import Mathlib.Tactic.DeriveFintype

import Steinberg.Macro.Attr

/-!

  File dox.

-/

namespace Steinberg.A3

open Steinberg PartialChevalley GradedPartialChevalley GradedChevalleyGenerator PartialChevalleySystem

/-! # The A3 positive root system -/

inductive A3PosRoot
  | α | β | γ | αβ | βγ | αβγ
deriving Fintype, DecidableEq

namespace A3PosRoot

@[reducible, height_simps]
def height : A3PosRoot → Nat
  | α | β | γ => 1
  | αβ | βγ => 2
  | αβγ => 3

def toString : A3PosRoot → String
  | α => "α"
  | β => "β"
  | γ => "γ"
  | αβ => "α+β"
  | βγ => "β+γ"
  | αβγ => "α+β+γ"

instance instPosRootSys : PositiveRootSystem A3PosRoot where
  height := height
  toString := toString

instance instCoeNat : Coe A3PosRoot Nat where
  coe r := height r

end A3PosRoot

open A3PosRoot

variable {R : Type TR} [Ring R]

/-! # Definition of the 'weak' A3 graded group -/

/-! ## Defining the 'weak' positive root system -/

abbrev present_roots : Set (A3PosRoot) :=
  {α, β, γ, αβ, βγ}

abbrev trivial_commutator_pairs : Set (A3PosRoot × A3PosRoot) :=
  {(α, γ), (α, αβ), (β, αβ), (β, βγ), (γ, βγ)}

abbrev single_commutator_pairs : Set (SingleSpanRootPair A3PosRoot) :=
  {⟨ α, β, αβ, 1, (by ht)⟩, ⟨β, γ, βγ, 1, (by ht)⟩}

abbrev weakA3System := PartialChevalleySystem.mk
  present_roots
  trivial_commutator_pairs
  single_commutator_pairs
  ∅
  (by simp only [trivial_commutator_pairs, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; tauto)
  (by simp only [single_comm_root_pairs, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; tauto)
  (by simp only [double_comm_root_pairs, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; tauto)

/-! ## Lifted relations -/

def rels_of_nonhomog_lift_of_comm_of_αβ_βγ :=
  { ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
      {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} ⁆
    | (t₁ : R) (t₀ : R) (u₁ : R) (u₀ : R) (v₁ : R) (v₀ : R) }

def lifted_sets (R : Type TR) [Ring R] : Set (Set (FreeGroup (GradedChevalleyGenerator A3PosRoot R))) :=
  { rels_of_nonhomog_lift_of_comm_of_αβ_βγ }

/-! ## Definition for missing root (αβγ) -/

def weak_define (R : Type TR) [Ring R] (g : GradedChevalleyGenerator A3PosRoot R) : FreeGroup (GradedChevalleyGenerator A3PosRoot R) :=
  let ⟨ ζ, i, hi, t ⟩ := g;
  match ζ with
  | αβγ => ⁅ {α,(split_3_into_1_2 i (by ht)).1, g.t}'(correct_of_split_3_into_1_2 i (by ht)).1,
    {βγ, (split_3_into_1_2 i (by ht)).2, 1}'(correct_of_split_3_into_1_2 i (by ht)).2.1 ⁆
  | ζ => FreeGroup.of g

theorem weak_define_of_present (R : Type TR) [Ring R] :
  ∀ {g : GradedChevalleyGenerator A3PosRoot R}, g.ζ ∈ weakA3System.present_roots → weak_define R g = FreeGroup.of g := by
  intro g h_g_in_present
  rcases g with ⟨ ζ, i, hi, t ⟩
  cases ζ
  all_goals simp only [weak_define] -- this will close all present roots
  all_goals ( -- this will close the remaining (nonpresent) roots
    simp only [present_roots] at h_g_in_present
    contradiction
  )

theorem weak_define_is_projection (R : Type TR) [Ring R] :
  ∀ {g : GradedChevalleyGenerator A3PosRoot R}, (FreeGroup.lift (weak_define R)) (weak_define R g) = weak_define R g := by
  intro g
  rcases g with ⟨ ζ, i, hi, t ⟩
  cases ζ
  all_goals simp only [weak_define, FreeGroup.lift.of, map_commutatorElement]


def weakA3 (R : Type TR) [Ring R] := GradedPartialChevalleyGroup.mk
  weakA3System
  (lifted_sets R)
  (weak_define R)
  (weak_define_of_present R)
  (weak_define_is_projection R)

/-! # Definition of the 'full' A3 ungraded and graded groups -/

abbrev full_present_roots : Set (A3PosRoot) :=
  present_roots ∪ {αβγ}

abbrev full_trivial_commutator_pairs : Set (A3PosRoot × A3PosRoot) :=
  trivial_commutator_pairs ∪ {(αβ, βγ), (α, αβγ), (β, αβγ), (γ, αβγ), (αβ, αβγ), (βγ, αβγ)}

abbrev full_single_commutator_pairs : Set (SingleSpanRootPair A3PosRoot) :=
  (single_commutator_pairs) ∪ {⟨ α, βγ, αβγ, 1, (by ht)⟩, ⟨αβ, γ, αβγ, 1, (by ht)⟩}

theorem all_root_pairs_have_relation : all_pairs A3PosRoot full_trivial_commutator_pairs full_single_commutator_pairs ∅ := by
    intro ζ η
    cases ζ <;> cases η
    all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, Set.union_insert, Set.union_singleton,
      Set.mem_insert_iff, Prod.mk.injEq, and_self, and_false, Set.mem_singleton_iff, or_self,
      exists_eq_or_imp, or_false, exists_eq_left, or_true, Set.mem_empty_iff_false, false_and,
      exists_false, imp_self, not_true_eq_false]

abbrev fullA3System := PartialChevalleySystem.mk_full A3PosRoot
  full_present_roots
  full_trivial_commutator_pairs
  full_single_commutator_pairs
  ∅
  (by decide)
  all_root_pairs_have_relation

def fullA3 (R : Type TR) [Ring R] := @PartialChevalleyGroup.mk A3PosRoot _ R _ fullA3System
def fullA3Graded (R : Type TR) [Ring R] := GradedPartialChevalleyGroup.full_mk A3PosRoot R fullA3System

/-! # Notation and macros -/

/- Instantiate the `declare_thms` macros from `PartialChevalley.lean`. -/

-- CC: TODO: Make this a macro to declare all at once for A3.
--     Something like: `declare_thms A3 weakA3 R`

macro "declare_A3_triv_expr_thm" R:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_expr_thm weakA3 $R $r₁ $r₂)

macro "declare_A3_triv_comm_of_root_pair_thms" R:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_comm_of_root_pair_thms weakA3 $R $r₁ $r₂)

macro "declare_A3_single_expr_thms" R:term:arg r₁:term:arg r₂:term:arg r₃:term:arg : command =>
  `(command| declare_single_expr_thms weakA3 $R $r₁ $r₂ $r₃ 1)

macro "declare_A3_single_comm_of_root_pair_thms" R:term:arg r₁:term:arg r₂:term:arg r₃:term:arg : command =>
  `(command| declare_single_comm_of_root_pair_thms weakA3 $R $r₁ $r₂ $r₃ 1)

macro "declare_A3_lin_id_inv_thms" R:term:arg root:term:arg : command =>
  `(command| declare_lin_id_inv_thms weakA3 $R $root)

macro "declare_A3_mixed_expr_thm" R:term:arg r:term:arg : command =>
  `(command| declare_mixed_expr_thm weakA3 $R $r)

macro "declare_A3_mixed_comm_thms" R:term:arg r:term:arg : command =>
  `(command| declare_mixed_comm_thms weakA3 $R $r)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "⸨" ζ ", " i ", " t "⸩" =>
  (weakA3 R).pres_mk {ζ, i, t}

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "⸨" ζ ", " i ", " t "⸩'" h =>
  (weakA3 R).pres_mk ({ζ, i, t}'h)

section forallNotation

set_option hygiene false

scoped notation "forall_i_t" h:max "," e =>
  ∀ ⦃i : ℕ⦄ (hi : i ≤ h) (t : R), e

scoped notation "forall_ij_t" h₁:max h₂:max "," e =>
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (t : R), e

scoped notation "forall_ij_tu" h₁:max h₂:max "," e =>
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (t u : R), e

scoped notation "forall_ik_tuv" h₁:max h₂:max "," e =>
  ∀ ⦃i k : ℕ⦄ (hi : i ≤ h₁) (hk : k ≤ h₂) (t u v : R), e

scoped notation "forall_ijk_tu" h₁:max h₂:max h₃:max "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (hk : k ≤ h₃) (t u : R), e

scoped notation "forall_ijk_tuv" h₁:max h₂:max h₃:max "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (hk : k ≤ h₃) (t u v : R), e

scoped notation "forall_ijk_tuv" "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) (t u v : R), e

end forallNotation

end Steinberg.A3
