/-

LICENSE goes here.

-/

import Steinberg.Defs.PartialChevalleyGroup
import Steinberg.Defs.GradedPartialChevalleyGroup
import Steinberg.Defs.ReflDeg
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp

/-!

  File dox.

-/

namespace Steinberg.B3Large

open PartialChevalley GradedPartialChevalley GradedChevalleyGenerator PartialChevalleySystem ReflDeg

/-! # The B3-large positive root system -/

inductive B3LargePosRoot
  | α | β | ψ | αβ | βψ | β2ψ | αβψ | αβ2ψ | α2β2ψ
deriving Fintype, DecidableEq, Inhabited

namespace B3LargePosRoot

@[reducible, height_simps]
def height : B3LargePosRoot → Nat
  | α | β | ψ => 1
  | αβ | βψ => 2
  | β2ψ | αβψ => 3
  | αβ2ψ => 4
  | α2β2ψ => 5

def toString : B3LargePosRoot → String
  | α => "α"
  | β => "β"
  | ψ => "ψ"
  | αβ => "α+β"
  | βψ => "β+ψ"
  | β2ψ => "β+2ψ"
  | αβψ => "α+β+ψ"
  | αβ2ψ => "α+β+2ψ"
  | α2β2ψ => "α+2β+2ψ"

instance : PositiveRootSystem B3LargePosRoot where
  height := height
  toString := toString

instance instCoeNat : Coe B3LargePosRoot Nat where
  coe r := r.height

end B3LargePosRoot

open B3LargePosRoot

variable {F : Type TR} [Field F]

/-! # Lifting -/

def hom_lift (i j k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : F) (g : ChevalleyGenerator B3LargePosRoot F)
  : GradedChevalleyGenerator B3LargePosRoot F :=
  match g.ζ with
  | α => GradedChevalleyGenerator.mk α i (by ht) (g.t * t)
  | β => GradedChevalleyGenerator.mk β j (by ht) (g.t * u)
  | ψ => GradedChevalleyGenerator.mk ψ k (by ht) (g.t * v)
  | αβ => GradedChevalleyGenerator.mk αβ (i+j) (by ht) (g.t * t * u)
  | βψ => GradedChevalleyGenerator.mk βψ (j+k) (by ht) (g.t * u * v)
  | β2ψ => GradedChevalleyGenerator.mk β2ψ (j+2*k) (by ht) (g.t * u * v^2)
  | αβψ => GradedChevalleyGenerator.mk αβψ (i+j+k) (by ht) (g.t * t * u * v)
  | αβ2ψ => GradedChevalleyGenerator.mk αβ2ψ (i+j+2*k) (by ht) (g.t * t * u * v^2)
  | α2β2ψ => GradedChevalleyGenerator.mk α2β2ψ (i+2*j+2*k) (by ht) (g.t * t * u^2 * v^2)

def hom_lift_set (r : FreeGroup (ChevalleyGenerator B3LargePosRoot F)) :=
  { FreeGroup.map (hom_lift i j k hi hj hk t u v) r | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

theorem eq_of_hom_lift_eq
  (i j k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
  (i' j' k' : ℕ) (hi' : i' ≤ α.height) (hj' : j' ≤ β.height) (hk' : k' ≤ ψ.height) (t u v : F)
  (hii' : i = i') (hjj' : j = j') (hkk' : k = k') : hom_lift i j k hi hj hk t u v = hom_lift i' j' k' hi' hj' hk' t u v := by
  ext
  simp only [hii', hjj', hkk']

/-! # Definition of the 'weak' B3-large graded group -/

/-! ## Defining the 'weak' positive root system -/

-- relations 8.69, 8.70, 8.71, 8.72, 8.73, 8.74
abbrev present_roots : Set B3LargePosRoot :=
  {α, β, ψ, αβ, βψ, β2ψ}

-- relations 8.60, 8.61, 8.62, 8.64, 8.65, 8.67, 8.68
abbrev trivial_commutator_pairs : Set (B3LargePosRoot × B3LargePosRoot) :=
  {(α, αβ), (β, αβ), (α, ψ), (β, βψ), (β, β2ψ), (ψ, β2ψ), (βψ, β2ψ)}

-- relations 8.59, 8.66
abbrev single_commutator_pairs : Set (SingleSpanRootPair B3LargePosRoot)
  := {⟨α, β, αβ, 1, (by ht)⟩, ⟨ψ, βψ, β2ψ, 2, (by ht)⟩}

-- relation 8.63
abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3LargePosRoot) :=
  {⟨β, ψ, βψ, β2ψ, 1, 1, rfl, rfl⟩}

abbrev weakB3LargeSystem := PartialChevalleySystem.mk
  present_roots
  trivial_commutator_pairs
  single_commutator_pairs
  double_commutator_pairs
  (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, reduceCtorEq, or_self,
    or_false, or_true, and_self, forall_eq])
  (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, reduceCtorEq, or_self,
    or_false, or_true, and_self, forall_eq])
  (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, reduceCtorEq, or_self,
    or_false, or_true, and_self, forall_eq])

-- Relation 8.81
def rels_of_nonhomog_lift_of_comm_of_αβ_βψ :=
  { ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
      {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} ⁆
    | (t₁ : F) (t₀ : F) (u₁ : F) (u₀ : F) (v₁ : F) (v₀ : F) }

-- Relation 8.82
def rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ :=
  { ⁅ {α, 1, t₁} * {α, 0, t₀},
      ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
        {β2ψ, 3, u₁ * v₁^2} * {β2ψ, 2, u₀ * v₁^2 + 2 * u₁ * v₀ * v₁}
          * {β2ψ, 1, u₁ * v₀^2 + 2 * u₀ * v₀ * v₁} * {β2ψ, 0, u₀ * v₀^2} ⁆ ⁆
    | (t₁ : F) (t₀ : F) (u₁ : F) (u₀ : F) (v₁ : F) (v₀ : F) }

section homog_rels
open ChevalleyGenerator

-- Relation 8.83
def base_rel_of_hom_lift_of_interchange_of_αβψ :=
  ({ψ, ((-1/2):F)} * {αβ, (1:F)} * {ψ, (1:F)} * {αβ, -(1:F)} * {ψ, ((-1 / 2):F)}
    * ({βψ, ((-1/2):F)} * {α, (1:F)} * ({βψ, (1:F)}) * {α, -(1:F)} * {βψ, -(1/2:F)})⁻¹)

-- Relation 8.84
def base_rel_of_hom_lift_of_doub_of_αβψ :=
  ({ψ, ((-1 / 2):F)} * {αβ, (1:F)} * {ψ, (1:F)} * {αβ, -(1:F)} * {ψ, ((-1 / 2):F)} * {ψ, ((-1 / 2):F)} *
    {αβ, (1:F)} * {ψ, (1:F)} * {αβ, -(1:F)} * {ψ, ((-1 / 2):F)}
    * ({ψ, -(1:F)} * {αβ, (1:F)} * {ψ, (2:F)} * {αβ, -(1:F)} * {ψ, -(1:F)})⁻¹)

-- Relation 8.85
def base_rel_of_hom_lift_of_interchange_of_αβ2ψ :=
  (⁅ {ψ, ((-1 / 2):F)} * {αβ, (1:F)} *
      {ψ, (1:F)} * {αβ, -(1:F)} *
      {ψ, ((-1 / 2):F)}, {ψ, (1:F)} ⁆
    * ⁅ {α, (1:F)},
        {β2ψ, -(2:F)} ⁆⁻¹)

-- Relation 8.86
def base_rel_of_hom_lift_of_comm_of_βψ_α_β2ψ :=
  (⁅ {βψ, (1:F)},
      ⁅ {α, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆)

-- Relation 8.87a
def base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_a :=
  (⁅ {α, (1:F)},
      {β2ψ, (1:F)} ⁆
    * ⁅ {α, -(1:F)},
        {β2ψ, -(1:F)}⁆⁻¹)

-- Relation 8.87b
def base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_b :=
  (⁅ {α, (1:F)}, {β2ψ, (1:F)} ⁆ * ⁅ {α, (1:F)}, {β2ψ, -(1:F)} ⁆)

-- Relation 8.87c
def base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_c :=
  (⁅ {α, (1:F)}, {β2ψ, (1:F)} ⁆ * ⁅ {α, (1:F)}, {β2ψ, (1:F)} ⁆ * ⁅ {α, (1:F)}, {β2ψ, (2:F)} ⁆⁻¹)

-- Relation 8.88
def base_rel_of_hom_lift_of_comm_of_β2ψ_αβψ :=
  (⁅ {β2ψ, (1:F)},
      {ψ, ((-1 / 2):F)} *
      {αβ, (1:F)} *
      {ψ, (1:F)} *
      {αβ, -(1:F)} *
      {ψ, ((-1 / 2):F)} ⁆)

-- Relation 8.89a
def base_rel_of_hom_lift_of_interchange_of_α2β2ψ_a :=
  (⁅ {αβ, (1:F)},
      {β2ψ, (2:F)} ⁆
    * ⁅ {ψ, ((-1 / 2):F)} *
        {αβ, (1:F)} *
        {ψ, (1:F)} *
        {αβ, -(1:F)} *
        {ψ, ((-1 / 2):F)},
        {βψ, (1:F)} ⁆⁻¹)

-- Relation 8.89b
def base_rel_of_hom_lift_of_interchange_of_α2β2ψ_b :=
  (⁅ {ψ, ((-1 / 2):F)} *
      {αβ, (1:F)} *
      {ψ, (1:F)} *
      {αβ, -(1:F)} *
      {ψ, ((-1 / 2):F)},
      {βψ, (1:F)} ⁆
    * ⁅ ⁅ {α, (1:F)},
          {β2ψ, (2:F)} ⁆,
        {β, (1:F)} ⁆⁻¹)

-- Relation 8.90
def base_rel_of_hom_lift_of_comm_of_ψ_αβ_β2ψ :=
  (⁅ {ψ, (1:F)},
      ⁅ {αβ, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆)

-- Relation 8.91a (s = 1)
def base_rel_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_a :=
  (⁅ {αβ, (1:F)},
      ⁅ {αβ, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆)

-- Relation 8.91b (s = -1)
def base_rel_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_b :=
  (⁅ {αβ, (1:F)},
      ⁅ {αβ, -(1:F)},
        {β2ψ, (1:F)} ⁆ ⁆)

-- Relation 8.92a
def base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a :=
  (⁅ {αβ, (1:F)},
      {β2ψ, (1:F)} ⁆
    * ⁅ {αβ, -(1:F)},
        {β2ψ, -(1:F)} ⁆⁻¹)

-- Relation 8.92b
def base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b :=
  (⁅ {αβ, (1:F)},
      {β2ψ, (1:F)} ⁆
    * ⁅ {αβ, -(1:F)},
        {β2ψ, (1:F)} ⁆)

-- Relation 8.92c
def base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c :=
  (⁅ {αβ, (1:F)},
      {β2ψ, (1:F)} ⁆
    * ⁅ {αβ, (1:F)},
        {β2ψ, (1:F)} ⁆
    * ⁅ {αβ, (2:F)},
        {β2ψ, (1:F)} ⁆⁻¹)

-- Relation 8.93a
def base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a :=
  (⁅ {β, (1:F)},
      ⁅ {α, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆
    * ⁅ {β, (-1:F)},
        ⁅ {α, -(1:F)},
          {β2ψ, (1:F)} ⁆ ⁆⁻¹)

-- Relation 8.93b
def base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b :=
  (⁅ {β, (1:F)},
      ⁅ {α, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆
    * ⁅ {β, (-1:F)},
        ⁅ {α, (1:F)},
          {β2ψ, (1:F)} ⁆ ⁆)

-- Relation 8.93c
def base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c :=
  (⁅ {β, (1:F)},
      ⁅ {α, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆
    * ⁅ {β, (1:F)},
        ⁅ {α, (1:F)},
          {β2ψ, (1:F)} ⁆ ⁆
    * ⁅ {β, (2:F)},
        ⁅ {α, (1:F)},
          {β2ψ, (1:F)} ⁆ ⁆⁻¹)

-- Relation 8.94
def base_rel_of_hom_lift_of_comm_of_βψ_αβ2ψ :=
  (⁅ {βψ, (1:F)},
      ⁅ {α, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆)

-- Relation 8.95
def base_rel_of_hom_lift_of_comm_of_β2ψ_αβ2ψ :=
  (⁅ {β2ψ, (1:F)},
      ⁅ {α, (1:F)},
        {β2ψ, (1:F)} ⁆ ⁆)

end homog_rels

def nonhom_lifted_sets (F : Type TF) [Field F] : Set (Set (FreeGroup (GradedChevalleyGenerator B3LargePosRoot F))) := {
  rels_of_nonhomog_lift_of_comm_of_αβ_βψ, rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ}

def hom_lifted_sets (F : Type TF) [Field F] : Set (Set (FreeGroup (GradedChevalleyGenerator B3LargePosRoot F))) :=
  hom_lift_set '' {
  base_rel_of_hom_lift_of_interchange_of_αβψ, base_rel_of_hom_lift_of_doub_of_αβψ,
  base_rel_of_hom_lift_of_interchange_of_αβ2ψ, base_rel_of_hom_lift_of_comm_of_βψ_α_β2ψ,
  base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_a, base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_b, base_rel_of_hom_lift_of_inv_doub_of_α_β2ψ_c,
  base_rel_of_hom_lift_of_comm_of_β2ψ_αβψ, base_rel_of_hom_lift_of_interchange_of_α2β2ψ_a, base_rel_of_hom_lift_of_interchange_of_α2β2ψ_b,
  base_rel_of_hom_lift_of_comm_of_ψ_αβ_β2ψ, base_rel_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_a, base_rel_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_b,
  base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a, base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b, base_rel_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c,
  base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a, base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b, base_rel_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c,
  base_rel_of_hom_lift_of_comm_of_βψ_αβ2ψ, base_rel_of_hom_lift_of_comm_of_β2ψ_αβ2ψ
}

def lifted_sets (F : Type TF) [Field F] := (nonhom_lifted_sets F) ∪ (hom_lifted_sets F)

/-! ## Definition for missing root (αβψ, αβ2ψ, α2β2ψ) -/

def split_3_into_1_2 (i : ℕ) (hi : i ≤ 3) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)

theorem correct_of_split_3_into_1_2 (i : ℕ) (hi : i ≤ 3) :
  (split_3_into_1_2 i hi).1 ≤ 1 ∧ (split_3_into_1_2 i hi).2 ≤ 2 ∧ (split_3_into_1_2 i hi).1 + (split_3_into_1_2 i hi).2 = i := by
  simp only [split_3_into_1_2]
  split
  all_goals trivial


def split_4_into_1_3 (i : ℕ) (hi : i ≤ 4) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)
  | 4 => (1, 3)

theorem correct_of_split_4_into_1_3 (i : ℕ) (hi : i ≤ 4) :
  (split_4_into_1_3 i hi).1 ≤ 1 ∧ (split_4_into_1_3 i hi).2 ≤ 3 ∧ (split_4_into_1_3 i hi).1 + (split_4_into_1_3 i hi).2 = i := by
  simp only [split_4_into_1_3]
  split
  all_goals trivial

def split_5_into_2_3 (i : ℕ) (hi : i ≤ 5) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)
  | 4 => (2, 2)
  | 5 => (2, 3)

theorem correct_of_split_5_into_2_3 (i : ℕ) (hi : i ≤ 5) :
  (split_5_into_2_3 i hi).1 ≤ 2 ∧ (split_5_into_2_3 i hi).2 ≤ 3 ∧ (split_5_into_2_3 i hi).1 + (split_5_into_2_3 i hi).2 = i := by
  simp only [split_5_into_2_3]
  split
  all_goals trivial

def weak_define (F : Type TR) [Field F] (g : GradedChevalleyGenerator B3LargePosRoot F) : FreeGroup (GradedChevalleyGenerator B3LargePosRoot F) :=
  let ⟨ ζ, i, hi, t ⟩ := g;
  match ζ with
  | αβψ =>
    {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2.1 *
    {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1 *
    {βψ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2.1 *
    {α, (split_3_into_1_2 i hi).1, -t}'(correct_of_split_3_into_1_2 i hi).1 *
    {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2.1
  | αβ2ψ => ⁅ {α, (split_4_into_1_3 i hi).1, t}'(correct_of_split_4_into_1_3 i hi).1,
      {β2ψ, (split_4_into_1_3 i hi).2, 1}'(correct_of_split_4_into_1_3 i hi).2.1 ⁆
  | α2β2ψ => ⁅ {αβ, (split_5_into_2_3 i hi).1, -t}'(correct_of_split_5_into_2_3 i hi).1,
      {β2ψ, (split_5_into_2_3 i hi).2, 1}'(correct_of_split_5_into_2_3 i hi).2.1 ⁆
  | _ => FreeGroup.of g

theorem weak_define_of_present (F : Type TR) [Field F] :
  ∀ {g : GradedChevalleyGenerator B3LargePosRoot F}, g.ζ ∈ weakB3LargeSystem.present_roots → weak_define F g = FreeGroup.of g := by
  intro g h_g_in_present
  rcases g with ⟨ ζ, i, hi, t ⟩
  cases ζ
  all_goals simp only [weak_define] -- this will close all present roots
  all_goals ( -- this will close the remaining (nonpresent) roots
    simp only [present_roots] at h_g_in_present
    contradiction
  )

theorem weak_define_is_projection (F : Type TR) [Field F] :
  ∀ {g : GradedChevalleyGenerator B3LargePosRoot F}, (FreeGroup.lift (weak_define F)) (weak_define F g) = weak_define F g := by
  intro g
  rcases g with ⟨ ζ, i, hi, t ⟩
  cases ζ
  all_goals simp only [weak_define, FreeGroup.lift.of, map_commutatorElement, map_inv, map_mul]

def weakB3Large (F : Type TF) [Field F] := GradedPartialChevalleyGroup.mk
  weakB3LargeSystem
  (lifted_sets F)
  (weak_define F)
  (weak_define_of_present F)
  (weak_define_is_projection F)

/-! # Definition of the 'full' A3 ungraded and graded groups -/

abbrev full_present_roots : Set (B3LargePosRoot) :=
  present_roots ∪ {αβψ, αβ2ψ, α2β2ψ}

abbrev full_trivial_commutator_pairs : Set (B3LargePosRoot × B3LargePosRoot) :=
  trivial_commutator_pairs ∪ {(αβ, βψ),
                              (α, αβψ), (β, αβψ), (αβ, αβψ), (β2ψ, αβψ),
                              (α, αβ2ψ), (ψ, αβ2ψ), (αβ, αβ2ψ), (βψ, αβ2ψ), (β2ψ, αβ2ψ), (αβψ, αβ2ψ),
                              (α, α2β2ψ), (β, α2β2ψ), (ψ, α2β2ψ), (αβ, α2β2ψ), (βψ, α2β2ψ), (β2ψ, α2β2ψ), (αβψ, α2β2ψ), (αβ2ψ, α2β2ψ)}

abbrev full_single_commutator_pairs : Set (SingleSpanRootPair B3LargePosRoot) :=
  single_commutator_pairs ∪ {⟨ α, β2ψ, αβ2ψ, 1, (by ht)⟩, ⟨αβψ, ψ, αβ2ψ, -2, (by ht)⟩,
                            ⟨αβ, β2ψ, α2β2ψ, -1, (by ht)⟩, ⟨αβψ, βψ, α2β2ψ, -2, (by ht)⟩, ⟨αβ2ψ, β, α2β2ψ, -1, (by ht)⟩}

abbrev full_double_commutator_pairs : Set (DoubleSpanRootPair B3LargePosRoot) :=
  double_commutator_pairs ∪ {⟨ α, βψ, αβψ, α2β2ψ, 1, 1, (by ht), (by ht)⟩, ⟨ αβ, ψ, αβψ, αβ2ψ, 1, 1, (by ht), (by ht)⟩}

theorem full_forall_roots_mem_present :
  ∀ (ζ : B3LargePosRoot), ζ ∈ full_present_roots := by
    intro ζ
    cases ζ
    all_goals tauto

def fullB3LargeSystem := PartialChevalleySystem.mk_full B3LargePosRoot
  full_present_roots
  full_trivial_commutator_pairs
  full_single_commutator_pairs
  full_double_commutator_pairs
  full_forall_roots_mem_present

def fullB3Large (F : Type TR) [Field F] := @PartialChevalleyGroup.mk B3LargePosRoot _ F _ fullB3LargeSystem
def fullB3LargeGraded (F : Type TR) [Field F] := GradedPartialChevalleyGroup.full_mk B3LargePosRoot F fullB3LargeSystem

--   ∀ S ∈ lifted_sets F,
--     ∀ r ∈ S, (weakB3Large F).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by

/-! # Notation and macros -/

/- Instantiate the `declare_thms` macros from `PartialChevalley.lean`. -/

macro "declare_B3Large_triv_expr_thm" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_expr_thm weakB3Large $F $r₁ $r₂)

macro "declare_B3Large_triv_comm_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_comm_of_root_pair_thms weakB3Large $F $r₁ $r₂)

macro "declare_B3Large_single_expr_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg n:num : command =>
  `(command| declare_single_expr_thms weakB3Large $F $r₁ $r₂ $r₃ $n)

macro "declare_B3Large_single_comm_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg n:num : command =>
  `(command| declare_single_comm_of_root_pair_thms weakB3Large $F $r₁ $r₂ $r₃ $n)

macro "declare_B3Large_lin_id_inv_thms" F:term:arg root:term:arg : command =>
  `(command| declare_lin_id_inv_thms weakB3Large $F $root)

macro "declare_B3Large_mixed_expr_thm" F:term:arg r:term:arg : command =>
  `(command| declare_mixed_expr_thm weakB3Large $F $r)

macro "declare_B3Large_mixed_comm_thms" F:term:arg r:term:arg : command =>
  `(command| declare_mixed_comm_thms weakB3Large $F $r)

-- r₁ is the larger root, as opposed to the above macros
macro "declare_B3Large_reflected_thm"
    F:term:arg v:term:arg r₁:term:arg r₂:term:arg r₃:term:arg
    "const" C:num
    "heights" n₁:num n₂:num n₃:num
    "to" n₄:num n₅:num n₆:num : command =>
  `(command| declare_reflected_thm weakB3Large $F $v $r₁ $r₂ $r₃ 0 $C $n₁ $n₂ $n₃ $n₄ $n₅ $n₆)

-- r₁ is the larger root, as opposed to the above macros
macro "declare_B3Large_reflected_thm"
    F:term:arg v:term:arg r₁:term:arg r₂:term:arg r₃:term:arg
    "const" "neg" C:num
    "heights" n₁:num n₂:num n₃:num
    "to" n₄:num n₅:num n₆:num : command =>
  `(command| declare_reflected_thm weakB3Large $F $v $r₁ $r₂ $r₃ 1 $C $n₁ $n₂ $n₃ $n₄ $n₅ $n₆)

macro "declare_B3Large_triv_comm_reflected_thm"
    F:term:arg v:term:arg r₁:term:arg r₂:term:arg
    "heights" n₁:num n₂:num
    "to" n₃:num n₄:num : command =>
  `(command| declare_triv_comm_reflected_thm weakB3Large $F $v $r₁ $r₂ $n₁ $n₂ $n₃ $n₄)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" =>
  (weakB3Large F).pres_mk {ζ, i, t}

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}'" h:max =>
  (weakB3Large F).pres_mk ({ζ, i, t}'h)

section forallNotation

set_option hygiene false

scoped notation "forall_i_t" h:max "," e =>
  ∀ ⦃i : ℕ⦄ (hi : i ≤ h) (t : F), e

scoped notation "forall_ij_tu" h₁:max h₂:max "," e =>
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ h₁) (hk : j ≤ h₂) (t u : F), e

scoped notation "forall_ik_tuv" h₁:max h₂:max "," e =>
  ∀ ⦃i k : ℕ⦄ (hi : i ≤ h₁) (hk : k ≤ h₂) (t u v : F), e

scoped notation "forall_ijk_tu" h₁:max h₂:max h₃:max "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (hk : k ≤ h₃) (t u : F), e

scoped notation "forall_ijk_tuv" h₁:max h₂:max h₃:max "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (hk : k ≤ h₃) (t u v : F), e

/-- By default, if no roots are provided, we use one each of `α`, `β`, `ψ`. -/
scoped notation "forall_ijk_tuv" "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : F), e

end forallNotation

example (S T : Set ℕ) (h : x ∈ S ∨ x ∈ T) : x ∈ S ∪ T := by exact h

macro "nonhom_tac " rel:ident " [" intros:ident,* "]" : tactic => `(tactic|
  ( intros $intros*;
    apply eq_of_mul_inv_eq_one;
    apply (weakB3Large _).lifted_helper $rel;
    simp only [weakB3Large, lifted_sets];
    left;
    simp only [nonhom_lifted_sets, Set.mem_singleton_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true];
    exists $intros,*
     ))

macro "hom_tac " rel:ident " [" intros:ident,* "]" : tactic => `(tactic|
  ( intros $intros*;
    apply eq_of_mul_inv_eq_one;
    apply (weakB3Large _).lifted_helper (hom_lift_set $rel);
    simp only [weakB3Large, lifted_sets];
    right;
    simp only [hom_lifted_sets, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left, true_or, or_true];
    exists $intros,*;
    unfold $rel;
    simp only [map_mul, map_inv, map_commutatorElement, commutatorElement_def, FreeGroup.map.of, hom_lift];
    simp only [one_mul, inv_one, mul_one, ←mul_assoc];
    try congr;
    try all_goals field_simp
     ))

end Steinberg.B3Large
