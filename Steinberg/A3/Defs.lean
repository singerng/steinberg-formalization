/-

LICENSE goes here.

-/

import Steinberg.Defs.PartialChevalley
import Steinberg.Macro.Attr
import Mathlib.Tactic.DeriveFintype

/-!

  File dox.

-/

namespace Steinberg.A3

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

instance instPosRootSys : PosRootSys A3PosRoot where
  height := height
  toString := toString

instance instCoeNat : Coe A3PosRoot Nat where
  coe r := height r

end A3PosRoot

open A3PosRoot GradedChevalleyGenerator

variable {R : Type TR} [Ring R]

/-! # Relations -/

/-
The specific relation arises from "nonhomogeneously lifting" the commutator of αβ and βγ elements. (There is no analogue
of this relation for other root-pairs, since all other present pairs lie in a common two-dimensional subspace.)
-/
/-- Steinberg relations in the weak A3 group -/
abbrev trivial_commutator_pairs : Set (A3PosRoot × A3PosRoot) :=
  {(α, γ), (α, αβ), (β, αβ), (β, βγ), (γ, βγ)}

abbrev single_commutator_pairs : Set (SingleSpanRootPair A3PosRoot R) :=
  {⟨ α, β, αβ, 1, (by ht)⟩, ⟨β, γ, βγ, 1, (by ht)⟩}

abbrev mixed_commutes_roots : Set (A3PosRoot) :=
  {α, β, γ, αβ, βγ}

abbrev lin_roots : Set (A3PosRoot) :=
  {α, β, γ, αβ, βγ}

/-- Additional relations (TBD title) -/

def rels_of_nonhomog_lift_of_comm_of_αβ_βγ :=
  { ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
      {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} ⁆
    | (t₁ : R) (t₀ : R) (u₁ : R) (u₀ : R) (v₁ : R) (v₀ : R) }

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

def rels_of_def_of_αβγ :=
  { ⁅ {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1,
      {βγ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
      * {αβγ, i, t}⁻¹
    | (i : ℕ) (hi : i ≤ αβγ.height) (t : R) }

-- lifted commutator of αβ and βγ
def lifted_sets (R : Type TR) [Ring R] : Set (Set (FreeGroup (GradedChevalleyGenerator A3PosRoot R))) :=
  { rels_of_nonhomog_lift_of_comm_of_αβ_βγ }

-- definition of αβγ
def def_sets (R : Type TR) [Ring R] : Set (Set (FreeGroup (GradedChevalleyGenerator A3PosRoot R))) :=
  { rels_of_def_of_αβγ }

def weakA3 (R : Type TR) [Ring R] := PartialChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  ∅
  mixed_commutes_roots
  lin_roots
  (lifted_sets R)
  (def_sets R)

/-! ### Additional relations which define the full A3 group -/

abbrev full_trivial_commutator_pairs : Set (A3PosRoot × A3PosRoot) :=
  trivial_commutator_pairs ∪ {(αβ, βγ), (α, αβγ), (β, αβγ), (γ, αβγ), (αβ, αβγ), (βγ, αβγ)}

abbrev full_single_commutator_pairs : Set (SingleSpanRootPair A3PosRoot R) :=
  single_commutator_pairs ∪ {⟨ α, βγ, αβγ, 1, (by ht)⟩, ⟨αβ, γ, αβγ, 1, (by ht)⟩}

abbrev full_mixed_commutes_roots : Set (A3PosRoot) :=
  mixed_commutes_roots ∪ {αβγ}

abbrev full_lin_roots : Set (A3PosRoot) :=
  lin_roots ∪ {αβγ}

def fullA3 (R : Type TR) [Ring R] := @PartialChevalley.mk _ _ R _
  full_trivial_commutator_pairs
  full_single_commutator_pairs
  ∅
  full_mixed_commutes_roots
  full_lin_roots
  (∅)
  (∅)

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
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" =>
  (weakA3 R).pres_mk (free_mk ζ i (by ht) t)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}'" h =>
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
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R), e

end forallNotation

end Steinberg.A3
