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
  -- double_commutator_pairs
  mixed_commutes_roots
  lin_roots
  (nonhomog_sets R)
  (def_sets R)
