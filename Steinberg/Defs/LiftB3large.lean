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

/-! ### Defining the B3 large positive root system -/

inductive B3LargePosRoot
  | α | β | ψ | αβ | βψ | β2ψ | αβψ | αβ2ψ | α2β2ψ deriving Fintype, DecidableEq

namespace B3LargePosRoot

@[reducible]
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

instance : PosRootSys B3LargePosRoot where
  height := height
  toString := toString

end B3LargePosRoot

namespace B3LargeProof

open B3LargePosRoot GradedGen ReflDeg

-- Nonhomogenous lift (top of page 61)
def rels_of_nonhomog_lift_of_comm_of_αβ_βψ :=
   { ⁅ (free_mk_mk αβ 2 (by trivial) (t₁ * u₁)) * (free_mk_mk αβ 1 (by trivial) (t₁ * u₀ + t₀ * u₁)) * (free_mk_mk αβ 0 (by trivial) (t₀ * u₀)),
       (free_mk_mk βψ 2 (by trivial) (u₁ * v₁)) * (free_mk_mk βψ 1 (by trivial) (u₁ * v₀ + u₀ * v₁)) * (free_mk_mk βψ 0 (by trivial) (u₀ * v₀)) ⁆ |
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

-- 8.116, second relation (top of page 68)
def rels_of_def_of_αβψ :=
  {
    (free_mk_mk βψ (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (-1/2 : R)) *
    (free_mk_mk α (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 t) *
    (free_mk_mk βψ (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (1 : R)) *
    (free_mk_mk α (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 (-t)) *
    (free_mk_mk βψ (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (-1/2 : R)) *
    (free_mk_mk αβψ i hi t)⁻¹
    | (i : ℕ) (hi : i ≤ αβψ.height) (t : R)
  }

-- relations 8.60, 8.61, 8.62, 8.64, 8.65, 8.67, 8.68
abbrev trivial_commutator_pairs : Set (B3LargePosRoot × B3LargePosRoot) := {(α, αβ), (β, αβ), (α, ψ), (β, βψ), (β, β2ψ), (ψ, β2ψ), (βψ, β2ψ)}

-- relations 8.59, 8.66
abbrev single_commutator_pairs : Set ((ζ : B3LargePosRoot) × (η : B3LargePosRoot) × (θ : B3LargePosRoot) × R ×' (θ.height = ζ.height + η.height))
  := {⟨α, β, αβ, 1, (by simp only [height])⟩, ⟨ψ, βψ, β2ψ, 2, (by simp only [height])⟩}

-- relation 8.63 ???

-- relations 8.75, 8.76, 8.77, 8.78, 8.79, 8.80
abbrev mixed_commutes_roots : Set (B3LargePosRoot) := {α, β, ψ, αβ, βψ, β2ψ}

abbrev lin_roots : Set (B3LargePosRoot) := {α, β, ψ, αβ, βψ, β2ψ}

def nonhomog_sets (R : Type TR) [Field R] : Set (Set (FreeGroupOnGradedGens B3LargePosRoot R)) := {
  rels_of_nonhomog_lift_of_comm_of_αβ_βψ
}

def def_sets (R : Type TR) [Field R] : Set (Set (FreeGroupOnGradedGens B3LargePosRoot R)) := {
  rels_of_def_of_αβψ
}

def weakB3Large := WeakChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  mixed_commutes_roots
  lin_roots
  (nonhomog_sets R)
  (def_sets R)
