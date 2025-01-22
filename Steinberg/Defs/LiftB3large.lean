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

variable {R : Type TR} [Ring R]

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

/-! ### Bundle together assumptions about the B3Large generators -/

/-
The specific relation arises from "nonhomogeneously lifting" the commutator of αβ and βψ elements. (There is no analogue
of this relation for other root-pairs, since all other present pairs lie in a common two-dimensional subspace.)
-/
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

def rels_of_def_of_αβψ :=
  { ⁅ (free_mk_mk α (split_3_into_1_2 i hi).1 (correct_of_split_3_into_1_2 i hi).1 t),
      (free_mk_mk βψ (split_3_into_1_2 i hi).2 (correct_of_split_3_into_1_2 i hi).2 (1 : R)) ⁆
      * (free_mk_mk αβψ i hi t)⁻¹ | (i : ℕ) (hi : i ≤ αβψ.height) (t : R)
  }

/-
In-subgroup relations

8.59 is 7.1 (from LiftA3.lean)

8.60 is 7.2

8.61 is 7.3

8.62

8.63 is 8.2 (from LiftB3small.lean)

8.64 is 8.3

8.65 is 8.4

8.66 is 8.5

8.67 is 8.6

8.68 is 8.7
-/
