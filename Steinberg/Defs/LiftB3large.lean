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

-- Relation 8.81
def rels_of_nonhomog_lift_of_comm_of_αβ_βψ :=
   { ⁅ (free_mk_mk αβ 2 (by trivial) (t₁ * u₁)) * (free_mk_mk αβ 1 (by trivial) (t₁ * u₀ + t₀ * u₁)) * (free_mk_mk αβ 0 (by trivial) (t₀ * u₀)),
       (free_mk_mk βψ 2 (by trivial) (u₁ * v₁)) * (free_mk_mk βψ 1 (by trivial) (u₁ * v₀ + u₀ * v₁)) * (free_mk_mk βψ 0 (by trivial) (u₀ * v₀)) ⁆ |
    (t₁ : R) (t₀ : R) (u₁ : R) (u₀ : R) (v₁ : R) (v₀ : R) }

-- Relation 8.82
def rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ :=
  { ⁅ (free_mk_mk α 1 (by trivial) t₁) * (free_mk_mk α 0 (by trivial) t₀),
      ⁅ (free_mk_mk αβ 2 (by trivial) (t₁ * u₁)) * (free_mk_mk αβ 2 (by trivial) (t₁ * u₀ + t₀ * u₁)) * (free_mk_mk αβ 0 (by trivial) (t₀ * u₀)),
        (free_mk_mk β2ψ 3 (by trivial) (t₁ * u₁^2)) * (free_mk_mk β2ψ 2 (by trivial) (t₀ * u₁^2 + 2 * t₁ * u₀ * u₁)) * (free_mk_mk β2ψ 1 (by trivial) (t₁ * u₀^2 + 2 * t₀ * u₀ * u₁)) * (free_mk_mk β2ψ 0 (by trivial) (t₀ * u₀^2)) ⁆ ⁆ |
    (t₁ : R) (t₀ : R) (u₁ : R) (u₀ : R) (v₁ : R) (v₀ : R)
  }

-- Relation 8.83
def rels_of_hom_lift_of_interchange_of_αβψ :=
  {
    (free_mk_mk ψ k hk (-v / 2)) *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u)) *
    (free_mk_mk ψ k hk v) *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u)) *
    (free_mk_mk ψ k hk (-v / 2)) *
    (free_mk_mk βψ (j + k) (add_le_add hj hk) (-u * v / 2))⁻¹ *
    (free_mk_mk α i hi (-t))⁻¹ *
    (free_mk_mk βψ (j + k) (add_le_add hj hk) (u * v))⁻¹ *
    (free_mk_mk α i hi t)⁻¹ *
    (free_mk_mk βψ (j + k) (add_le_add hj hk) (-u * v / 2))⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.84
def rels_of_hom_lift_of_doub_of_αβψ :=
  {
    (free_mk_mk ψ k hk (-v / 2)) *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u)) *
    (free_mk_mk ψ k hk v) *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u)) *
    (free_mk_mk ψ k hk (-v / 2)) *
    (free_mk_mk ψ k hk (-v / 2)) *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u)) *
    (free_mk_mk ψ k hk v) *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u)) *
    (free_mk_mk ψ k hk (-v / 2)) *
    (free_mk_mk ψ k hk (-v))⁻¹ *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u))⁻¹ *
    (free_mk_mk ψ k hk (2 * v))⁻¹ *
    (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u))⁻¹ *
    (free_mk_mk ψ k hk (-v))⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.85
def rels_of_hom_lift_of_interchange_of_αβ2ψ :=
  { ⁅
      (free_mk_mk ψ k hk (-v / 2)) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u)) *
      (free_mk_mk ψ k hk v) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u)) *
      (free_mk_mk ψ k hk (-v / 2)),
      free_mk_mk ψ k hk v
    ⁆ * ⁅
      free_mk_mk α i hi t,
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (-2 * u * v^2)
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.86
def rels_of_hom_lift_of_commutator_of_βψ_α_β2ψ :=
  { ⁅
      free_mk_mk βψ (j + k) (add_le_add hj hk) (u * v),
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.87a
def rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a :=
  { ⁅
      free_mk_mk α i hi t,
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk α i hi (-t),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (-u * v^2)
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.87b
def rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b :=
  { ⁅
      free_mk_mk α i hi t,
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk α i hi (-t),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.87c
def rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c :=
  { ⁅
      free_mk_mk α i hi t,
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk α i hi t,
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk α i hi (2 * t),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.88
def rels_of_hom_lift_of_commutator_of_β2ψ_αβψ :=
  { ⁅
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2),
      (free_mk_mk ψ k hk (-v / 2)) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u)) *
      (free_mk_mk ψ k hk v) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u)) *
      (free_mk_mk ψ k hk (-v / 2))
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.89a
def rels_of_hom_lift_of_interchange_of_α2β2ψ_a :=
  { ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (2 * u * v^2)
    ⁆ * ⁅
      (free_mk_mk ψ k hk (-v / 2)) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u)) *
      (free_mk_mk ψ k hk v) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u)) *
      (free_mk_mk ψ k hk (-v / 2)),
      free_mk_mk βψ (j + k) (add_le_add hj hk) (u * v)
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.89b
def rels_of_hom_lift_of_interchange_of_α2β2ψ_b :=
  { ⁅
      (free_mk_mk ψ k hk (-v / 2)) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u)) *
      (free_mk_mk ψ k hk v) *
      (free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u)) *
      (free_mk_mk ψ k hk (-v / 2)),
      free_mk_mk βψ (j + k) (add_le_add hj hk) (u * v)
    ⁆ * ⁅
      ⁅free_mk_mk α i hi t, free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)⁆,
      free_mk_mk β j hj u
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.90
def rels_of_hom_lift_of_commutator_of_ψ_αβ_β2ψ :=
  { ⁅
      free_mk_mk ψ k hk v,
      ⁅
        free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.91a (s = 1)
def rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a :=
  { ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
      ⁅
        free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.91b (s = -1)
def rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b :=
  { ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
      ⁅
        free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u),
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.92a
def rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a :=
  { ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (-u * v^2)
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.92b
def rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b :=
  { ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (-t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.92c
def rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c :=
  { ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆ * ⁅
      free_mk_mk αβ (i + j) (add_le_add hi hj) (2 * t * u),
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.93a
def rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a :=
  {
    ⁅
      free_mk_mk β i hi t,
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆ * ⁅
      free_mk_mk β i hi (-t),
      ⁅
        free_mk_mk α i hi (-t),
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.93b
def rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b :=
  { ⁅
      free_mk_mk β i hi t,
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆ * ⁅
      free_mk_mk β i hi (-t),
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.93c
def rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c :=
  { ⁅
      free_mk_mk β i hi t,
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆ * ⁅
      free_mk_mk β i hi t,
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆ * ⁅
      free_mk_mk β i hi (2 * t),
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.94
def rels_of_hom_lift_of_commutator_of_βψ_αβ2ψ :=
  { ⁅
      free_mk_mk βψ (j + k) (add_le_add hj hk) (u * v),
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.95
def rels_of_hom_lift_of_commutator_of_β2ψ_αβ2ψ :=
  { ⁅
      free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2),
      ⁅
        free_mk_mk α i hi t,
        free_mk_mk β2ψ (j + 2 * k) (add_le_add hj (mul_le_mul_of_nonneg_left hk (by norm_num))) (u * v^2)
      ⁆
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

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

def split_4_into_1_3 (i : ℕ) (hi : i ≤ 4) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)
  | 4 => (1, 3)

theorem correct_of_split_4_into_1_3 (i : ℕ) (hi : i ≤ 4) :
  (split_4_into_1_3 i hi).1 ≤ 1 ∧ (split_4_into_1_3 i hi).2 ≤ 3 := by
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
  (split_5_into_2_3 i hi).1 ≤ 2 ∧ (split_5_into_2_3 i hi).2 ≤ 3 := by
  simp only [split_5_into_2_3]
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

-- 8.135, first relation (page 76)
def rels_of_def_of_αβ2ψ :=
  { ⁅
      (free_mk_mk α (split_4_into_1_3 i hi).1 (correct_of_split_4_into_1_3 i hi).1 t),
      (free_mk_mk β2ψ (split_4_into_1_3 i hi).2 (correct_of_split_4_into_1_3 i hi).2 (1 : R))
    ⁆ * (free_mk_mk αβ2ψ i hi t)⁻¹
    | (i : ℕ) (hi : i ≤ αβ2ψ.height) (t : R)
  }

-- 8.174
def rels_of_def_of_α2β2ψ :=
  { ⁅
      (free_mk_mk αβ (split_5_into_2_3 i hi).1 (correct_of_split_5_into_2_3 i hi).1 t),
      (free_mk_mk β2ψ (split_5_into_2_3 i hi).2 (correct_of_split_5_into_2_3 i hi).2 (1 : R))
    ⁆ * (free_mk_mk α2β2ψ i hi (-t))⁻¹
    | (i : ℕ) (hi : i ≤ α2β2ψ.height) (t : R)
  }

-- relations 8.60, 8.61, 8.62, 8.64, 8.65, 8.67, 8.68
abbrev trivial_commutator_pairs : Set (B3LargePosRoot × B3LargePosRoot) := {(α, αβ), (β, αβ), (α, ψ), (β, βψ), (β, β2ψ), (ψ, β2ψ), (βψ, β2ψ)}

-- relations 8.59, 8.66
abbrev single_commutator_pairs : Set ((ζ : B3LargePosRoot) × (η : B3LargePosRoot) × (θ : B3LargePosRoot) × R ×' (θ.height = ζ.height + η.height))
  := {⟨α, β, αβ, 1, (by simp only [height])⟩, ⟨ψ, βψ, β2ψ, 2, (by simp only [height])⟩}

-- relations 8.75, 8.76, 8.77, 8.78, 8.79, 8.80
abbrev mixed_commutes_roots : Set (B3LargePosRoot) := {α, β, ψ, αβ, βψ, β2ψ}

-- relations 8.69, 8.70, 8.71, 8.72, 8.73, 8.74
abbrev lin_roots : Set (B3LargePosRoot) := {α, β, ψ, αβ, βψ, β2ψ}

-- relation 8.63
abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3LargePosRoot R) :=
  {⟨β, ψ, βψ, β2ψ, 1, 1, (by exact rfl), (by exact rfl)⟩}

def homog_and_nonhomog_sets (R : Type TR) [Field R] : Set (Set (FreeGroupOnGradedGens B3LargePosRoot R)) := {
  rels_of_nonhomog_lift_of_comm_of_αβ_βψ, rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ,
  rels_of_hom_lift_of_interchange_of_αβψ, rels_of_hom_lift_of_doub_of_αβψ,
  rels_of_hom_lift_of_interchange_of_αβ2ψ, rels_of_hom_lift_of_commutator_of_βψ_α_β2ψ,
  rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a, rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b, rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c,
  rels_of_hom_lift_of_commutator_of_β2ψ_αβψ, rels_of_hom_lift_of_interchange_of_α2β2ψ_a, rels_of_hom_lift_of_interchange_of_α2β2ψ_b,
  rels_of_hom_lift_of_commutator_of_ψ_αβ_β2ψ, rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a, rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b,
  rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a, rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b, rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c,
  rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a, rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b, rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c,
  rels_of_hom_lift_of_commutator_of_βψ_αβ2ψ, rels_of_hom_lift_of_commutator_of_β2ψ_αβ2ψ
}

def def_sets (R : Type TR) [Field R] : Set (Set (FreeGroupOnGradedGens B3LargePosRoot R)) := {
  rels_of_def_of_αβψ, rels_of_def_of_αβ2ψ, rels_of_def_of_α2β2ψ
}

def weakB3Large := WeakChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  double_commutator_pairs
  mixed_commutes_roots
  lin_roots
  (homog_and_nonhomog_sets R)
  (def_sets R)

abbrev weakB3Large_rels (R : Type TR) [Field R] := @weakB3Large.all_rels B3LargePosRoot _ R _

abbrev WeakChevalleyB3LargeGroup (R : Type TR) [Field R] := PresentedGroup (@weakB3Large.all_rels B3LargePosRoot _ R _)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" => weakB3Large.pres_mk (free_mk_mk ζ i (by (try simp only [PosRootSys.height] at *; try simp only [B3LargePosRoot.height] at *; first | trivial | omega)) t)

section UnpackingPresentation

-- Trivial: {(α, αβ), (β, αβ), (α, ψ), (β, βψ), (β, β2ψ), (ψ, β2ψ), (βψ, β2ψ)}

theorem comm_of_α_αβ : trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk α αβ :=
  weakB3Large.trivial_commutator_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem comm_of_β_αβ : trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk β αβ :=
  weakB3Large.trivial_commutator_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem comm_of_α_ψ : trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk α ψ :=
  weakB3Large.trivial_commutator_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem comm_of_β_βψ : trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk β βψ :=
  weakB3Large.trivial_commutator_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem comm_of_β_β2ψ : trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk β β2ψ :=
  weakB3Large.trivial_commutator_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_β2ψ : trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk ψ β2ψ :=
  weakB3Large.trivial_commutator_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem comm_of_βψ_β2ψ : trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk βψ β2ψ :=
  weakB3Large.trivial_commutator_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

-- Single: {(α, β), (ψ, βψ)}

theorem comm_of_α_β : single_commutator_of_root_pair (R := R) weakB3Large.pres_mk α β αβ 1 rfl :=
  weakB3Large.single_commutator_helper α β αβ 1 rfl (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem comm_of_ψ_βψ : single_commutator_of_root_pair weakB3Large.pres_mk ψ βψ β2ψ (2 : R) (by rfl) :=
  weakB3Large.single_commutator_helper ψ βψ β2ψ (2 : R) (by rfl) (by rw [weakB3Large, trivial_commutator_pairs]; simp)

-- Double: {(β, ψ)}
theorem comm_of_β_ψ : double_commutator_of_root_pair (R := R) weakB3Large.pres_mk β ψ βψ β2ψ (1 : R) (1 : R) (by rfl) (by rfl) :=
  weakB3Large.double_commutator_helper β ψ βψ β2ψ (1 : R) (1 : R) (by rfl) (by rfl) (by rw [weakB3Large, trivial_commutator_pairs]; simp)

/-! ### Linearity theorems for specific roots -/
-- {α, β, ψ, αβ, βψ, β2ψ}

theorem lin_of_α : lin_of_root (R := R) weakB3Large.pres_mk α :=
  weakB3Large.lin_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem lin_of_β : lin_of_root (R := R) weakB3Large.pres_mk β :=
  weakB3Large.lin_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem lin_of_ψ : lin_of_root (R := R) weakB3Large.pres_mk ψ :=
  weakB3Large.lin_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem lin_of_αβ : lin_of_root (R := R) weakB3Large.pres_mk αβ :=
  weakB3Large.lin_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem lin_of_βψ : lin_of_root (R := R) weakB3Large.pres_mk βψ :=
  weakB3Large.lin_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem lin_of_β2ψ : lin_of_root (R := R) weakB3Large.pres_mk β2ψ :=
  weakB3Large.lin_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

/-! ### Mixed-degree theorem for specific roots -/
-- {α, β, ψ αβ, βψ, β2ψ}

theorem mixed_commutes_of_α : mixed_commutes_of_root (R := R) weakB3Large.pres_mk α :=
  weakB3Large.mixed_commutes_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_β : mixed_commutes_of_root (R := R) weakB3Large.pres_mk β :=
  weakB3Large.mixed_commutes_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_ψ : mixed_commutes_of_root (R := R) weakB3Large.pres_mk ψ :=
  weakB3Large.mixed_commutes_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_αβ : mixed_commutes_of_root (R := R) weakB3Large.pres_mk αβ :=
  weakB3Large.mixed_commutes_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_βψ : mixed_commutes_of_root (R := R) weakB3Large.pres_mk βψ :=
  weakB3Large.mixed_commutes_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

theorem mixed_commutes_of_β2ψ : mixed_commutes_of_root (R := R) weakB3Large.pres_mk β2ψ :=
  weakB3Large.mixed_commutes_helper (by rw [weakB3Large, trivial_commutator_pairs]; simp)

/-! ### Nonhomogeneous lift -/

-- 8.81
theorem raw_nonhomog_lift_of_comm_of_αβ_βψ :
  ∀ t₁ t₀ u₁ u₀ v₁ v₀ : R,
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}
    , {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} ⁆
    = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_nonhomog_lift_of_comm_of_αβ_βψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists t₁, t₀, u₁, u₀, v₁, v₀

-- 8.82
theorem raw_nonhomog_lift_of_comm_of_α_α2β2ψ :
  ∀ t₁ t₀ u₁ u₀ v₁ v₀ : R,
    ⁅ {α, 1, t₁} * {α, 0, t₀},
      ⁅ {αβ, 2, t₁ * u₁} * {αβ, 2, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
        {β2ψ, 3, t₁ * u₁^2} * {β2ψ, 2, t₀ * u₁^2 + 2 * t₁ * u₀ * u₁} *
        {β2ψ, 1, t₁ * u₀^2 + 2 * t₀ * u₀ * u₁} * {β2ψ, 0, t₀ * u₀^2} ⁆⁆
    = 1 := by
    intro t₁ t₀ u₁ u₀ v₁ v₀
    apply WeakChevalley.helper
    apply weakB3Large.nonhomog_helper rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ
    · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
    · exists t₁, t₀, u₁, u₀, v₁, v₀

/-! ### Homogeneous lift -/

-- 8.83
theorem raw_hom_lift_of_interchange_of_αβψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  {ψ, k, -v/2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v/2} =
  {βψ, j + k, -u * v/2} * {α, i, t} * {βψ, j + k, u * v} * {α, i, -t} * {βψ, j + k, -u * v / 2} := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_interchange_of_αβψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.84
theorem raw_hom_lift_of_doub_of_αβψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} *
  {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} =
  {ψ, k, -v} * {αβ, i + j, t * u} * {ψ, k, 2 * v} * {αβ, i + j, -t * u} * {ψ, k, -v} := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_doub_of_αβψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.85
theorem raw_hom_lift_of_interchange_of_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2}, {ψ, k, v}⁆ =
  ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u * v^2}⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_interchange_of_αβ2ψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.86
theorem raw_hom_lift_of_commutator_of_βψ_α_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{βψ, j + k, u * v}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_commutator_of_βψ_α_β2ψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.87a
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆ = ⁅{α, i, -t}, {β2ψ, j + 2 * k, -u * v^2}⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.87b
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆ * ⁅{α, i, -t}, {β2ψ, j + 2 * k, u * v^2}⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.87c
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_c :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{α, i, t} , {β2ψ, j + 2 * k, u * v^2}⁆ * ⁅{α, i, t} , {β2ψ, j + 2 * k, u * v^2}⁆ = ⁅{α, i, 2 * t}, {β2ψ, j + 2 * k, u * v^2}⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.88
theorem raw_hom_lift_of_commutator_of_β2ψ_αβψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{β2ψ, j + 2 * k, u * v^2}, {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2}⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_commutator_of_β2ψ_αβψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.89a
theorem raw_hom_lift_of_interchange_of_α2β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, 2 * u * v^2}⁆ = ⁅{ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2}, {βψ, j + k, u * v}⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_interchange_of_α2β2ψ_a
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.89b
theorem raw_hom_lift_of_interchange_of_α2β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2}, {βψ, j + k, u * v}⁆ = ⁅⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆, {β, j, u}⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_interchange_of_α2β2ψ_b
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.90
theorem raw_hom_lift_of_commutator_of_ψ_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{ψ, k, v}, ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_commutator_of_ψ_αβ_β2ψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.91a
theorem raw_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβ, i + j, t * u}, ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.91b
theorem raw_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβ, i + j, t * u}, ⁅{αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.92a
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2}⁆ = ⁅{αβ, i + j, -t * u}, {β2ψ, j + 2 * k, -u * v^2}⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.92b
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2}⁆ * ⁅{αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2}⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.92c
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_c :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2}⁆ * ⁅{αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2}⁆ = ⁅{αβ, i + j, 2 * t * u}, {β2ψ, j + 2 * k, u * v^2}⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.93a
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{β, i, t}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = ⁅{β, i, -t}, ⁅{α, i, -t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.93b
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_b :
 ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
 ⁅{β, i, t}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ * ⁅{β, i, -t}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.93c
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_c :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{β, i, t}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ * ⁅{β, i, t}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = ⁅{β, i, 2 * t}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.94
theorem raw_hom_lift_of_commutator_of_βψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{βψ, j + k, u * v}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_commutator_of_βψ_αβ2ψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

-- 8.95
theorem raw_hom_lift_of_commutator_of_β2ψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{β2ψ, j + 2 * k, u * v^2}, ⁅{α, i, t}, {β2ψ, j + 2 * k, u * v^2}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_hom_lift_of_commutator_of_β2ψ_αβ2ψ
  · simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, j, k, hi, hj, hk, t, u, v

theorem refl_of_homog_and_nonhomog :
  ∀ S ∈ homog_and_nonhomog_sets R,
    ∀ r ∈ S, weakB3Large.pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  intro rel hrel r hr
  simp only [homog_and_nonhomog_sets] at hrel
  sorry

theorem refl_of_def : ∀ S ∈ def_sets R, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  sorry

theorem b3small_valid : ReflDeg.refl_valid (R := R) weakB3Large :=
  ⟨refl_of_homog_and_nonhomog, refl_of_def⟩

end UnpackingPresentation

/-! ### Identity theorems : 8.96 - 8.101 -/

theorem id_of_α : id_of_root (R := R) weakB3Large.pres_mk α :=
  id_of_lin_of_root lin_of_α

theorem id_of_β : id_of_root (R := R) weakB3Large.pres_mk β :=
  id_of_lin_of_root lin_of_β

theorem id_of_ψ : id_of_root (R := R) weakB3Large.pres_mk ψ :=
  id_of_lin_of_root lin_of_ψ

theorem id_of_αβ : id_of_root (R := R) weakB3Large.pres_mk αβ :=
  id_of_lin_of_root lin_of_αβ

theorem id_of_βψ : id_of_root (R := R) weakB3Large.pres_mk βψ :=
  id_of_lin_of_root lin_of_βψ

theorem id_of_β2ψ : id_of_root (R := R) weakB3Large.pres_mk β2ψ :=
  id_of_lin_of_root lin_of_β2ψ

/-! ### Inverse theorems - 8.102 - 8.107 -/

theorem inv_of_α : inv_of_root (R := R) weakB3Large.pres_mk α :=
  inv_of_lin_of_root lin_of_α

theorem inv_of_β : inv_of_root (R := R) weakB3Large.pres_mk β :=
  inv_of_lin_of_root lin_of_β

theorem inv_of_ψ : inv_of_root (R := R) weakB3Large.pres_mk ψ :=
  inv_of_lin_of_root lin_of_ψ

theorem inv_of_αβ : inv_of_root (R := R) weakB3Large.pres_mk αβ :=
  inv_of_lin_of_root lin_of_αβ

theorem inv_of_βψ : inv_of_root (R := R) weakB3Large.pres_mk βψ :=
  inv_of_lin_of_root lin_of_βψ

theorem inv_of_β2ψ : inv_of_root (R := R) weakB3Large.pres_mk β2ψ :=
  inv_of_lin_of_root lin_of_β2ψ

-- 8.108
theorem expand_βψ_as_ψ_β_ψ_β_ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
  {βψ, i + j, t * u} = {ψ, i, -t/2} * {β, j, u} * {ψ, i, t} * {β, j, -u} * {ψ, i, -t/2} := by
  sorry

-- 8.109
theorem expand_αβ_as_α_β_α_β :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (t u : R),
  {αβ, i + j, t * u} = {α, i, t} * {β, j, u} * {α, i, -t} * {β, j, -u} := by
  sorry

-- 8.110
theorem expand_β2ψ_as_ψ_βψ_ψ_βψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
  {β2ψ, i + j, 2 * t * u} = {ψ, i, t} * {βψ, j, u} * {ψ, i, -t} * {βψ, j, -u} := by
  sorry

-- 8.111
theorem expr_β_α_as_αβ_α_β :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (t u : R),
  {β, j, u} * {α, i, t} = {αβ, i + j, -t * u} * {α, i, t} * {β, j, u} := by
  sorry

-- 8.112a
theorem expr_ψ_β_as_β_ψ_βψ_β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
  {ψ, j, u} * {β, i, t} = {β, i, t} * {ψ, j, u} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, t * u^2} := by
  sorry

-- 8.112b
theorem expr_ψ_β_as_β2ψ_βψ_β_ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
  {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := by
  sorry

-- 8.112c
theorem expr_ψ_β_as_β_β2ψ_βψ_ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
  {ψ, j, u} * {β, i, t} = {β, i, t} * {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {ψ, j, u} := by
  sorry

-- 8.112d
theorem expr_ψ_β_as_β_βψ_β2ψ_ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : R),
  {ψ, j, u} * {β, i, t} = {β, i, t} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, -t * u^2} * {ψ, j, u} := by
  sorry

-- 8.113a
theorem expr_ψ_βψ_as_βψ_β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ βψ.height) (t u : R),
  {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {β2ψ, i + j, 2 * t * u} * {ψ, i, t} := by
  sorry

-- 8.113b
theorem expr_ψ_βψ_as_βψ_ψ_β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ βψ.height) (t u : R),
  {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {ψ, i, t} * {β2ψ, i + j, 2 * t * u} := by
  sorry

-- 8.114a
theorem expr_βψ_ψ_as_ψ_β2ψ_βψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ βψ.height) (t u : R),
  {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {β2ψ, i + j, -2 * t * u} * {βψ, j, u} := by
  sorry

-- 8.114b
theorem expr_βψ_ψ_as_ψ_βψ_β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ βψ.height) (t u : R),
  {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {βψ, j, u} * {β2ψ, i + j, -2 * t * u} := by
  sorry

-- 8.115
theorem trivial_comm_of_αβ_βψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβ βψ := by
  sorry

-- 8.117 (8.116 defines αβψ)
theorem trivial_comm_of_α_αβψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk α αβψ := by
  sorry

-- 8.118
theorem trivial_comm_of_αβ_αβψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβ αβψ := by
  sorry

-- 8.119
theorem trivial_comm_of_β_αβψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk β αβψ := by
  sorry

-- 8.120a
theorem inv_doub_of_αβψ_a :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ αβψ.height) (t : R),
  {αβψ, i, t} * {αβψ, i, -t} = 1 := by
  sorry

-- 8.120b
theorem inv_doub_of_αβψ_b :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ αβψ.height) (t : R),
  {αβψ, i, t} * {αβψ, i, t} = {αβψ, i, 2 * t} := by
  sorry

-- 8.121a
theorem generic_commutator_of_αβ_ψ_a :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβψ, i + j, t * u} * ⁅{αβψ, i + j, -t * u}, {ψ, j, u / 2}⁆ := by
  sorry

-- 8.121b
theorem generic_commutator_of_αβ_ψ_b :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  ⁅{αβ, i, t}, {ψ, j, u}⁆ = ⁅{αβψ, i + j, t * u}, {ψ, j, u / 2}⁆⁻¹ * {αβψ, i + j, t * u} := by
  sorry

-- 8.122a
theorem generic_commutator_of_α_βψ_a :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βψ.height) (t u : R),
  ⁅{α, i, t}, {βψ, j, u}⁆ = {αβψ, i + j, t * u} * ⁅{αβψ, i + j, -t * u}, {βψ, j, u / 2}⁆ := by
  sorry

-- 8.122b
theorem generic_commutator_of_α_βψ_b :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βψ.height) (t u : R),
  ⁅{α, i, t}, {βψ, j, u}⁆ = ⁅{αβψ, i + j, t * u}, {βψ, j, u / 2}⁆⁻¹ * {αβψ, i + j, t * u} := by
  sorry

-- 8.123
theorem lift_hom_interchange_of_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβψ, i + j + k, t * u}, {ψ, k, v}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u * v}⁆ := by
  sorry

-- 8.124
theorem lift_hom_commutator_of_βψ_α_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{βψ, j + k, t}, ⁅{α, i, u}, {β2ψ, j + 2 * k, v}⁆⁆ = 1 := by
  sorry

-- 8.125a
theorem lift_hom_inv_doub_of_α_β2ψ_a :
  ∀ ⦃i j : ℕ⦄ (hi :i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  ⁅{α, i, t}, {β2ψ, j, u}⁆ = ⁅{α, i, -t}, {β2ψ, j, -u}⁆ := by
  sorry

-- 8.125b
theorem lift_hom_inv_doub_of_α_β2ψ_b :
  ∀ ⦃i j : ℕ⦄ (hi :i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  ⁅{α, i, t}, {β2ψ, j, u}⁆ * ⁅{α, i, t}, {β2ψ, j, -u}⁆ = 1 := by
  sorry

-- 8.125c
theorem lift_hom_inv_doub_of_α_β2ψ_c :
  ∀ ⦃i j : ℕ⦄ (hi :i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  ⁅{α, i, t}, {β2ψ, j, u}⁆ * ⁅{α, i, t}, {β2ψ, j, u}⁆ = ⁅{α, i, t}, {β2ψ, j, 2 * u}⁆ := by
  sorry

-- 8.126
theorem lift_hom_commutator_of_β2ψ_αβψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{β2ψ, j + 2 * k, t}, {αβψ, i + j + k, u}⁆ = 1 := by
  sorry

-- 8.127
theorem comm_of_ψ_α_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ α.height) (hk : k ≤ β2ψ.height) (t u v : R),
  ⁅{ψ, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  sorry

-- 8.128
theorem comm_of_α_αβψ_ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ αβψ.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{α, i, t}, ⁅{αβψ, j, u}, {ψ, k, v}⁆⁆ = 1 := by
  sorry

-- 8.129
theorem comm_of_α_α_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ α.height) (hk : k ≤ β2ψ.height) (t u v : R),
  ⁅{α, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  sorry

-- Proposition 8.130
theorem sufficient_conditions_for_commutator_of_αβψ_and_ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 1)
  (hyp : ∀ t u v : R, ⁅{βψ, j, t}, ⁅{α, i, u}, {β2ψ, j + k, v}⁆⁆ = 1),
  ∀ t u v : R, ⁅{αβψ, i + j, t * u}, {ψ, k, v}⁆ = ⁅{α, i, t}, {β2ψ, j + k, -2 * u * v}⁆ := by
  sorry

-- 8.131
theorem partial_A_interchange_of_αβ2ψ :
  ∀ t u v : R,
  ⁅{αβψ, 0, t * u}, {ψ, 1, v}⁆ = ⁅{α, 0, t}, {β2ψ, 1, -2 * u * v}⁆ := by
  sorry

-- Proposition 8.132
theorem sufficient_conditions_for_commutator_of_βψ_and_α_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 3)
  (hyp : ∀ t u : R, ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1),
  ∀ t u v : R, ⁅{βψ, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  sorry

-- 8.133
theorem partial_comm_of_βψ_α_β2ψ :
  ∀ t u v : R,
  ⁅{βψ, 2, t}, ⁅{α, 0, u}, {β2ψ, 2, v}⁆⁆ = 1 := by
  sorry

-- 8.134
theorem partial_B_interchange_of_αβ2ψ :
  ∀ t u v : R,
  ⁅{αβψ, 2, t * u}, {ψ, 0, v}⁆ = ⁅{α, 0, t}, {β2ψ, 2, -2 * u * v}⁆ := by
  sorry

-- 8.136 (8.135 is establishing αβ2ψ)
theorem trivial_comm_of_α_αβ2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk α αβ2ψ := by
  sorry

-- 8.137
theorem trivial_comm_of_ψ_αβ2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk ψ αβ2ψ := by
  sorry

-- 8.138a
theorem inv_doub_of_αβ2ψ_a :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ αβ2ψ.height) (t : R),
  {αβ2ψ, i, t} * {αβ2ψ, i, -t} = 1 := by
  sorry

-- 8.138b
theorem inv_doub_of_αβ2ψ_b :
    ∀ ⦃i : ℕ⦄ (hi : i ≤ αβ2ψ.height) (t : R),
    {αβ2ψ, i, t} * {αβ2ψ, i, t} = {αβ2ψ, i, 2 * t} := by
    sorry

-- 8.139a
theorem commutator_of_αβ_ψ_a :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, t * u^2} := by
  sorry

-- 8.139b
theorem commutator_of_αβ_ψ_b :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβ2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} := by
  sorry

-- 8.140a
theorem expression_αβ2ψ_to_α_β2ψ_a :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  {αβ2ψ, i + j, t * u} = {α, i, t} * {β2ψ, j, u} * {α, i, -t} * {β2ψ, j, -u} := by
  sorry

-- 8.140b
theorem expression_αβ2ψ_to_α_β2ψ_b :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  {αβ2ψ, i + j, t * u} = {β2ψ, j, -u} * {α, i, t} * {β2ψ, j, u} * {α, i, -t} := by
  sorry

-- 8.141a
theorem expression_αβ2ψ_to_ψ_αβψ_a :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβψ.height) (hj : j ≤ ψ.height) (t u : R),
  {αβ2ψ, i + j, -2 * t * u} = {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} * {ψ, j, -t} := by
  sorry

-- 8.141b
theorem expression_αβ2ψ_to_ψ_αβψ_b :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβψ.height) (hj : j ≤ ψ.height) (t u : R),
  {αβ2ψ, i + j, -2 * t * u} = {ψ, j, -t} * {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} := by
  sorry

-- 8.142a
theorem expr_α_β2ψ_as_αβ2ψ_β2ψ_α :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  {α, i, t} * {β2ψ, j, u} = {αβ2ψ, i + j, t * u} * {β2ψ, j, u} * {α, i, t} := by
  sorry

-- 8.142b
theorem expr_α_β2ψ_as_β2ψ_αβ2ψ_α :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  {α, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {αβ2ψ, i + j, t * u} * {α, i, t} := by
  sorry

-- 8.142c
theorem expr_α_β2ψ_as_β2ψ_α_αβ2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β2ψ.height) (t u : R),
  {α, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {α, i, t} * {αβ2ψ, i + j, t * u} := by
  sorry

-- 8.143a
theorem expr_ψ_αβψ_as_αβψ_αβ2ψ_ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ αβψ.height) (t u : R),
  {ψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {αβ2ψ, i + j, 2 * t * u} * {ψ, i, t} := by
  sorry

-- 8.143b
theorem expr_ψ_αβψ_as_αβψ_ψ_αβ2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ αβψ.height) (t u : R),
  {ψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {ψ, i, t} * {αβ2ψ, i + j, 2 * t * u} := by
  sorry

-- 8.144a
theorem expr_αβψ_ψ_as_αβ2ψ_ψ_αβψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ αβψ.height) (t u : R),
  {αβψ, j, u} * {ψ, i, t} = {αβ2ψ, i + j, -2 * t * u} * {ψ, i, t} * {αβψ, j, u} := by
  sorry

-- 8.144b
theorem expr_αβψ_ψ_as_ψ_αβ2ψ_αβψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ ψ.height) (hj : j ≤ αβψ.height) (t u : R),
  {αβψ, j, u} * {ψ, i, t} = {ψ, i, t} * {αβ2ψ, i + j, -2 * t * u} * {αβψ, j, u} := by
  sorry

-- 8.145a
theorem expr_αβ_ψ_as_ψ_αβ_αβψ_αβ2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβ, i, t} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} := by
  sorry

-- 8.145b
theorem expr_αβ_ψ_as_ψ_αβψ_αβ2ψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβ, i, t} := by
  sorry

-- 8.145c
theorem expr_αβ_ψ_as_ψ_αβ2ψ_αβψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβ, i, t} := by
  sorry

-- 8.145d
theorem expr_αβ_ψ_as_αβ2ψ_αβψ_ψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  {αβ, i, t} * {ψ, j, u} = {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} * {ψ, j, u} * {αβ, i, t} := by
  sorry

-- 8.146
theorem expr_ψ_αβ_as_αβ_αβ2ψ_αβψ_ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ ψ.height) (t u : R),
  {ψ, j, u} * {αβ, i, t} = {αβ, i, t} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, -t * u} * {ψ, j, u} := by
  sorry

-- 8.147a
theorem hom_lift_of_interchange_of_α2β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, 2 * u * v}⁆ = ⁅{αβψ, i + j + k, t * u}, {βψ, j + k, v}⁆ := by
  sorry

-- 8.147b
theorem hom_lift_of_interchange_of_α2β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : R),
  ⁅{αβψ, i + j + k, t}, {βψ, j + k, u * v}⁆ = ⁅{αβ2ψ, i + j + 2 * k, 2 * t * u}, {β, j, v}⁆ := by
  sorry

-- 8.148
theorem hom_lift_of_commutator_ψ_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u v : R),
  ⁅{ψ, i, t}, ⁅{αβ, i + j, u}, {β2ψ, j + 2 * k, v}⁆⁆ = 1 := by
  sorry

-- 8.149a
theorem hom_lift_of_commutator_αβ_αβ_β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{αβ, i + j, t}, ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆⁆ = 1 := by
  sorry

-- 8.149b
theorem hom_lift_of_commutator_αβ_αβ_β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{αβ, i + j, t}, ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, u}⁆⁆ = 1 := by
  sorry

-- 8.150a
theorem hom_lift_of_inv_doub_of_αβ_β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ = ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, -u}⁆ := by
  sorry

-- 8.150b
theorem hom_lift_of_inv_doub_of_αβ_β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ * ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, u}⁆ = 1 := by
  sorry

-- 8.150c
theorem hom_lift_of_inv_doub_of_αβ_β2ψ_c :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ * ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ = ⁅{αβ, i + j, 2 * t}, {β2ψ, j + 2 * k, u}⁆ := by
  sorry

-- 8.151a
theorem hom_lift_of_inv_doub_of_β_αβ2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = ⁅{β, i, -t}, {αβ2ψ, i + j + 2 * k, -u}⁆ := by
  sorry

-- 8.151b
theorem hom_lift_of_inv_doub_of_β_αβ2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ * ⁅{β, i, -t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 := by
  sorry

-- 8.151c
theorem hom_lift_of_inv_doub_of_β_αβ2ψ_c :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ * ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = ⁅{β, i, 2 * t}, {αβ2ψ, i + j + 2 * k, u}⁆ := by
  sorry

-- 8.152 TODO: ASK
theorem hom_lift_of_commutator_βψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{βψ, j + k, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 := by
  sorry

-- 8.153
theorem hom_lift_of_commutator_of_β2ψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{β2ψ, j + 2 * k, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 := by
  sorry

-- 8.154
theorem comm_of_βψ_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ βψ.height) (hj : j ≤ αβ.height) (hk : k ≤ β2ψ.height) (t u v : R),
  ⁅{βψ, i, t}, ⁅{αβ, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  sorry

-- 8.155
theorem comm_of_αβ_βψ_αβψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ βψ.height) (hk : k ≤ αβψ.height) (t u v : R),
  ⁅{αβ, i, t}, ⁅{βψ, j, u}, {αβψ, k, v}⁆⁆ = 1 := by
  sorry

-- 8.156
theorem comm_of_β_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβ.height) (hk : k ≤ β2ψ.height) (t u v : R),
  ⁅{β, i, t}, ⁅{αβ, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  sorry

-- 8.157
theorem comm_of_β_αβψ_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβψ.height) (hk : k ≤ βψ.height) (t u v : R),
  ⁅{β, i, t}, ⁅{αβψ, j, u}, {βψ, k, v}⁆⁆ = 1 := by
  sorry

-- 8.158
theorem sufficient_conditions_for_commutator_of_αβψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 2)
  (h35a : ∀ t u v : R, ⁅{ψ, j, t}, ⁅{αβ, i, u}, {β2ψ, j + k, v}⁆⁆ = 1)
  (h35b : ∀ t u v : R, ⁅{αβ, i, t}, ⁅{αβ, i, u}, {β2ψ, j + k, v}⁆⁆ = 1)
  (h35c : ∀ t u : R, ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, -t}, {β2ψ, j + k, -u}⁆)
  (h35d : ∀ t u : R, ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ * ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, 2 * t}, {β2ψ, j + k, u}⁆),
  ∀ t u : R, ⁅{αβψ, i + j, t * u}, {βψ, k, v}⁆ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ := by
  sorry

-- 8.159a
theorem partial_A_interchange_of_α2β2ψ_a :
  ∀ t u v : R,
  ⁅{αβψ, 0, t * u}, {βψ, 2, v}⁆ = ⁅{αβ, 0, t}, {β2ψ, 2, 2 * u * v}⁆ := by
  sorry

-- 8.159b
theorem partial_A_interchange_of_α2β2ψ_b :
  ∀ t u v : R,
  ⁅{αβψ, 2, t * u}, {βψ, 0, v}⁆ = ⁅{αβ, 1, t}, {β2ψ, 1, 2 * u * v}⁆ := by
  sorry

-- 8.160
theorem more_sufficient_conditions_for_commutator_of_αβψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 1)
  (h38a : ∀ t u v : R, ⁅{β, k, t}, ⁅{αβ2ψ, i + j, u}, {β, k, v}⁆⁆ = 1)
  (h38b : ∀ t u v : R, ⁅{ψ, j, t}, ⁅{αβ2ψ, i + j, u}, {β, k, v}⁆⁆ = 1)
  (h38c : ∀ t u : R, ⁅{β, k, u}, {αβ2ψ, i + j, -t}⁆ = ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆)
  (h38d : ∀ t u : R, ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆ * ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆ = ⁅{αβ2ψ, i + j, 2 * t}, {β, k, u}⁆),
  ∀ t u : R, ⁅{αβψ, i, t}, {βψ, j + k, u * v}⁆ = ⁅{αβ2ψ, i + j, 2 * t * u}, {β, k, v}⁆ := by
  sorry

-- 8.161
theorem sufficient_conditions_for_commutator_of_αβ2ψ_and_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 3)
  (hyp : ∀ t u : R, ⁅{β2ψ, k, t}, {αβ2ψ, i + j, u}⁆ = 1),
  ∀ t u : R, ⁅{β2ψ, i, t}, {αβ2ψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.162a
theorem partial_comm_of_β2ψ_αβ2ψ_a :
  ∀ t u : R, ⁅{β2ψ, 2, t}, {αβ2ψ, 1, u}⁆ = 1 := by
  sorry

-- 8.162b
theorem partial_comm_of_β2ψ_αβ2ψ_b :
  ∀ t u : R, ⁅{β2ψ, 0, t}, {αβ2ψ, 2, u}⁆ = 1 := by
  sorry

-- 8.163
theorem sufficient_conditions_for_commutator_of_ψ_and_αβ2ψ_β :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 4) (hk : k ≤ 1)
  (h41a : ∀ t u : R, ⁅{β2ψ, 2 * i + k, t}, {αβ2ψ, j, u}⁆ = 1)
  (h41b : ∀ t u : R, ⁅{βψ, i + k, t}, {αβ2ψ, j, u}⁆ = 1),
  ∀ t u v : R, ⁅{ψ, i, t}, ⁅{αβ2ψ, j, u}, {β, k, v}⁆⁆ = 1 := by
  sorry

-- 8.164
theorem partial_comm_of_ψ_αβ2ψ_β :
  ∀ t u v : R, ⁅{ψ, 1, v}, ⁅{αβ2ψ, 1, t}, {β, 0, u}⁆⁆ = 1 := by
  sorry

-- 8.165
theorem partial_B_interchange_of_α2β2ψ :
  ∀ t u v : R, ⁅{αβψ, 0, t}, {βψ, 1, u * v}⁆ = ⁅{αβ2ψ, 1, 2 * t * u}, {β, 0, v}⁆ := by
  sorry

-- 8.166
theorem sufficient_conditions_for_commutator_of_αβ_and_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 2)
  (h42a : ∀ t u : R, ⁅{αβ2ψ, i + 2 * j, t}, {βψ, k, u}⁆ = 1)
  (h42b : ∀ t u v : R, ⁅{ψ, j, t}, ⁅{αβψ, i + j, u}, {βψ, k, v}⁆⁆ = 1),
  ∀ t u v : R, ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ = ⁅{αβψ, i + j, t * u}, {βψ, k, v}⁆ := by
  sorry

-- 8.167
theorem sufficient_conditions_for_commutator_of_αβ2ψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 4) (hj : j ≤ 1) (hk : k ≤ 1)
  (h44a : ∀ t u v : R, ⁅⁅{αβ2ψ, i, t}, {β, j, u}⁆, {ψ, k, v}⁆ = 1)
  (h44b : ∀ t u : R, ⁅{β, j, -u}, {αβ2ψ, i, t}⁆ = ⁅{αβ2ψ, i, t}, {β, j, u}⁆)
  (h44c : ∀ t u : R, ⁅{αβ2ψ, i, t}, {β, j, u}⁆ * ⁅{αβ2ψ, i, -t}, {β, j, u}⁆ = 1),
  ∀ t u : R, ⁅{αβ2ψ, i, t}, {βψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.168
theorem partial_comm_of_βψ_αβ2ψ :
  ∀ t u : R, ⁅{αβ2ψ, 2, t}, {βψ, 0, u}⁆ = 1 := by
  sorry

-- 8.169a
theorem partial_C_interchange_of_α2β2ψ_a :
  ∀ t u v : R, ⁅{αβ, 0, t}, {β2ψ, 1, u * v}⁆ = ⁅{αβψ, 1, t * u}, {βψ, 0, 2 * v}⁆ := by
  sorry

-- 8.169b
theorem partial_C_interchange_of_α2β2ψ_b :
  ∀ t u v : R, ⁅{αβ, 2, t}, {β2ψ, 0, u * v}⁆ = ⁅{αβψ, 2, t * v}, {βψ, 0, 2 * v}⁆ := by
  sorry

-- 8.170
theorem sufficient_conditions_for_commutator_of_αβ2ψ_and_β :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 1)
  (h47a : ∀ t u : R, ⁅{αβψ, i, t}, {β2ψ, 2 * j + k, u}⁆ = 1)
  (h47b : ∀ t u v : R, ⁅⁅{αβψ, i, t}, {βψ, j + k, u}⁆, {ψ, j, v}⁆ = 1)
  (h47c : ∀ t u : R, ⁅{βψ, j + k, -u}, {αβψ, i, t}⁆ = ⁅{αβψ, i, t}, {βψ, j + k, u}⁆),
  ∀ t u v : R, ⁅{αβ2ψ, i + j, 2 * t * u}, {β, k, v}⁆ = ⁅{αβψ, i, t}, {βψ, j + k, u * v}⁆ := by
  sorry

-- 8.171
theorem sufficient_conditions_for_commutator_of_αβψ_and_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
  (hyp : ∀ t u : R, ⁅{αβ2ψ, i + k, u}, {βψ, j, t}⁆ = 1),
  ∀ t u : R, ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1 := by
  sorry

-- 8.172
theorem partial_comm_of_αβψ_β2ψ :
  ∀ t u : R, ⁅{αβψ, 0, t}, {β2ψ, 1, u}⁆ = 1 := by
  sorry

-- 8.173
theorem partial_D_interchange_of_α2β2ψ :
  ∀ t u v : R, ⁅{αβψ, 0, t}, {βψ, 1, u * v}⁆ = ⁅{αβ2ψ, 0, t * u}, {β, 1, 2 * u}⁆ := by
  sorry

-- 8.175 (8.174 is establishing α2β2ψ)
theorem trivial_comm_of_β_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk β α2β2ψ := by
  sorry

-- 8.176
theorem trivial_comm_of_αβ_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβ α2β2ψ := by
  sorry

-- 8.177
theorem trivial_comm_of_βψ_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk βψ α2β2ψ := by
  sorry

-- 8.178a
theorem inv_doub_of_α2β2ψ_a :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ α2β2ψ.height) (t : R),
  {α2β2ψ, i, t} * {α2β2ψ, i, -t} = 1 := by
  sorry

-- 8.178b
theorem inv_doub_of_α2β2ψ_b :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ α2β2ψ.height) (t : R),
  {α2β2ψ, i, t} * {α2β2ψ, i, t} = {α2β2ψ, i, 2 * t} := by
  sorry

-- 8.179a
theorem expand_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : R),
  {α2β2ψ, i + j, -t * u} = {αβ, i, t} * {β2ψ, j, u} * {αβ, i, -t} * {β2ψ, j, -u} := by
  sorry

-- 8.179b
theorem expand_α2β2ψ_as_β2ψ_αβ_β2ψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : R),
  {α2β2ψ, i + j, -t * u} = {β2ψ, j, -u} * {αβ, i, t} * {β2ψ, j, u} * {αβ, i, -t} := by
  sorry

-- 8.180a
theorem expr_αβ_β2ψ_as_β2ψ_α2β2ψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : R),
  {αβ, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {α2β2ψ, i + j, -t * u} * {αβ, i, t} := by
  sorry

-- 8.180b
theorem expr_αβ_β2ψ_as_β2ψ_αβ_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : R),
  {αβ, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {αβ, i, t} * {α2β2ψ, i + j, -t * u} := by
  sorry

-- 8.181a
theorem expr_β_αβ2ψ_as_αβ2ψ_α2β2ψ_β :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβ2ψ.height) (t u : R),
  {β, i, t} * {αβ2ψ, j, u} = {αβ2ψ, j, u} * {α2β2ψ, i + j, t * u} * {β, i, t} := by
  sorry

-- 8.181b
theorem expr_β_αβ2ψ_as_αβ2ψ_β_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβ2ψ.height) (t u : R),
  {β, i, t} * {αβ2ψ, j, u} = {αβ2ψ, j, u} * {β, i, t} * {α2β2ψ, i + j, t * u} := by
  sorry

-- 8.182a
theorem expr_βψ_αβψ_as_αβψ_α2β2ψ_βψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ βψ.height) (hj : j ≤ αβψ.height) (t u : R),
  {βψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {α2β2ψ, i + j, 2 * t * u} * {βψ, i, t} := by
  sorry

-- 8.182b
theorem expr_βψ_αβψ_as_αβψ_βψ_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ βψ.height) (hj : j ≤ αβψ.height) (t u : R),
  {βψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {βψ, i, t} * {α2β2ψ, i + j, 2 * t * u} := by
  sorry

-- 8.183a
theorem commutator_of_α_βψ_a :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βψ.height) (t u : R),
  ⁅{α, i, t}, {βψ, j, u}⁆ = {αβψ, i + j, t * u} * {α2β2ψ, i + 2 * j, t * u^2} := by
  sorry

-- 8.183b
theorem commutator_of_α_βψ_b :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βψ.height) (t u : R),
  ⁅{α, i, t}, {βψ, j, u}⁆ = {α2β2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} := by
  sorry

-- 8.184
theorem sufficient_conditions_for_commutator_of_ψ_and_α2β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
  (h50a : ∀ t u : R, ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1)
  (h50b : ∀ t u : R, ⁅{αβ2ψ, 2 * i + j, t}, {β2ψ, k, u}⁆ = 1),
  ∀ t u : R, ⁅{ψ, i, t}, {α2β2ψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.185
theorem partial_comm_of_ψ_α2β2ψ :
  ∀ t u : R, ⁅{ψ, 1, t}, {α2β2ψ, 0, u}⁆ = 1 := by
  sorry

-- 8.186
theorem trivial_comm_of_ψ_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk ψ α2β2ψ := by
  sorry

-- 8.187
theorem trivial_comm_of_β2ψ_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk β2ψ α2β2ψ := by
  sorry

-- 8.188
theorem trivial_comm_of_αβψ_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβψ α2β2ψ := by
  sorry

-- 8.189
theorem trivial_comm_of_αβ2ψ_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβ2ψ α2β2ψ := by
  sorry

-- 8.190
theorem mixed_comm_of_α2β2ψ :
  mixed_commutes_of_root (R := R) weakB3Large.pres_mk α2β2ψ := by
  sorry

-- 8.191
theorem trivial_comm_of_αβψ_β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβψ β2ψ := by
  sorry

-- 8.192
theorem trivial_comm_of_βψ_αβ2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk βψ αβ2ψ := by
  sorry

-- 8.193
theorem trivial_comm_of_β2ψ_αβ2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk β2ψ αβ2ψ := by
  sorry

-- 8.194
theorem trivial_comm_of_αβψ_αβ2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβψ αβ2ψ := by
  sorry

-- 8.195
theorem mixed_comm_of_αβ2ψ :
  mixed_commutes_of_root (R := R) weakB3Large.pres_mk αβ2ψ := by
  sorry

-- 8.196
theorem lin_of_αβ2ψ :
  lin_of_root (R := R) weakB3Large.pres_mk αβ2ψ := by
  sorry

-- 8.197
theorem lin_of_α2β2ψ :
  lin_of_root (R := R) weakB3Large.pres_mk α2β2ψ := by
  sorry

-- 8.198
theorem hom_lift_of_comm_of_α_α2β2ψ_square :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t r : R),
  ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 2 * k, t * r^2}⁆ = 1 := by
  sorry

-- 8.200 (8.199 is about sum of squares in finite field)
theorem hom_lift_of_comm_of_α_α2β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : R),
  ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 2 * k, u}⁆ = 1 := by
  sorry

-- 8.201
theorem nonhomog_lift_of_comm_of_α_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (t u : R),
  ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 1, u}⁆ = 1 := by
  sorry

-- 8.202
theorem sufficient_conditions_for_commutator_of_αβ_and_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 4)
  (hyp : ∀ t u : R, ⁅{α, i, t}, {α2β2ψ, j + k, u}⁆ = 1),
  ∀ t u : R, ⁅{αβ, i + j, t}, {αβ2ψ, k, u}⁆ = 1 := by
  sorry

-- 8.203
theorem partial_comm_of_αβ_α2β2ψ :
  ∀ t u : R, ⁅{αβ, 0, t}, {αβ2ψ, 1, u}⁆ = 1 := by
  sorry

-- 8.204
theorem sufficient_conditions_for_commutator_of_α_and_α2β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
  (hyp : ∀ t u : R, ⁅{αβ, j, t}, {αβ2ψ, i + k, u}⁆ = 1),
  ∀ t u : R, ⁅{α, i, t}, {α2β2ψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.205
theorem partial_comm_of_α_α2β2ψ :
  ∀ t u : R, ⁅{α, 1, t}, {α2β2ψ, 0, u}⁆ = 1 := by
  sorry

-- 8.206
theorem trivial_comm_of_α_α2β2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk α α2β2ψ := by
  sorry

-- 8.207
theorem trivial_comm_of_αβ_αβ2ψ :
  trivial_commutator_of_root_pair (R := R) weakB3Large.pres_mk αβ αβ2ψ := by
  sorry

-- 8.208
theorem mixed_comm_of_αβψ :
  mixed_commutes_of_root (R := R) weakB3Large.pres_mk αβψ := by
  sorry

-- 8.209
theorem lin_of_αβψ :
  lin_of_root (R := R) weakB3Large.pres_mk αβψ := by
  sorry

end B3LargeProof
