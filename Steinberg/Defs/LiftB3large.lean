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
    ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t : R) (u : R) (v : R)
  }

-- Relation 8.86
def rels_of_hom_lift_of_comm_of_βψ_α_β2ψ :=
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
    ⁆⁻¹
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
def rels_of_hom_lift_of_comm_of_β2ψ_αβψ :=
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
def rels_of_hom_lift_of_comm_of_ψ_αβ_β2ψ :=
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
def rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_a :=
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
def rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_b :=
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
def rels_of_hom_lift_of_comm_of_βψ_αβ2ψ :=
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
def rels_of_hom_lift_of_comm_of_β2ψ_αβ2ψ :=
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

-- 8.81, second relation (top of page 68)
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
  rels_of_hom_lift_of_interchange_of_αβ2ψ, rels_of_hom_lift_of_comm_of_βψ_α_β2ψ,
  rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a, rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b, rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c,
  rels_of_hom_lift_of_comm_of_β2ψ_αβψ, rels_of_hom_lift_of_interchange_of_α2β2ψ_a, rels_of_hom_lift_of_interchange_of_α2β2ψ_b,
  rels_of_hom_lift_of_comm_of_ψ_αβ_β2ψ, rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_a, rels_of_hom_lift_of_comm_of_αβ_αβ_β2ψ_b,
  rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a, rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b, rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c,
  rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a, rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b, rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c,
  rels_of_hom_lift_of_comm_of_βψ_αβ2ψ, rels_of_hom_lift_of_comm_of_β2ψ_αβ2ψ
}

def def_sets (R : Type TR) [Field R] : Set (Set (FreeGroupOnGradedGens B3LargePosRoot R)) := {
  rels_of_def_of_αβψ
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
theorem nonhomog_lift_of_comm_of_αβ_βψ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R),
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}
    , {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} ⁆
    = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply WeakChevalley.helper
  apply weakB3Large.nonhomog_helper rels_of_nonhomog_lift_of_comm_of_αβ_βψ
  · simp only [weakB3Large, homog_and_nonhomog_sets]
    exact Set.mem_insert _ _
  · exists t₁, t₀, u₁, u₀, v₁, v₀

-- 8.82
theorem nonhomog_lift_of_comm_of_α_α2β2ψ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R),
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
