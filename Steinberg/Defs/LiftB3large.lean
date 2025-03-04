/-

  LICENSE goes here.

-/

import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype

import Steinberg.Defs.Deg
import Steinberg.Defs.Commutator
import Steinberg.Defs.ReflDeg

import Steinberg.Upstream.FreeGroup

/-!

  File summary goes here.

-/

namespace Steinberg

open Steinberg.Macro

variable {F : Type TF} [Field F] (Fchar : (2 : F) ≠ 0)

/-! ### Defining the B3 large positive root system -/

inductive B3LargePosRoot
  | α | β | ψ | αβ | βψ | β2ψ | αβψ | αβ2ψ | α2β2ψ
deriving Fintype, DecidableEq, Inhabited

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
  { ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
      {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} ⁆
    | (t₁ : F) (t₀ : F) (u₁ : F) (u₀ : F) (v₁ : F) (v₀ : F) }

-- Relation 8.82
def rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ :=
  { ⁅ {α, 1, t₁} * {α, 0, t₀},
      ⁅ {αβ, 2, t₁ * u₁} * {αβ, 2, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
        {β2ψ, 3, t₁ * u₁^2} * {β2ψ, 2, t₀ * u₁^2 + 2 * t₁ * u₀ * u₁}
          * {β2ψ, 1, t₁ * u₀^2 + 2 * t₀ * u₀ * u₁} * {β2ψ, 0, t₀ * u₀^2} ⁆ ⁆
    | (t₁ : F) (t₀ : F) (u₁ : F) (u₀ : F) (v₁ : F) (v₀ : F) }

-- Relation 8.83
def rels_of_hom_lift_of_interchange_of_αβψ :=
  { {ψ, k, -v / 2} * {αβ, i + j, t * u}'(add_le_add hi hj) *
    {ψ, k, v} * {αβ, i + j, -t * u}'(add_le_add hi hj) *
    {ψ, k, -v / 2} * ({βψ, j + k, -u * v / 2}'(add_le_add hj hk))⁻¹ *
    {α, i, -t}⁻¹ * ({βψ, j + k, u * v}'(add_le_add hj hk))⁻¹ *
    {α, i, t}⁻¹ * ({βψ, j + k,-u * v / 2}'(add_le_add hj hk))⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.84
def rels_of_hom_lift_of_doub_of_αβψ :=
  { {ψ, k, -v / 2} * {αβ, i, t * u} *
    {ψ, k, v} * {αβ, i, -t * u} *
    {ψ, k, -v / 2} * {ψ, k, -v / 2} *
    {αβ, i, t * u} * {ψ, k, v} *
    {αβ, i, -t * u} * {ψ, k, -v / 2} *
    {ψ, k, -v}⁻¹ * {αβ, i, -t * u}⁻¹ *
    {ψ, k, 2 * v}⁻¹ * {αβ, i, t * u}⁻¹ * {ψ, k, -v}⁻¹
    | (i : ℕ) (k : ℕ)
      (hi : i ≤ αβ.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.85
def rels_of_hom_lift_of_interchange_of_αβ2ψ :=
  { ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u}'(add_le_add hi hj) *
      {ψ, k, v} * {αβ, i + j, -t * u}'(add_le_add hi hj) *
      {ψ, k, -v / 2}, {ψ, k, v} ⁆
    * ⁅ {α, i, t},
        {β2ψ, j + 2 * k, -2 * u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.86
def rels_of_hom_lift_of_commutator_of_βψ_α_β2ψ :=
  { ⁅ {βψ, j + k, u * v}'(add_le_add hj hk),
      ⁅ {α, i, t},
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.87a
def rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a :=
  { ⁅ {α, i, t},
      {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {α, i, -t},
        {β2ψ, j + 2 * k, -u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial)))⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.87b
def rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b :=
  { ⁅ {α, i, t},
      {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {α, i, t},
        {β2ψ, j + 2 * k, -u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.87c
def rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c :=
  { ⁅ {α, i, t},
      {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {α, i, t},
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
      * ⁅ {α, i, t},
          {β2ψ, j + 2 * k, 2 * u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.88
def rels_of_hom_lift_of_commutator_of_β2ψ_αβψ :=
  { ⁅ {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))),
      {ψ, k, -v / 2} *
      {αβ, i + j, t * u}'(add_le_add hi hj) *
      {ψ, k, v} *
      {αβ, i + j, -t * u}'(add_le_add hi hj) *
      {ψ, k, -v / 2} ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.89a
def rels_of_hom_lift_of_interchange_of_α2β2ψ_a :=
  { ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
      {β2ψ, j + 2 * k, 2 * u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {ψ, k, -v / 2} *
        {αβ, i + j, t * u}'(add_le_add hi hj) *
        {ψ, k, v} *
        {αβ, i + j, -t * u}'(add_le_add hi hj) *
        {ψ, k, -v / 2},
        {βψ, j + k, u * v}'(add_le_add hj hk) ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height)
      (hk : k ≤ ψ.height) (t : F) (u : F) (v : F) }

-- Relation 8.89b
def rels_of_hom_lift_of_interchange_of_α2β2ψ_b :=
  { ⁅ {ψ, k, -v / 2} *
      {αβ, i + j, t * u}'(add_le_add hi hj) *
      {ψ, k, v} *
      {αβ, i + j, -t * u}'(add_le_add hi hj) *
      {ψ, k, -v / 2},
      {βψ, j + k, u * v}'(add_le_add hj hk) ⁆
    * ⁅ ⁅ {α, i, t},
          {β2ψ, j + 2 * k, 2 * u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆,
        {β, j, u} ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.90
def rels_of_hom_lift_of_commutator_of_ψ_αβ_β2ψ :=
  { ⁅ {ψ, k, v},
      ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.91a (s = 1)
def rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a :=
  { ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
      ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.91b (s = -1)
def rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b :=
  { ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
      ⁅ {αβ, i + j, -t * u}'(add_le_add hi hj),
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.92a
def rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a :=
  { ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
      {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {αβ, i + j, -t * u}'(add_le_add hi hj),
        {β2ψ, j + 2 * k, -u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.92b
def rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b :=
  { ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
      {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {αβ, i + j, -t * u}'(add_le_add hi hj),
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.92c
def rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c :=
  { ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
      {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {αβ, i + j, t * u}'(add_le_add hi hj),
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆
    * ⁅ {αβ, i + j, 2 * t * u}'(add_le_add hi hj),
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.93a
def rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a :=
  { ⁅ {β, i, t},
      ⁅ {α, i, t},
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    * ⁅ {β, i, -t},
        ⁅ {α, i, -t},
          {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.93b
def rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b :=
  { ⁅ {β, i, t},
      ⁅ {α, i, t},
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    * ⁅ {β, i, -t},
        ⁅ {α, i, t},
          {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.93c
def rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c :=
  { ⁅ {β, i, t},
      ⁅ {α, i, t},
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    * ⁅ {β, i, t},
        ⁅ {α, i, t},
          {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    * ⁅ {β, i, 2 * t},
        ⁅ {α, i, t},
          {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆⁻¹
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.94
def rels_of_hom_lift_of_commutator_of_βψ_αβ2ψ :=
  { ⁅ {βψ, j + k, u * v}'(add_le_add hj hk),
      ⁅ {α, i, t},
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

-- Relation 8.95
def rels_of_hom_lift_of_commutator_of_β2ψ_αβ2ψ :=
  { ⁅ {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))),
      ⁅ {α, i, t},
        {β2ψ, j + 2 * k, u * v^2}'(add_le_add hj (mul_le_mul_of_nonneg_left hk (by trivial))) ⁆ ⁆
    | (i : ℕ) (j : ℕ) (k : ℕ)
      (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height)
      (t : F) (u : F) (v : F) }

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
  { {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2 *
    {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1 *
    {βψ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 *
    {α, (split_3_into_1_2 i hi).1, -t}'(correct_of_split_3_into_1_2 i hi).1 *
    {βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2 *
    {αβψ, i, t}⁻¹
    | (i : ℕ) (hi : i ≤ αβψ.height) (t : F) }

-- 8.135, first relation (page 76)
def rels_of_def_of_αβ2ψ :=
  { ⁅ {α, (split_4_into_1_3 i hi).1, t}'(correct_of_split_4_into_1_3 i hi).1,
      {β2ψ, (split_4_into_1_3 i hi).2, 1}'(correct_of_split_4_into_1_3 i hi).2 ⁆
    * {αβ2ψ, i, t}⁻¹
    | (i : ℕ) (hi : i ≤ αβ2ψ.height) (t : F) }

-- 8.174
def rels_of_def_of_α2β2ψ :=
  { ⁅ {αβ, (split_5_into_2_3 i hi).1, t}'(correct_of_split_5_into_2_3 i hi).1,
      {β2ψ, (split_5_into_2_3 i hi).2, 1}'(correct_of_split_5_into_2_3 i hi).2 ⁆
    * ({α2β2ψ, i, -t} : FreeGroupOnGradedGens _ _)⁻¹
    | (i : ℕ) (hi : i ≤ α2β2ψ.height) (t : F) }

-- relations 8.60, 8.61, 8.62, 8.64, 8.65, 8.67, 8.68
abbrev trivial_commutator_pairs : Set (B3LargePosRoot × B3LargePosRoot) :=
  {(α, αβ), (β, αβ), (α, ψ), (β, βψ), (β, β2ψ), (ψ, β2ψ), (βψ, β2ψ)}

-- relations 8.59, 8.66
abbrev single_commutator_pairs : Set ((ζ : B3LargePosRoot) × (η : B3LargePosRoot) × (θ : B3LargePosRoot) × F ×' (θ.height = ζ.height + η.height))
  := {⟨α, β, αβ, 1, (by simp only [height])⟩, ⟨ψ, βψ, β2ψ, 2, (by simp only [height])⟩}

-- relations 8.75, 8.76, 8.77, 8.78, 8.79, 8.80
abbrev mixed_commutes_roots : Set B3LargePosRoot :=
  {α, β, ψ, αβ, βψ, β2ψ}

-- relations 8.69, 8.70, 8.71, 8.72, 8.73, 8.74
abbrev lin_roots : Set B3LargePosRoot :=
  {α, β, ψ, αβ, βψ, β2ψ}

-- relation 8.63
abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3LargePosRoot F) :=
  {⟨β, ψ, βψ, β2ψ, 1, 1, (by exact rfl), (by exact rfl)⟩}

def homog_and_nonhomog_sets (F : Type TF) [Field F] : Set (Set (FreeGroupOnGradedGens B3LargePosRoot F)) := {
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

def def_sets (F : Type TF) [Field F] : Set (Set (FreeGroupOnGradedGens B3LargePosRoot F)) := {
  rels_of_def_of_αβψ, rels_of_def_of_αβ2ψ, rels_of_def_of_α2β2ψ
}

def weakB3Large (F : Type TF) [Field F] := WeakChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  double_commutator_pairs
  mixed_commutes_roots
  lin_roots
  (homog_and_nonhomog_sets F)
  (def_sets F)

abbrev WeakChevalleyB3LargeGroup (F : Type TF) [Field F] :=
  PresentedGroup (weakB3Large F).all_rels

/- Instantiate the `declare_thms` macros from `WeakChevalley.lean`. -/

-- CC: TODO: Make this a macro to declare all at once for A3.
--     Something like: `declare_thms A3 weakA3 R`

macro "declare_B3Large_triv_comm_of_root_pair_thms" r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_comm_of_root_pair_thms weakB3Large F $r₁ $r₂)

macro "declare_B3Large_single_comm_of_root_pair_thms" r₁:term:arg r₂:term:arg r₃:term:arg n:term:arg : command =>
  `(command| declare_single_comm_of_root_pair_thms weakB3Large F $r₁ $r₂ $r₃ $n)

macro "declare_B3Large_lin_id_inv_thms" root:term:arg : command =>
  `(command| declare_lin_id_inv_thms weakB3Large F $root)

macro "declare_B3Large_expr_as_thm" r₁:term:arg r₂:term:arg : command =>
  `(command| declare_expr_as_thm weakB3Large F $r₁ $r₂)

macro "declare_B3Large_mixed_comm_thms" r:term:arg : command =>
  `(command| declare_mixed_comm_thms weakB3Large F $r)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" =>
  (weakB3Large F).pres_mk (free_mk_mk ζ i (by
    try simp only [PosRootSys.height] at *
    try simp only [B3LargePosRoot.height] at *; first | trivial | omega) t)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}'" h =>
  (weakB3Large F).pres_mk ({ζ, i, t}'h)

set_option maxHeartbeats 0

section UnpackingPresentation

declare_B3Large_triv_comm_of_root_pair_thms α αβ
declare_B3Large_triv_comm_of_root_pair_thms β αβ
declare_B3Large_triv_comm_of_root_pair_thms α ψ
declare_B3Large_triv_comm_of_root_pair_thms β βψ
declare_B3Large_triv_comm_of_root_pair_thms β β2ψ
declare_B3Large_triv_comm_of_root_pair_thms ψ β2ψ
declare_B3Large_triv_comm_of_root_pair_thms βψ β2ψ

declare_B3Large_single_comm_of_root_pair_thms α β αβ 1
declare_B3Large_single_comm_of_root_pair_thms ψ βψ β2ψ 2

-- Double: {(β, ψ)}
theorem commutator_of_β_ψ : double_commutator_of_root_pair (weakB3Large F).pres_mk β ψ βψ β2ψ (1 : F) (1 : F) (by rfl) (by rfl) :=
  (weakB3Large F).double_commutator_helper β ψ βψ β2ψ (1 : F) (1 : F) (by rfl) (by rfl)
    (by unfold weakB3Large; simp)

/-! ### Linearity theorems for specific roots -/
/-! ### Identity theorems : 8.96 - 8.101 -/
/-! ### Inverse theorems - 8.102 - 8.107 -/

declare_B3Large_lin_id_inv_thms α
declare_B3Large_lin_id_inv_thms β
declare_B3Large_lin_id_inv_thms ψ
declare_B3Large_lin_id_inv_thms αβ
declare_B3Large_lin_id_inv_thms βψ
declare_B3Large_lin_id_inv_thms β2ψ

/-! ### Mixed-degree theorem for specific roots -/

declare_B3Large_mixed_comm_thms α
declare_B3Large_mixed_comm_thms β
declare_B3Large_mixed_comm_thms ψ
declare_B3Large_mixed_comm_thms αβ
declare_B3Large_mixed_comm_thms βψ
declare_B3Large_mixed_comm_thms β2ψ

theorem def_of_αβψ :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ αβψ.height) (t : F),
  ({βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2) *
  ({α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1) *
  ({βψ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2) *
  ({α, (split_3_into_1_2 i hi).1, -t}'(correct_of_split_3_into_1_2 i hi).1) *
  ({βψ, (split_3_into_1_2 i hi).2, -1/2}'(correct_of_split_3_into_1_2 i hi).2)
  = {αβψ, i, t} := by
  intro i hi t
  apply WeakChevalley.helper
  apply (weakB3Large F).def_helper rels_of_def_of_αβψ
  · simp only [weakB3Large, def_sets]
    exact Set.mem_insert rels_of_def_of_αβψ _
  · exists i, hi, t

theorem def_of_αβ2ψ :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ αβ2ψ.height) (t : F),
  ⁅ ({α, (split_4_into_1_3 i hi).1, t}'(correct_of_split_4_into_1_3 i hi).1),
    ({β2ψ, (split_4_into_1_3 i hi).2, 1}'(correct_of_split_4_into_1_3 i hi).2)
  ⁆ = {αβ2ψ, i, t} := by
  intro i hi t
  apply WeakChevalley.helper
  apply (weakB3Large F).def_helper rels_of_def_of_αβ2ψ
  · simp only [weakB3Large, def_sets, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · exists i, hi, t

/-! ### Nonhomogeneous lift -/

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

scoped notation "forall_ijk_tuv" "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : F), e

end forallNotation

macro "raw_hom_tac " rel:ident " [" intros:ident,* "]" : tactic => `(tactic|
  ( intros $intros*;
    apply WeakChevalley.helper;
    apply (weakB3Large F).nonhomog_helper $rel;
    simp only [weakB3Large, homog_and_nonhomog_sets, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or, or_true];
    exists $intros,* ))

-- 8.81
theorem raw_nonhomog_lift_of_comm_of_αβ_βψ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}
    , {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} ⁆
    = 1 := by
  raw_hom_tac rels_of_nonhomog_lift_of_comm_of_αβ_βψ [t₁, t₀, u₁, u₀, v₁, v₀]

-- 8.82
theorem raw_nonhomog_lift_of_comm_of_α_α2β2ψ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {α, 1, t₁} * {α, 0, t₀},
      ⁅ {αβ, 2, t₁ * u₁} * {αβ, 2, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
        {β2ψ, 3, t₁ * u₁^2} * {β2ψ, 2, t₀ * u₁^2 + 2 * t₁ * u₀ * u₁} *
        {β2ψ, 1, t₁ * u₀^2 + 2 * t₀ * u₀ * u₁} * {β2ψ, 0, t₀ * u₀^2} ⁆⁆ = 1 := by
  raw_hom_tac rels_of_nonhomog_lift_of_comm_of_α_α2β2ψ [t₁, t₀, u₁, u₀, v₁, v₀]

/-! ### Homogeneous lift -/

-- 8.83
theorem raw_hom_lift_of_interchange_of_αβψ :
  forall_ijk_tuv,
    {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} =
    {βψ, j + k, -u * v / 2} * {α, i, t} * {βψ, j + k, u * v} * {α, i, -t} * {βψ, j + k, -u * v / 2} := by
  raw_hom_tac rels_of_hom_lift_of_interchange_of_αβψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.84
theorem raw_hom_lift_of_doub_of_αβψ :
  forall_ik_tuv αβ ψ,
    {ψ, k, -v / 2} * {αβ, i, t * u} * {ψ, k, v} * {αβ, i, -t * u} * {ψ, k, -v / 2} *
    {ψ, k, -v / 2} * {αβ, i, t * u} * {ψ, k, v} * {αβ, i, -t * u} * {ψ, k, -v / 2} =
    {ψ, k, -v} * {αβ, i, t * u} * {ψ, k, 2 * v} * {αβ, i, -t * u} * {ψ, k, -v} := by
  raw_hom_tac rels_of_hom_lift_of_doub_of_αβψ [i, k, hi, hk, t, u, v]

-- 8.85
theorem raw_hom_lift_of_interchange_of_αβ2ψ :
  forall_ijk_tuv,
    ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
      {ψ, k, v} ⁆
      = ⁅ {α, i, t}, {β2ψ, j + 2 * k, -2 * u * v^2} ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_interchange_of_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.86
theorem raw_hom_lift_of_commutator_of_βψ_α_β2ψ :
  forall_ijk_tuv,
    ⁅ {βψ, j + k, u * v}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_commutator_of_βψ_α_β2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.87a
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_a :
  forall_ijk_tuv,
    ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {α, i, -t}, {β2ψ, j + 2 * k, -u * v^2} ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.87b
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_b :
  forall_ijk_tuv,
    ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {α, i, t}, {β2ψ, j + 2 * k, -u * v^2} ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.87c
theorem raw_hom_lift_of_inv_doub_of_α_β2ψ_c :
  forall_ijk_tuv,
    ⁅ {α, i, t} , {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅{α, i, t}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_α_β2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.88
theorem raw_hom_lift_of_commutator_of_β2ψ_αβψ :
  forall_ijk_tuv,
    ⁅ {β2ψ, j + 2 * k, u * v^2},
      {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2} ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_commutator_of_β2ψ_αβψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.89a
theorem raw_hom_lift_of_interchange_of_α2β2ψ_a :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆
      = ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
          {βψ, j + k, u * v} ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_interchange_of_α2β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.89b
theorem raw_hom_lift_of_interchange_of_α2β2ψ_b :
  forall_ijk_tuv,
    ⁅ {ψ, k, -v / 2} * {αβ, i + j, t * u} * {ψ, k, v} * {αβ, i + j, -t * u} * {ψ, k, -v / 2},
      {βψ, j + k, u * v} ⁆
      = ⁅ ⁅ {α, i, t}, {β2ψ, j + 2 * k, 2 * u * v^2} ⁆, {β, j, u} ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_interchange_of_α2β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.90
theorem raw_hom_lift_of_commutator_of_ψ_αβ_β2ψ :
  forall_ijk_tuv,
    ⁅ {ψ, k, v}, ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_commutator_of_ψ_αβ_β2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.91a
theorem raw_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.91b
theorem raw_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.92a
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_a :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, -u * v^2} ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.92b
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_b :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {αβ, i + j, -t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.92c
theorem raw_hom_lift_of_inv_doub_of_αβ_β2ψ_c :
  forall_ijk_tuv,
    ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
    * ⁅ {αβ, i + j, t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆
      = ⁅ {αβ, i + j, 2 * t * u}, {β2ψ, j + 2 * k, u * v^2} ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_αβ_β2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.93a
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_a :
  forall_ijk_tuv,
    ⁅ {β, i, t},
      ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
      = ⁅ {β, i, -t}, ⁅ {α, i, -t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_a [i, j, k, hi, hj, hk, t, u, v]

-- 8.93b
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_b :
  forall_ijk_tuv,
    ⁅ {β, i, t}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
    * ⁅ {β, i, -t}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_b [i, j, k, hi, hj, hk, t, u, v]

-- 8.93c
theorem raw_hom_lift_of_inv_doub_of_β_αβ2ψ_c :
  forall_ijk_tuv,
    ⁅ {β, i, t}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
    * ⁅ {β, i, t}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆
      = ⁅ {β, i, 2 * t}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ := by
  raw_hom_tac rels_of_hom_lift_of_inv_doub_of_β_αβ2ψ_c [i, j, k, hi, hj, hk, t, u, v]

-- 8.94
theorem raw_hom_lift_of_commutator_of_βψ_αβ2ψ :
  forall_ijk_tuv,
    ⁅ {βψ, j + k, u * v}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_commutator_of_βψ_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

-- 8.95
theorem raw_hom_lift_of_commutator_of_β2ψ_αβ2ψ :
  forall_ijk_tuv,
    ⁅ {β2ψ, j + 2 * k, u * v^2}, ⁅ {α, i, t}, {β2ψ, j + 2 * k, u * v^2} ⁆ ⁆ = 1 := by
  raw_hom_tac rels_of_hom_lift_of_commutator_of_β2ψ_αβ2ψ [i, j, k, hi, hj, hk, t, u, v]

theorem refl_of_homog_and_nonhomog :
  ∀ S ∈ homog_and_nonhomog_sets F,
    ∀ r ∈ S, (weakB3Large F).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  intro rel hrel r hr
  simp only [homog_and_nonhomog_sets] at hrel
  sorry

theorem refl_of_def : ∀ S ∈ def_sets F, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  sorry

theorem b3large_valid : ReflDeg.refl_valid (weakB3Large F) :=
  ⟨refl_of_homog_and_nonhomog, refl_of_def⟩

end UnpackingPresentation

/-! ### Helper commute theorems -/

declare_B3Large_expr_as_thm α αβ
declare_B3Large_expr_as_thm β αβ
declare_B3Large_expr_as_thm α ψ
declare_B3Large_expr_as_thm β βψ
declare_B3Large_expr_as_thm β β2ψ
declare_B3Large_expr_as_thm ψ β2ψ
declare_B3Large_expr_as_thm βψ β2ψ

include Fchar
-- 8.108
theorem expand_βψ_as_ψ_β_ψ_β_ψ :
  forall_ij_tu 1 1,
    {βψ, i + j, t * u} = {ψ, i, -t/2} * {β, j, u} * {ψ, i, t} * {β, j, -u} * {ψ, i, -t/2} := by
  intro i j hi hj t u
  have := calc
    ⁅{β, j, u}, {ψ, i, t}⁆ = {βψ, i + j, t * u} * {β2ψ, j + 2 * i, u * t^2} := by rw [commutator_of_β_ψ]; group
    _ = {β2ψ, j + 2 * i, u * t^2} * {βψ, i + j, t * u} := by rw [comm_left, comm_of_βψ_β2ψ]; group
    _ = ⁅{ψ, i, t / 2}, {βψ, i + j, t * u}⁆ * {βψ, i + j, t * u} := by rw [comm_of_ψ_βψ]; field_simp; group
    _ = {ψ, i, t / 2} * {βψ, i + j, t * u} * {ψ, i, t / 2}⁻¹ := by group
  calc
    {βψ, i + j, t * u} = {ψ, i, t / 2}⁻¹ * ⁅{β, j, u}, {ψ, i, t}⁆ * {ψ, i, t / 2} := by rw [this]; group
    _ = {ψ, i, t / 2}⁻¹ * {β, j, u} * {ψ, i, t} * {β, j, u}⁻¹ * {ψ, i, t}⁻¹ * {ψ, i, t / 2} := by group
    _ = {ψ, i, -t / 2} * {β, j, u} * {ψ, i, t} * {β, j, -u} * {ψ, i, -t} * {ψ, i, t / 2} := by rw [inv_of_ψ, inv_of_β, inv_of_ψ]; group
    _ = {ψ, i, -t / 2} * {β, j, u} * {ψ, i, t} * {β, j, -u} * {ψ, i, -t / 2} := by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, lin_of_ψ]; field_simp; group

omit Fchar

-- 8.109
theorem expand_αβ_as_α_β_α_β :
  forall_ij_tu α β,
    {αβ, i + j, t * u} = {α, i, t} * {β, j, u} * {α, i, -t} * {β, j, -u} := by
  intro i j hi hj t u
  calc
    {αβ, i + j, t * u} = ⁅{α, i, t}, {β, j, u}⁆ := by rw [comm_of_α_β, one_mul]
    _ = {α, i, t} * {β, j, u} * {α, i, -t} * {β, j, -u} := by rw [commutatorElement_def, inv_of_α, inv_of_β]

-- 8.110
theorem expand_β2ψ_as_ψ_βψ_ψ_βψ :
  forall_ij_tu β ψ,
    {β2ψ, i + j, 2 * t * u} = {ψ, i, t} * {βψ, j, u} * {ψ, i, -t} * {βψ, j, -u} := by
  intro i j hi hj t u
  calc
    {β2ψ, i + j, 2 * t * u} = ⁅{ψ, i, t}, {βψ, j, u}⁆ := by rw [comm_of_ψ_βψ, mul_assoc]
    _ = {ψ, i, t} * {βψ, j, u} * {ψ, i, -t} * {βψ, j, -u} := by rw [commutatorElement_def, inv_of_ψ, inv_of_βψ]

-- 8.111
@[group_reassoc]
theorem expr_β_α_as_αβ_α_β :
  forall_ij_tu α β,
    {β, j, u} * {α, i, t} = {αβ, i + j, -t * u} * {α, i, t} * {β, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ, i + j, -t * u} * {α, i, t} * {β, j, u} = {αβ, i + j, t * u}⁻¹ * {α, i, t} * {β, j, u} := by rw [inv_of_αβ]; group
    _ = ⁅{α, i, t}, {β, j, u}⁆⁻¹ * {α, i, t} * {β, j, u} := by rw [comm_of_α_β, one_mul];
    _ = {β, j, u} * {α, i, t} := by group
  exact this.symm

-- 8.112a
@[group_reassoc]
theorem expr_ψ_β_as_β_ψ_βψ_β2ψ :
  forall_ij_tu 1 1,
  {ψ, j, u} * {β, i, t} = {β, i, t} * {ψ, j, u} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, t * u^2} := by
  intro i j hi hj t u
  calc
    {ψ, j, u} * {β, i, t} = {β, i, t} * {ψ, j, u} * ⁅{β, i, t}⁻¹, {ψ, j, u}⁻¹⁆⁻¹ := by group
    _ = {β, i, t} * {ψ, j, u} * ⁅{β, i, -t}, {ψ, j, -u}⁆⁻¹ := by chev_simp
    _ = {β, i, t} * {ψ, j, u} * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, -t * u^2})⁻¹ := by grw [commutator_of_β_ψ]; field_simp; group
    _ = {β, i, t} * {ψ, j, u} * {β2ψ, i + 2 * j, -t * u^2}⁻¹ * {βψ, i + j, t * u}⁻¹ := by group
    _ = {β, i, t} * {ψ, j, u} * {β2ψ, i + 2 * j, t * u^2} * {βψ, i + j, -t * u} := by grw [neg_mul, neg_mul, inv_of_β2ψ, inv_of_βψ, inv_inv]
    _ = {β, i, t} * {ψ, j, u} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, t * u^2} := by grw [expr_βψ_β2ψ_as_β2ψ_βψ (add_le_add hi hj) (add_le_add hi (mul_le_mul_of_nonneg_left hj (by trivial)))]


-- 8.112b
@[group_reassoc]
theorem expr_ψ_β_as_β2ψ_βψ_β_ψ :
  forall_ij_tu 1 1,
    {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := by
  intro i j hi hj t u
  have h₁ : ⁅{β, i, t}, {ψ, j, u}⁆ = {βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} := by rw [commutator_of_β_ψ]; group
  have h₂ := congrArg (HMul.hMul ({β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u})) (reorder_left_of_eq_comm h₁)
  calc
    {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, t * u^2}⁻¹ * {βψ, i + j, t * u}⁻¹ * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} * {ψ, j, u} * {β, i, t}) := by group
    _ = {β2ψ, i + 2 * j, -(t * u^2)} * {βψ, i + j, -(t * u)} * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} * {ψ, j, u} * {β, i, t}) := by rw [inv_of_βψ, inv_of_β2ψ]
    _ = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * ({βψ, i + j, t * u} * {β2ψ, i + 2 * j, t * u^2} * {ψ, j, u} * {β, i, t}) := by group
    _ = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * ({β, i, t} * {ψ, j, u}) := by rw [h₂]
    _ = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := by group

-- 8.112c
omit Fchar
@[group_reassoc]
theorem expr_ψ_β_as_β_β2ψ_βψ_ψ :
  forall_ij_tu 1 1,
  {ψ, j, u} * {β, i, t} = {β, i, t} * {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {ψ, j, u} := by
  intro i j hi hj t u
  calc
    {ψ, j, u} * {β, i, t} = {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {β, i, t} * {ψ, j, u} := expr_ψ_β_as_β2ψ_βψ_β_ψ hi hj t u
    _ = {β2ψ, i + 2 * j, -t * u^2} * ({βψ, i + j, -t * u} * {β, i, t}) * {ψ, j, u} := rfl
    _ = {β2ψ, i + 2 * j, -t * u^2} * ({β, i, t} * {βψ, i + j, -t * u}) * {ψ, j, u} := by rw [triv_comm_iff_commutes.1 (comm_of_β_βψ _ _ t (-t * u))]
    _ = ({β2ψ, i + 2 * j, -t * u^2} * {β, i, t}) * {βψ, i + j, -t * u} * {ψ, j, u} := rfl
    _ = ({β, i, t} * {β2ψ, i + 2 * j, -t * u^2}) * {βψ, i + j, -t * u} * {ψ, j, u} := by rw [triv_comm_iff_commutes.1 (comm_of_β_β2ψ _ _ t (-t * u^2))]

-- 8.112d
@[group_reassoc]
theorem expr_ψ_β_as_β_βψ_β2ψ_ψ :
  forall_ij_tu β ψ,
    {ψ, j, u} * {β, i, t} = {β, i, t} * {βψ, i + j, -t * u} * {β2ψ, i + 2 * j, -t * u^2} * {ψ, j, u} := by
  intro i j hi hj t u
  calc
    {ψ, j, u} * {β, i, t} = {β, i, t} * {β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u} * {ψ, j, u} := expr_ψ_β_as_β_β2ψ_βψ_ψ hi hj t u
    _ = {β, i, t} * ({β2ψ, i + 2 * j, -t * u^2} * {βψ, i + j, -t * u}) * {ψ, j, u} := rfl
    _ = {β, i, t} * ({βψ, i + j, -t * u} * {β2ψ, i + 2 * j, -t * u^2}) * {ψ, j, u} := by rw [triv_comm_iff_commutes.1 (comm_of_βψ_β2ψ _ _ (-t * u) (-t * u^2))]

-- 8.113a
@[group_reassoc]
theorem expr_ψ_βψ_as_βψ_β2ψ_ψ :
  forall_ij_tu ψ βψ,
    {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {β2ψ, i + j, 2 * t * u} * {ψ, i, t} := by
  intro i j hi hj t u
  calc
    {ψ, i, t} * {βψ, j, u} = {β2ψ, i + j, 2 * (t * u)} * {βψ, j, u} * {ψ, i, t} := reorder_left_of_eq_comm (comm_of_ψ_βψ  hi hj t u)
    _ = {βψ, j, u} * {β2ψ, i + j, 2 * (t * u)} * {ψ, i, t} := by rw [triv_comm_iff_commutes.1 (comm_of_βψ_β2ψ _ _ u (2 * (t * u)))]
    _ = {βψ, j, u} * {β2ψ, i + j, 2 * t * u} * {ψ, i, t} := by group

-- 8.113b
@[group_reassoc]
theorem expr_ψ_βψ_as_βψ_ψ_β2ψ :
  forall_ij_tu ψ βψ,
    {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {ψ, i, t} * {β2ψ, i + j, 2 * t * u} := by
  intro i j hi hj t u
  calc
    {ψ, i, t} * {βψ, j, u} = {βψ, j, u} * {β2ψ, i + j, 2 * t * u} * {ψ, i, t} := expr_ψ_βψ_as_βψ_β2ψ_ψ hi hj t u
    _ = {βψ, j, u} * ({β2ψ, i + j, 2 * t * u} * {ψ, i, t}) := rfl
    _ = {βψ, j, u} * ({ψ, i, t} * {β2ψ, i + j, 2 * t * u}) := by rw [triv_comm_iff_commutes.1 (comm_of_ψ_β2ψ _ _ t (2 * t * u))]

-- 8.114a
@[group_reassoc]
theorem expr_βψ_ψ_as_ψ_β2ψ_βψ :
  forall_ij_tu ψ βψ,
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {β2ψ, i + j, -2 * t * u} * {βψ, j, u} := by
  intro i j hi hj t u
  calc
    {βψ, j, u} * {ψ, i, t} = ({βψ, j, u} * {ψ, i, t} * {β2ψ, i + j, 2 * t * u}) * {β2ψ, i + j, 2 * t * u}⁻¹ := by group
    _ = ({ψ, i, t} * {βψ, j, u}) * {β2ψ, i + j, 2 * t * u}⁻¹ := by rw [expr_ψ_βψ_as_βψ_ψ_β2ψ hi hj]
    _ = ({ψ, i, t} * {βψ, j, u}) * {β2ψ, i + j, -2 * t * u} := by rw [inv_of_β2ψ]; group
    _ = {ψ, i, t} * ({βψ, j, u} * {β2ψ, i + j, -2 * t * u}) := rfl
    _ = {ψ, i, t} * ({β2ψ, i + j, -2 * t * u} * {βψ, j, u}) := by rw [triv_comm_iff_commutes.1 (comm_of_βψ_β2ψ _ _ u (-2 * t * u))]

-- 8.114b
@[group_reassoc]
theorem expr_βψ_ψ_as_ψ_βψ_β2ψ :
  forall_ij_tu ψ βψ,
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * {βψ, j, u} * {β2ψ, i + j, -2 * t * u} := by
  intro i j hi hj t u
  calc
    {βψ, j, u} * {ψ, i, t} = {ψ, i, t} * ({β2ψ, i + j, -2 * t * u} * {βψ, j, u}) := expr_βψ_ψ_as_ψ_β2ψ_βψ hi hj t u
    _ = {ψ, i, t} * ({βψ, j, u} * {β2ψ, i + j, -2 * t * u}) := by rw [triv_comm_iff_commutes.1 (comm_of_βψ_β2ψ _ _ u (-2 * t * u))]

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) -/
private lemma homog_lift_of_comm_of_αβ_βψ (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : F), ⁅ { αβ, i + j, t}, {βψ, j + k, u} ⁆ = 1 := by
  intro t u
  let t₁ : F := match i with
    | 1 => t
    | 0 => 0
  let t₀ : F := match i with
    | 1 => 0
    | 0 => t
  let u₁ : F := match j with
    | 1 => 1
    | 0 => 0
  let u₀ : F := match j with
    | 1 => 0
    | 0 => 1
  let v₁ : F := match k with
    | 1 => u
    | 0 => 0
  let v₀ : F := match k with
    | 1 => 0
    | 0 => u
  have hf_i : i ∈ [0,1] := mem_list_range_iff_le.mp hi
  have hf_j : j ∈ [0,1] := mem_list_range_iff_le.mp hj
  have hf_k : k ∈ [0,1] := mem_list_range_iff_le.mp hk
  have id₁ : {αβ, i + j, t} = {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp only [t₀, t₁, u₀, u₁, v₀, v₁]
        simp only [add_zero, mul_zero, zero_mul, mul_one, zero_add]
        repeat rw [id_of_αβ]
        simp only [one_mul, mul_one]
      )
    )
  have id₂ : {βψ, j + k, u} = {βψ, 2, u₁ * v₁} * {βψ, 1, u₁ * v₀ + u₀ * v₁} * {βψ, 0, u₀ * v₀} := by (
    fin_cases hf_i, hf_j, hf_k
    all_goals (
      simp only [t₀, t₁, u₀, u₁, v₀, v₁]
      simp only [add_zero, mul_zero, zero_mul, one_mul, zero_add]
      repeat rw [id_of_βψ]
      simp only [one_mul, mul_one]
    )
  )
  rw [id₁, id₂, raw_nonhomog_lift_of_comm_of_αβ_βψ]

private lemma comm_of_αβ_βψ_20 : ∀ (t u : F), ⁅ {αβ, 2, t}, {βψ, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {βψ, 1, u} _ ({αβ, 1, t + 1} * {αβ, 0, 1})
  · mul_assoc_l
    rw [←raw_nonhomog_lift_of_comm_of_αβ_βψ t 1 1 1 0 u]
    simp only [one_mul, mul_one, mul_zero, add_zero]
    rw [id_of_βψ]
    rw [one_mul]
  · rw [←homog_lift_of_comm_of_αβ_βψ 1 1 0 (by trivial) (by trivial) (by trivial) t u]
  · apply triv_comm_mul_left
    rw [←homog_lift_of_comm_of_αβ_βψ 0 1 0 (by trivial) (by trivial) (by trivial) (t+1) u]
    rw [←homog_lift_of_comm_of_αβ_βψ 0 0 1 (by trivial) (by trivial) (by trivial) 1 u]
  apply triv_comm_mul_left
  rw [←homog_lift_of_comm_of_αβ_βψ 1 0 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [←homog_lift_of_comm_of_αβ_βψ 0 0 0 (by trivial) (by trivial) (by trivial) 1 u]

-- symmetric to proof of `comm_of_αβ_βγ_20`
private lemma comm_of_αβ_βψ_02 : ∀ (t u : F), ⁅ {αβ, 0, t}, {βψ, 2, u} ⁆ = 1 := by
  intro t u
  have : ⁅ {αβ, 0, t}, {βψ, 2, u} ⁆ = ReflDeg.refl_symm b3large_valid ⁅ {αβ, 2, t}, {βψ, 0, u} ⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, comm_of_αβ_βψ_20, map_one]

private lemma image_of_homog_lift_of_comm_of_αβ_βψ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ βψ.height)
    : ((i, j) ∈ ij_jk_image) → ∀ (t u : F), ⁅ {αβ, i, t}, {βψ, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  rcases this with ⟨ ⟨i', j', k'⟩, ⟨ h_in_cube, h_f ⟩ ⟩
  rcases mem_range_of_boolean_cube _ h_in_cube with ⟨ hi', hj', hk' ⟩
  have h_f' : i = i' + j' ∧ j = j' + k' := by rw [← Prod.mk.injEq, ← h_f, f_ij_jk]
  rcases h_f' with ⟨ rfl, rfl ⟩
  rw [←homog_lift_of_comm_of_αβ_βψ i' j' k' hi' hj' hk' t u]

-- 8.115
theorem trivial_comm_of_αβ_βψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ βψ := by
  intro i j hi hj t u
  have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ ((i, j) ∈ ij_jk_image) := by
    rw [ij_jk_image]
    simp only [PosRootSys.height, height] at *
    simp -- should fix
    omega
  rcases this with ( ⟨ rfl, rfl ⟩ | ⟨rfl, rfl⟩ | hij )
  · rw [←comm_of_αβ_βψ_02 t u]
  · rw [←comm_of_αβ_βψ_20 t u]
  · exact image_of_homog_lift_of_comm_of_αβ_βψ hi hj hij _ _

@[group_reassoc]
theorem expr_αβ_βψ_as_βψ_αβ :
  forall_ij_tu αβ βψ,
    {αβ, i, t} * {βψ, j, u} = {βψ, j, u} * {αβ, i, t} := by
  intro i j hi hj t u
  rw [triv_comm_iff_commutes.1 (trivial_comm_of_αβ_βψ _ _ t u)]

/- ### Establishing α + β + ψ -/

private lemma interchange_αβψ_refl_v :
  forall_ijk_tu 1 1 1,
  {ψ, k, -1/2} * {αβ, i + j, t * u} * {ψ, k, 1} * {αβ, i + j, -t * u} * {ψ, k, -1/2} = {βψ, j + k, -u/2} * {α, i, t} * {βψ, j + k, u} * {α, i, -t} * {βψ, j + k, -u/2} := by
  intro i j k hi hj hk t u
  rw [raw_hom_lift_of_interchange_of_αβψ hi hj hk t u 1]
  simp only [mul_one]

private lemma interchange_αβψ_refl_u :
  forall_ijk_tu 1 1 1,
  {ψ, k, -u/2} * {αβ, i + j, t} * {ψ, k, u} * {αβ, i + j, -t} * {ψ, k, -u/2} = {βψ, j + k, -u/2} * {α, i, t} * {βψ, j + k, u} * {α, i, -t} * {βψ, j + k, -u/2} := by
  intro i j k hi hj hk t u
  rw [←mul_one t, ←neg_mul, raw_hom_lift_of_interchange_of_αβψ hi hj hk t 1 u]
  simp only [neg_mul, one_mul, mul_one]

private lemma interchange_αβψ_trans_βψ_α :
  forall_ijk_tu 1 1 1,
  {βψ, j + k, -1/2} * {α, i, t * u} * {βψ, j + k, 1} * {α, i, -t * u} * {βψ, j + k, -1/2} = {βψ, j + k, -u/2} * {α, i, t} * {βψ, j + k, u} * {α, i, -t} * {βψ, j + k, -u/2} := by
  intro i j k hi hj hk t u
  have aux₁ := raw_hom_lift_of_interchange_of_αβψ hi hj hk t u 1
  have aux₂ := raw_hom_lift_of_interchange_of_αβψ hi hj hk (t * u) 1 1
  simp only [one_mul, mul_one] at aux₁
  simp only [one_mul, mul_one, ←neg_mul] at aux₂
  rwa [aux₂] at aux₁

private lemma interchange_αβψ_trans_ψ_αβ :
  forall_ijk_tu 1 1 1,
  {ψ, k, -1 / 2} * {αβ, i + j, t * u} * {ψ, k, 1} * {αβ, i + j, -t * u} * {ψ, k, -1 / 2} = {ψ, k, -u / 2} * {αβ, i + j, t} * {ψ, k, u} * {αβ, i + j, -t} * {ψ, k, -u / 2} := by
  intro i j k hi hj hk t u
  have aux₁ := raw_hom_lift_of_interchange_of_αβψ hi hj hk 1 t u
  have aux₂ := raw_hom_lift_of_interchange_of_αβψ hi hj hk 1 (t * u) 1
  simp only [one_mul, mul_one, neg_mul] at aux₁
  simp only [one_mul, mul_one, neg_mul] at aux₂
  rwa [←aux₁, ←neg_mul] at aux₂

-- height 0
private lemma expand_αβψ_as_βψ_α_βψ_α_βψ_00 :
  ∀ t u : F, {αβψ, 0, t * u} = {βψ, 0, -u/2} * {α, 0, t} * {βψ, 0, u} * {α, 0, -t} * {βψ, 0, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 0 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_00 :
  ∀ t u : F, {αβψ, 0, t * u} = {ψ, 0, -u/2} * {αβ, 0, t} * {ψ, 0, u} * {αβ, 0, -t} * {ψ, 0, -u/2} := by
  intro t u
  rw [expand_αβψ_as_βψ_α_βψ_α_βψ_00, ←@interchange_αβψ_refl_v _ _ 0 0 0 (by trivial) (by trivial) (by trivial),
  interchange_αβψ_trans_ψ_αβ (by trivial) (by trivial) (by trivial)]

-- height 1
private lemma expand_αβψ_as_βψ_α_βψ_α_βψ_01 :
  ∀ t u : F, {αβψ, 1, t * u} = {βψ, 1, -u/2} * {α, 0, t} * {βψ, 1, u} * {α, 0, -t} * {βψ, 1, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 1 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_01 :
  ∀ t u : F, {αβψ, 1, t * u} = {ψ, 1, -u/2} * {αβ, 0, t} * {ψ, 1, u} * {αβ, 0, -t} * {ψ, 1, -u/2} := by
  intro t u
  rw [expand_αβψ_as_βψ_α_βψ_α_βψ_01, @interchange_αβψ_refl_u _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_10 :
  ∀ t u : F, {αβψ, 1, t * u} = {ψ, 0, -u/2} * {αβ, 1, t} * {ψ, 0, u} * {αβ, 1, -t} * {ψ, 0, -u/2} := by
  intro t u
  rw [expand_αβψ_as_βψ_α_βψ_α_βψ_01, ←@interchange_αβψ_refl_v _ _ 0 1 0 (by trivial) (by trivial) (by trivial),
  interchange_αβψ_trans_ψ_αβ (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_βψ_α_βψ_α_βψ_10 :
  ∀ t u : F, {αβψ, 1, t * u} = {βψ, 0, -u/2} * {α, 1, t} * {βψ, 0, u} * {α, 1, -t} * {βψ, 0, -u/2} := by
  intro t u
  rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_10, @interchange_αβψ_refl_u _ _ 1 0 0 (by trivial) (by trivial) (by trivial)]

-- height 2
private lemma expand_αβψ_as_βψ_α_βψ_α_βψ_11 :
  ∀ t u : F, {αβψ, 2, t * u} = {βψ, 1, -u/2} * {α, 1, t} * {βψ, 1, u} * {α, 1, -t} * {βψ, 1, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 2 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_20 :
  ∀ t u : F, {αβψ, 2, t * u} = {ψ, 0, -u/2} * {αβ, 2, t} * {ψ, 0, u} * {αβ, 2, -t} * {ψ, 0, -u/2} := by
  intro t u
  rw [expand_αβψ_as_βψ_α_βψ_α_βψ_11, @interchange_αβψ_refl_u _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_11 :
  ∀ t u : F, {αβψ, 2, t * u} = {ψ, 1, -u/2} * {αβ, 1, t} * {ψ, 1, u} * {αβ, 1, -t} * {ψ, 1, -u/2} := by
  intro t u
  rw [expand_αβψ_as_βψ_α_βψ_α_βψ_11, @interchange_αβψ_refl_u _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_βψ_α_βψ_α_βψ_02 :
  ∀ t u : F, {αβψ, 2, t * u} = {βψ, 2, -u/2} * {α, 0, t} * {βψ, 2, u} * {α, 0, -t} * {βψ, 2, -u/2} := by
  intro t u
  rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_11, @interchange_αβψ_refl_u _ _ 0 1 1 (by trivial) (by trivial) (by trivial)]

-- height 3
private lemma expand_αβψ_as_βψ_α_βψ_α_βψ_12 :
  ∀ t u : F, {αβψ, 3, t * u} = {βψ, 2, -u/2} * {α, 1, t} * {βψ, 2, u} * {α, 1, -t} * {βψ, 2, -u/2} := by
  intro t u
  have := @def_of_αβψ _ _ 3 (by trivial) (t * u)
  unfold split_3_into_1_2 at this
  rw [←this, ←neg_mul, @interchange_αβψ_trans_βψ_α _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_21 :
  ∀ t u : F, {αβψ, 3, t * u} = {ψ, 1, -u/2} * {αβ, 2, t} * {ψ, 1, u} * {αβ, 2, -t} * {ψ, 1, -u/2} := by
  intro t u
  rw [expand_αβψ_as_βψ_α_βψ_α_βψ_12, @interchange_αβψ_refl_u _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]

-- 8.116a
theorem expand_αβψ_as_ψ_αβ_ψ_αβ_ψ :
  forall_ij_tu 2 1,
    {αβψ, i + j, t * u} = {ψ, j, -u/2} * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * {ψ, j, -u/2} := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_00]
  | 1, 0 => rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_10]
  | 0, 1 => rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_01]
  | 2, 0 => rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_20]
  | 1, 1 => rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_11]
  | 2, 1 => rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ_21]

-- 8.116b
theorem expand_αβψ_as_βψ_α_βψ_α_βψ :
  forall_ij_tu 1 2,
  {αβψ, i + j, t * u} = {βψ, j, -u/2} * {α, i, t} * {βψ, j, u} * {α, i, -t} * {βψ, j, -u/2} := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expand_αβψ_as_βψ_α_βψ_α_βψ_00]
  | 1, 0 => rw [expand_αβψ_as_βψ_α_βψ_α_βψ_10]
  | 0, 1 => rw [expand_αβψ_as_βψ_α_βψ_α_βψ_01]
  | 0, 2 => rw [expand_αβψ_as_βψ_α_βψ_α_βψ_02]
  | 1, 1 => rw [expand_αβψ_as_βψ_α_βψ_α_βψ_11]
  | 1, 2 => rw [expand_αβψ_as_βψ_α_βψ_α_βψ_12]

-- 8.117
theorem trivial_comm_of_α_αβψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk α αβψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height ψ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  rw [←one_mul u]
  grw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hj₁ hj₂, expr_α_ψ_as_ψ_α hi hj₂,
  expr_α_αβ_as_αβ_α hi hj₁, expr_α_ψ_as_ψ_α hi hj₂, expr_α_αβ_as_αβ_α hi hj₁,
  expr_α_ψ_as_ψ_α hi hj₂]

@[group_reassoc]
theorem expr_α_αβψ_as_αβψ_α :
  forall_ij_tu 1 3,
    {α, i, t} * {αβψ, j, u} = {αβψ, j, u} * {α, i, t} := by
  intro i j hi hj t u
  rw [triv_comm_iff_commutes.1 (trivial_comm_of_α_αβψ _ _ t u)]

-- 8.118
theorem trivial_comm_of_αβ_αβψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ αβψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height ψ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  have : {αβψ, j₁ + j₂, u} = {αβψ, j₂ + j₁, u} := by group
  rw [this]
  rw [←one_mul u]
  grw [expand_αβψ_as_βψ_α_βψ_α_βψ hj₂ hj₁,
  expr_αβ_βψ_as_βψ_αβ hi hj₁, ←expr_α_αβ_as_αβ_α hj₂ hi, expr_αβ_βψ_as_βψ_αβ hi hj₁, ←expr_α_αβ_as_αβ_α hj₂ hi,
  expr_αβ_βψ_as_βψ_αβ hi hj₁]

@[group_reassoc]
theorem expr_αβ_αβψ_as_αβψ_αβ :
  forall_ij_tu 2 3,
    {αβ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {αβ, i, t} := by
  intro i j hi hj t u
  rw [triv_comm_iff_commutes.1 (trivial_comm_of_αβ_αβψ _ _ t u)]

-- 8.119
theorem trivial_comm_of_β_αβψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk β αβψ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height ψ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  have : {αβψ, j₁ + j₂, u} = {αβψ, j₂ + j₁, u} := by group
  rw [this]
  rw [←one_mul u]
  grw [expand_αβψ_as_βψ_α_βψ_α_βψ hj₂ hj₁, expr_β_βψ_as_βψ_β hi hj₁,
  expr_β_α_as_αβ_α_β hj₂ hi, expr_β_βψ_as_βψ_β hi hj₁, expr_β_α_as_αβ_α_β hj₂ hi,
  expr_β_βψ_as_βψ_β hi hj₁, ←expr_α_αβ_as_αβ_α hj₂ (add_le_add hj₂ hi),
  expr_αβ_βψ_as_βψ_αβ (add_le_add hj₂ hi) hj₁, neg_neg, neg_mul, one_mul, inv_of_αβ,
  inv_mul_cancel_right]


@[group_reassoc]
theorem expr_β_αβψ_as_αβψ_β :
  forall_ij_tu 1 3,
    {β, i, t} * {αβψ, j, u} = {αβψ, j, u} * {β, i, t} := by
  intro i j hi hj t u
  rw [triv_comm_iff_commutes.1 (trivial_comm_of_β_αβψ _ _ t u)]

-- 8.120a
private lemma inv_doub_of_αβψ_a :
  forall_i_t αβψ,
    {αβψ, i, t} * {αβψ, i, -t} = 1 := by
  intro i hi t
  rcases decompose αβ.height ψ.height i hi with ⟨ i₁, i₂, ⟨ rfl, hi₁, hi₂ ⟩ ⟩
  have : (-(1 : F) / 2) = -((1 : F) / 2) := by ring
  rw [←mul_one t, expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂, mul_one]
  have expand := expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂ t (-1)
  rw [mul_neg_one, neg_neg] at expand
  grw [expand, neg_neg, this]

-- restatement of 8.120a using our naming conventions
theorem inv_of_αβψ :
  forall_i_t αβψ,
    {αβψ, i, -t} = {αβψ, i, t}⁻¹ := by
  intro i hi t
  have := eq_inv_of_mul_eq_one_left (inv_doub_of_αβψ_a hi (-t))
  rw [neg_neg] at this
  exact this


-- 8.120b
include Fchar
theorem doub_of_αβψ :
  forall_i_t αβψ,
    {αβψ, i, t} * {αβψ, i, t} = {αβψ, i, 2 * t} := by
  intros i hi t
  rcases decompose αβ.height ψ.height i hi with ⟨ i₁, i₂, ⟨ rfl, hi₁, hi₂ ⟩ ⟩
  rw [←mul_one t]
  grw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂]
  have := raw_hom_lift_of_doub_of_αβψ hi₁ hi₂ t 1 1
  rw [mul_one, neg_mul, mul_one, mul_one] at this
  grw [this]
  rw [mul_comm 2 t]
  grw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hi₁ hi₂, neg_div_self Fchar]
  sorry -- CC: I'm very sorry, this broke

lemma half_add_half (u : F) : (u / 2) + (u / 2) = u := by
  have : ((2 : F) / 2) = 1 := (div_eq_one_iff_eq Fchar).mpr rfl
  rw [←mul_two, div_mul_comm, this, one_mul]

-- 8.121
theorem generic_commutator_of_αβ_ψ :
  forall_ij_tu 2 1,
    ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβψ, i + j, t * u} * ⁅{αβψ, i + j, -t * u}, {ψ, j, u / 2}⁆
    ∧ ⁅{αβ, i, t}, {ψ, j, u}⁆ = ⁅{αβψ, i + j, t * u}, {ψ, j, u / 2}⁆⁻¹ * {αβψ, i + j, t * u} := by
  intro i j hi hj t u
  set x := {αβ, i, t} with hx
  set y := {ψ, j, u/2} with hy
  have xinv : x⁻¹ = {αβ, i, -t} := by rw [inv_of_αβ]
  have ysquare : y^2 = {ψ, j, u} := by
    rw [pow_two, lin_of_ψ, ←two_mul, mul_div_left_comm, div_self Fchar, mul_one]
  have yinv : y⁻¹ = {ψ, j, -(u / 2)} := by rw [inv_of_ψ]
  have x_star_y : (x ⋆ y) = {αβψ, i + j, t * u} := by
    unfold star x y
    grw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hi hj, neg_div 2 u, inv_of_ψ, pow_two, inv_of_αβ,
    lin_of_ψ, half_add_half Fchar u]
  have x_star_y_inv : (x ⋆ y)⁻¹ = {αβψ, i + j, -t * u} := by
    rw [x_star_y, eq_inv_of_mul_eq_one_left (inv_doub_of_αβψ_a (add_le_add hi hj) (t * u)), inv_inv, neg_mul]
  rw [←ysquare, ←x_star_y, ←x_star_y_inv]
  exact ⟨(star_commutator x y).symm, (commutator_star x y).symm⟩

-- 8.122
theorem generic_commutator_of_α_βψ :
  forall_ij_tu 1 2,
    ⁅{α, i, t}, {βψ, j, u}⁆ = {αβψ, i + j, t * u} * ⁅{αβψ, i + j, -t * u}, {βψ, j, u / 2}⁆
    ∧ ⁅{α, i, t}, {βψ, j, u}⁆ = ⁅{αβψ, i + j, t * u}, {βψ, j, u / 2}⁆⁻¹ * {αβψ, i + j, t * u} := by
  intro i j hi hj t u
  set x := {α, i, t} with hx
  set y := {βψ, j, u / 2} with hy
  have ysquare : y^2 = {βψ, j, u} := by
    rw [pow_two, hy, lin_of_βψ, half_add_half Fchar u]
  have x_star_y : (x ⋆ y) = {αβψ, i + j, t * u} := by
    unfold star x y
    grw [expand_αβψ_as_βψ_α_βψ_α_βψ hi hj, neg_div 2 u, inv_of_βψ, pow_two, lin_of_βψ, half_add_half Fchar u, inv_of_α]
  have x_star_y_inv : (x ⋆ y)⁻¹ = {αβψ, i + j, -t * u} := by
    rw [x_star_y, eq_inv_of_mul_eq_one_left (inv_doub_of_αβψ_a (add_le_add hi hj) (t * u)), inv_inv, neg_mul]
  rw [←ysquare, ←x_star_y, ←x_star_y_inv]
  exact ⟨(star_commutator x y).symm, (commutator_star x y).symm⟩

-- 8.123
omit Fchar
theorem lift_hom_interchange_of_αβ2ψ :
  forall_ijk_tuv,
    ⁅{αβψ, i + j + k, t * u}, {ψ, k, v}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u * v}⁆ := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, mul_zero, id_of_ψ, id_of_β2ψ]; group
  have expand_αβ2ψ := raw_hom_lift_of_interchange_of_αβ2ψ hi hj hk t (u / v) v
  have : -2 * (u / v) * v^2 = -2 * u * v := by field_simp; group
  rw [this] at expand_αβ2ψ
  have expand_αβψ := expand_αβψ_as_ψ_αβ_ψ_αβ_ψ (add_le_add hi hj) hk (t * (u / v)) v
  have : t * (u / v) * v = t * u := by field_simp
  rw [this] at expand_αβψ
  grw [←expand_αβ2ψ, expand_αβψ, neg_mul]


-- 8.124
theorem lift_hom_commutator_of_βψ_α_β2ψ :
  forall_ijk_tuv,
    ⁅{βψ, j + k, t}, ⁅{α, i, u}, {β2ψ, j + 2 * k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, id_of_β2ψ]; group
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_βψ]; group
  have hβψ := raw_hom_lift_of_commutator_of_βψ_α_β2ψ hi hj hk u (t^2 / v) (v / t)
  have : t^2 / v * (v / t) = t := by rw [pow_two]; field_simp
  rw [this] at hβψ
  have : t^2 / v * (v / t)^2 = v := by field_simp; group
  rw [this] at hβψ
  exact hβψ

-- 8.125a
theorem lift_hom_inv_doub_of_α_β2ψ_a :
  forall_ij_tu 1 3,
    ⁅{α, i, t}, {β2ψ, j, u}⁆ = ⁅{α, i, -t}, {β2ψ, j, -u}⁆ := by
  intro i j hi hj t u
  rcases decompose' j hj with ⟨j₁, j₂, ⟨ rfl, hj₁, hj₂⟩ ⟩
  have := raw_hom_lift_of_inv_doub_of_α_β2ψ_a hi hj₁ hj₂ t u 1
  field_simp at this
  exact this

-- 8.125b
theorem lift_hom_inv_doub_of_α_β2ψ_b :
  forall_ij_tu α β2ψ,
    ⁅{α, i, t}, {β2ψ, j, u}⁆ * ⁅{α, i, t}, {β2ψ, j, -u}⁆ = 1 := by
  intro i j hi hj t u
  rcases decompose' j hj with ⟨j₁, j₂, ⟨ rfl, hj₁, hj₂⟩ ⟩
  have := raw_hom_lift_of_inv_doub_of_α_β2ψ_b hi hj₁ hj₂ t u 1
  field_simp at this
  exact this

theorem inv_of_commutator_of_α_β2ψ :
  forall_ij_tu α β2ψ,
    ⁅{α, i, t}, {β2ψ, j, u}⁆⁻¹ = ⁅{α, i, t}, {β2ψ, j, -u}⁆ := by
  intro i j hi hj t u
  exact inv_eq_of_mul_eq_one_right (lift_hom_inv_doub_of_α_β2ψ_b hi hj t u)

-- 8.125c
theorem lift_hom_inv_doub_of_α_β2ψ_c :
  forall_ij_tu α β2ψ,
    ⁅{α, i, t}, {β2ψ, j, u}⁆ * ⁅{α, i, t}, {β2ψ, j, u}⁆ = ⁅{α, i, t}, {β2ψ, j, 2 * u}⁆ := by
  intro i j hi hj t u
  rcases decompose' j hj with ⟨j₁, j₂, ⟨ rfl, hj₁, hj₂⟩ ⟩
  have := raw_hom_lift_of_inv_doub_of_α_β2ψ_c hi hj₁ hj₂ t u 1
  field_simp at this
  exact this

-- 8.126
theorem lift_hom_commutator_of_β2ψ_αβψ :
  forall_ijk_tu α β ψ,
    ⁅{β2ψ, j + 2 * k, t}, {αβψ, i + j + k, u}⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_β2ψ]; group
  have expand_β2ψ := raw_hom_lift_of_commutator_of_β2ψ_αβψ hi hj hk (u / t) t 1
  rw [←mul_one u, expand_αβψ_as_ψ_αβ_ψ_αβ_ψ (add_le_add hi hj) hk u 1]
  field_simp at expand_β2ψ
  have : -(u * t) / t = -u := by field_simp
  rw [this] at expand_β2ψ
  exact expand_β2ψ

-- 8.127
theorem comm_of_ψ_α_β2ψ :
  forall_ijk_tuv ψ α β2ψ,
    ⁅{ψ, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.mpr
  rw [commutatorElement_def]
  grw [←inv_of_α, ←inv_of_β2ψ, ←expr_α_ψ_as_ψ_α hj hi, expr_ψ_β2ψ_as_β2ψ_ψ hi hk,
  ←expr_α_ψ_as_ψ_α hj hi, expr_ψ_β2ψ_as_β2ψ_ψ hi hk]

@[group_reassoc]
theorem expr_ψ_comm_α_β2ψ_as_comm_α_β2ψ_ψ :
  forall_ijk_tuv ψ α β2ψ,
    {ψ, i, t} * ⁅{α, j, u}, {β2ψ, k, v}⁆ = ⁅{α, j, u}, {β2ψ, k, v}⁆ * {ψ, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_ψ_α_β2ψ hi hj hk t u v)

-- 8.128
theorem comm_of_α_αβψ_ψ :
  forall_ijk_tuv α αβψ ψ,
    ⁅{α, i, t}, ⁅{αβψ, j, u}, {ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.mpr
  rw [commutatorElement_def]
  grw [←inv_of_αβψ hj, expr_α_αβψ_as_αβψ_α hi hj, expr_α_ψ_as_ψ_α hi hk,
  expr_α_αβψ_as_αβψ_α hi hj, expr_α_ψ_as_ψ_α hi hk]

@[group_reassoc]
theorem expr_α_comm_αβψ_ψ_as_comm_αβψ_ψ_α :
  forall_ijk_tuv α αβψ ψ,
    {α, i, t} * ⁅{αβψ, j, u}, {ψ, k, v}⁆ = ⁅{αβψ, j, u}, {ψ, k, v}⁆ * {α, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_α_αβψ_ψ hi hj hk t u v)

-- 8.129 ??????????????????????????????????????????????????
theorem comm_of_α_α_β2ψ :
  forall_ijk_tuv α α β2ψ,
    ⁅{α, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  rcases decompose' k hk with ⟨ j', k', ⟨ rfl, hj', hk' ⟩ ⟩
  have := lift_hom_interchange_of_αβ2ψ hj hj' hk' 1 u v
  sorry

@[group_reassoc]
theorem expr_α_comm_α_β2ψ_as_comm_α_β2ψ_α :
  forall_ijk_tuv α α β2ψ,
    {α, i, t} * ⁅{α, j, u}, {β2ψ, k, v}⁆ = ⁅{α, j, u}, {β2ψ, k, v}⁆ * {α, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_α_α_β2ψ hi hj hk t u v)

-- Proposition 8.130
include Fchar
theorem sufficient_conditions_for_commutator_of_αβψ_and_ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 1)
  (hyp : ∀ (t u v : F), ⁅{βψ, j, t}, ⁅{α, i, u}, {β2ψ, j + k, v}⁆⁆ = 1),
  ∀ (t u v : F), ⁅{αβψ, i + j, t * u}, {ψ, k, v}⁆ = ⁅{α, i, t}, {β2ψ, j + k, -2 * u * v}⁆ := by
  intro i j k hi hj hk hyp t u v
  apply eq_comm_of_reorder_left
  grw [expand_αβψ_as_βψ_α_βψ_α_βψ hi hj, expr_βψ_ψ_as_ψ_β2ψ_βψ hk hj, expr_α_ψ_as_ψ_α hi hk, expr_βψ_ψ_as_ψ_β2ψ_βψ hk hj, expr_α_ψ_as_ψ_α hi hk, expr_βψ_ψ_as_ψ_β2ψ_βψ hk hj]
  have : -2 * v * (-u / 2) = u * v := by field_simp; group
  rw [this]
  have hyp' := fun t' u' v' ↦ triv_comm_iff_commutes.1 (hyp t' u' v')
  have aux₁ : {β2ψ, k + j, u * v} * {α, i, t} = ⁅{α, i, t}, {β2ψ, j + k, -u * v}⁆ * {α, i, t} * {β2ψ, j + k, u * v} := by
    rw [comm_left_rev, inv_of_commutator_of_α_β2ψ hi (add_le_add hk hj), neg_mul]
    group
  have aux₂ : {α, i, -t} * {β2ψ, k + j, u * v} = {β2ψ, j + k, u * v} * {α, i, -t} * ⁅{α, i, t}, {β2ψ, j + k, -u * v}⁆ := by
    rw [← inv_of_α, neg_mul, ← inv_of_β2ψ]
    group
  have aux₃ := calc
   {β2ψ, j + k, u * v} * {β2ψ, k + j, -2 * v * u} = {β2ψ, j + k, u * v} * {β2ψ, j + k, -2 * u * v} := by group
   _ = {β2ψ, j + k, -u * v} := by rw [lin_of_β2ψ]; ring_nf
  have aux₄ : {β2ψ, j + k, -u * v} * {β2ψ, j + k, u * v} = 1 := by
    rw [neg_mul, ← inv_of_β2ψ, inv_mul_cancel]
  stop -- CC: I'm very sorry, this broke
  grw [←expr_βψ_β2ψ_as_β2ψ_βψ hj (add_le_add hk hj) (-u / 2), aux₁, aux₂,
  expr_βψ_β2ψ_as_β2ψ_βψ hj (add_le_add hj hk) u (u * v), aux₃, aux₄, hyp' (-u/2),
  expr_ψ_comm_α_β2ψ_as_comm_α_β2ψ_ψ hk hi (add_le_add hj hk), expr_α_comm_α_β2ψ_as_comm_α_β2ψ_α hi hi (add_le_add hj hk),
  hyp' u, mul_one, expr_α_comm_α_β2ψ_as_comm_α_β2ψ_α hi hi (add_le_add hj hk), hyp' (-u/2), expr_ψ_comm_α_β2ψ_as_comm_α_β2ψ_ψ hk hi (add_le_add hj hk),
  lift_hom_inv_doub_of_α_β2ψ_c hi (add_le_add hj hk)]
  group

-- 8.131
theorem partial_A_interchange_of_αβ2ψ :
  ∀ (t u v : F),
  ⁅{αβψ, 0, t * u}, {ψ, 1, v}⁆ = ⁅{α, 0, t}, {β2ψ, 1, -2 * u * v}⁆ := by
  apply @sufficient_conditions_for_commutator_of_αβψ_and_ψ _ _ Fchar 0 0 1 (by trivial) (by trivial) (by trivial)
  intro t u v
  have h₁ := @lift_hom_interchange_of_αβ2ψ _ _ 1 0 0 (by trivial) (by trivial) (by trivial) u (-v/2) 1
  have h := @lift_hom_interchange_of_αβ2ψ _ _ 0 1 0 (by trivial) (by trivial) (by trivial) u (-v/2) 1
  norm_num at h₁
  norm_num at h
  rw [h₁] at h
  have : -(2 * (-v / 2)) = v := by field_simp
  rw [this] at h
  have h₁ := @lift_hom_commutator_of_βψ_α_β2ψ _ _ 1 0 0 (by trivial) (by trivial) (by trivial) t u v
  rwa [h] at h₁


-- Proposition 8.132
theorem sufficient_conditions_for_commutator_of_βψ_and_α_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 3) (hyp : ∀ (t u : F), ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1),
  ∀ (t u v : F), ⁅{βψ, i, t}, ⁅{α, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk hyp t u v
  apply triv_comm_iff_commutes.2
  have hyp' := fun t' u' ↦ triv_comm_iff_commutes.1 (hyp t' u')
  have aux₁ : ∀ (u' : F), {βψ, i, t} * {α, j, u'} = {α, j, u'} * ⁅{α, j, -u'}, {βψ, i, t}⁆ * {βψ, i, t} := by
    intro u'; rw [← inv_of_α]; group
  have aux₂ : ∀ (u' : F), {βψ, i, t} * {α, j, u'} = ⁅{α, j, u'}, {βψ, i, t}⁆⁻¹ * {α, j, u'} * {βψ, i, t} := by
    intro u'; group
  stop -- CC: I'm sorry, I'm breaking everything
  grw [commutatorElement_def, ←inv_of_α, ←inv_of_β2ψ, aux₁ u, expr_βψ_β2ψ_as_β2ψ_βψ hi hk, aux₂ (-u), expr_βψ_β2ψ_as_β2ψ_βψ hi hk]
  suffices h : ⁅{α, j, -u}, {βψ, i, t}⁆ * {β2ψ, k, v} * ⁅{α, j, -u}, {βψ, i, t}⁆⁻¹ = {β2ψ, k, v} by grw [h]
  apply mul_inv_eq_iff_eq_mul.2
  have := (generic_commutator_of_α_βψ Fchar hj hi (-u) t).1
  field_simp at this
  have := calc
    ⁅{α, j, -u}, {βψ, i, t}⁆ = {αβψ, j + i, -(u * t)} * ⁅{αβψ, j + i, u * t}, {βψ, i, t / 2}⁆ := this
    _ = {αβψ, i + j, -t * u} * ⁅{αβψ, i + j, t * u}, {βψ, i, t / 2}⁆ := by group
  grw [this, commutatorElement_def, ←inv_of_αβψ (add_le_add hi hj), ←inv_of_βψ, expr_βψ_β2ψ_as_β2ψ_βψ hi hk,
  hyp' (-(t * u)), expr_βψ_β2ψ_as_β2ψ_βψ hi hk, hyp' (t * u), hyp' (-t * u)]

-- 8.133
theorem partial_comm_of_βψ_α_β2ψ :
  ∀ (t u v : F),
  ⁅{βψ, 2, t}, ⁅{α, 0, u}, {β2ψ, 2, v}⁆⁆ = 1 := by
  apply @sufficient_conditions_for_commutator_of_βψ_and_α_β2ψ _ _ Fchar 2 0 2 (by trivial) (by trivial) Nat.AtLeastTwo.prop
  intro t u
  have := triv_comm_iff_commutes.mp (@lift_hom_commutator_of_β2ψ_αβψ _ _ 1 0 1 (by trivial) (by trivial) (by trivial) u t)
  apply triv_comm_iff_commutes.mpr
  rw [←this]

-- 8.134
theorem partial_B_interchange_of_αβ2ψ :
  ∀ (t u v : F),
  ⁅{αβψ, 2, t * u}, {ψ, 0, v}⁆ = ⁅{α, 0, t}, {β2ψ, 2, -2 * u * v}⁆ :=
  @sufficient_conditions_for_commutator_of_αβψ_and_ψ _ _ Fchar 0 2 0 (by trivial) (by trivial) (by trivial) (@partial_comm_of_βψ_α_β2ψ _ _ Fchar)

/- ### Establishing α + β + 2ψ -/

private lemma interchange_of_αβ2ψ_trans_α_β2ψ :
  forall_ijk_tu 1 1 1, ⁅{α, i, t * u}, {β2ψ, j + 2 * k, 1}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, u}⁆ := by
  intro i j k hi hj hk t u
  have aux₁ := lift_hom_interchange_of_αβ2ψ hi hj hk (t * u) 1 (-1/2)
  have aux₂ := lift_hom_interchange_of_αβ2ψ hi hj hk t u (-1/2)
  field_simp at aux₁
  field_simp at aux₂
  rwa [aux₁] at aux₂

omit Fchar
private lemma interchange_of_αβ2ψ_refl_u :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t}, {ψ, k, u}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u}⁆ := by
  intro i j k hi hj hk t u
  rw [←mul_one t, lift_hom_interchange_of_αβ2ψ hi hj hk]
  simp only [neg_mul, mul_one]

private lemma interchange_of_αβ2ψ_refl_v :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t * u}, {ψ, k, 1}⁆ = ⁅{α, i, t}, {β2ψ, j + 2 * k, -2 * u}⁆ := by
  intro i j k hi hj hk t u
  rw [lift_hom_interchange_of_αβ2ψ hi hj hk]
  simp only [neg_mul, mul_one]

private lemma interchange_of_αβ2ψ_trans_αβψ_ψ :
  forall_ijk_tu 1 1 1, ⁅{αβψ, i + j + k, t * u}, {ψ, k, 1}⁆ = ⁅{αβψ, i + j + k, t}, {ψ, k, u}⁆ := by
  intro i j k hi hj hk t u
  rw [interchange_of_αβ2ψ_refl_v hi hj hk, interchange_of_αβ2ψ_refl_u hi hj hk]

include Fchar
private lemma interchange_A_of_αβ2ψ_refl_u :
  ∀ t u : F, ⁅{αβψ, 0, t}, {ψ, 1, u}⁆ = ⁅{α, 0, t}, {β2ψ, 1, -2 * u}⁆ := by
  intro t u
  rw [←mul_one t, partial_A_interchange_of_αβ2ψ Fchar]
  simp only [mul_one, neg_mul]

private lemma interchange_A_of_αβ2ψ_refl_v :
  ∀ t u : F, ⁅{αβψ, 0, t * u}, {ψ, 1, 1}⁆ = ⁅{α, 0, t}, {β2ψ, 1, -2 * u}⁆ := by
  intro t u
  rw [partial_A_interchange_of_αβ2ψ Fchar]
  simp only [neg_mul, mul_one]

private lemma interchange_A_of_αβ2ψ_trans_αβψ_ψ :
  ∀ t u : F, ⁅{αβψ, 0, t * u}, {ψ, 1, 1}⁆ = ⁅{αβψ, 0, t}, {ψ, 1, u}⁆ := by
  intro t u
  rw [interchange_A_of_αβ2ψ_refl_v Fchar, interchange_A_of_αβ2ψ_refl_u Fchar]

private lemma interchange_B_of_αβ2ψ_refl_u :
  ∀ t u : F, ⁅{αβψ, 2, t}, {ψ, 0, u}⁆ = ⁅{α, 0, t}, {β2ψ, 2, -2 * u}⁆ := by
  intro t u
  rw [←mul_one t, partial_B_interchange_of_αβ2ψ Fchar]
  simp only [mul_one, neg_mul]

private lemma interchange_B_of_αβ2ψ_refl_v :
  ∀ t u : F, ⁅{αβψ, 2, t * u}, {ψ, 0, 1}⁆ = ⁅{α, 0, t}, {β2ψ, 2, -2 * u}⁆ := by
  intro t u
  rw [partial_B_interchange_of_αβ2ψ Fchar]
  simp only [neg_mul, mul_one]

private lemma interchange_B_of_αβ2ψ_trans_αβψ_ψ :
  ∀ t u : F, ⁅{αβψ, 2, t * u}, {ψ, 0, 1}⁆ = ⁅{αβψ, 2, t}, {ψ, 0, u}⁆ := by
  intro t u
  rw [interchange_B_of_αβ2ψ_refl_v Fchar, interchange_B_of_αβ2ψ_refl_u Fchar]

-- height 0
private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_00 :
  ∀ t u : F, {αβ2ψ, 0, t * u} = ⁅{α, 0, t}, {β2ψ, 0, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 0 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 0 0 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_00 :
  ∀ t u : F, {αβ2ψ, 0, -2 * t * u} = ⁅{αβψ, 0, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_00 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 0 0 0 (by trivial) (by trivial) (by trivial),
  mul_comm t u, interchange_of_αβ2ψ_trans_αβψ_ψ (by trivial) (by trivial) (by trivial)]

-- height 1
private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_01 :
  ∀ t u : F, {αβ2ψ, 1, t * u} = ⁅{α, 0, t}, {β2ψ, 1, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 1 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 0 1 0 (by trivial) (by trivial) (by trivial)]

-- `A` edge
private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_01 :
  ∀ t u : F, {αβ2ψ, 1, -2 * t * u} = ⁅{αβψ, 0, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_01 Fchar, ←interchange_A_of_αβ2ψ_refl_v Fchar,
  mul_comm t u, interchange_A_of_αβ2ψ_trans_αβψ_ψ Fchar]

private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_10 :
  ∀ t u : F, {αβ2ψ, 1, -2 * t * u} = ⁅{αβψ, 1, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_01 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 0 1 0 (by trivial) (by trivial) (by trivial),
  mul_comm t u, @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_10 :
  ∀ t u : F, {αβ2ψ, 1, t * u} = ⁅{α, 1, t}, {β2ψ, 0, u}⁆ := by
  intro t u
  have : t * u = -2 * (-u / 2) * t := by ring_nf; field_simp
  rw [this, expand_αβ2ψ_as_commutator_of_αβψ_ψ_10 Fchar, @interchange_of_αβ2ψ_refl_u _ _ 1 0 0 (by trivial) (by trivial) (by trivial)]
  field_simp

-- height 2
private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_11 :
  ∀ t u : F, {αβ2ψ, 2, t * u} = ⁅{α, 1, t}, {β2ψ, 1, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 2 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 1 1 0 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_20 :
  ∀ t u : F, {αβ2ψ, 2, -2 * t * u} = ⁅{αβψ, 2, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_11 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 1 1 0 (by trivial) (by trivial) (by trivial),
  mul_comm t u, @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 1 1 0 (by trivial) (by trivial) (by trivial)]

-- `B` edge
private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_02 :
  ∀ t u : F, {αβ2ψ, 2, t * u} = ⁅{α, 0, t}, {β2ψ, 2, u}⁆ := by
  intro t u
  have : t * u = -2 * (-u / 2) * t := by ring_nf; field_simp
  rw [this, expand_αβ2ψ_as_commutator_of_αβψ_ψ_20 Fchar, interchange_B_of_αβ2ψ_refl_u Fchar]
  field_simp

private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_11 :
  ∀ t u : F, {αβ2ψ, 2, -2 * t * u} = ⁅{αβψ, 1, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = t * (-2 * u) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_02 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 0 0 1 (by trivial) (by trivial) (by trivial),
  mul_comm t u, interchange_of_αβ2ψ_trans_αβψ_ψ (by trivial) (by trivial) (by trivial)]

-- height 3
private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_12 :
  ∀ t u : F, {αβ2ψ, 3, t * u} = ⁅{α, 1, t}, {β2ψ, 2, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 3 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 1 0 1 (by trivial) (by trivial) (by trivial)]

-- `A` edge
private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_30 :
  ∀ t u : F, {αβ2ψ, 3, -2 * t * u} = ⁅{αβψ, 3, u}, {ψ, 0, t}⁆ := by
  intro t u
  have : -2 * t * u = u * (-2 * t) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_12 Fchar]
  have : ⁅{αβψ, 3, u}, {ψ, 0, t}⁆ = ReflDeg.refl_symm b3large_valid ⁅{αβψ, 0, u}, {ψ, 1, t}⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this]
  have : ⁅{α, 1, u}, {β2ψ, 2, -2 * t}⁆ = ReflDeg.refl_symm b3large_valid ⁅{α, 0, u}, {β2ψ, 1, -2 * t}⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, interchange_A_of_αβ2ψ_refl_u Fchar]

private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_21 :
  ∀ t u : F, {αβ2ψ, 3, -2 * t * u} = ⁅{αβψ, 2, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = u * (-2 * t) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_12 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 1 0 1 (by trivial) (by trivial) (by trivial),
  @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 1 0 1 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_03 :
  ∀ t u : F, {αβ2ψ, 3, t * u} = ⁅{α, 0, t}, {β2ψ, 3, u}⁆ := by
  intro t u
  have : t * u = -2 * (-u / 2) * t := by ring_nf; field_simp
  rw [this, expand_αβ2ψ_as_commutator_of_αβψ_ψ_21 Fchar, @interchange_of_αβ2ψ_refl_u _ _ 0 1 1 (by trivial) (by trivial) (by trivial)]
  field_simp

-- height 4
private lemma expand_αβ2ψ_as_commutator_of_α_β2ψ_13 :
  ∀ t u : F, {αβ2ψ, 4, t * u} = ⁅{α, 1, t}, {β2ψ, 3, u}⁆ := by
  intro t u
  have := @def_of_αβ2ψ _ _ 4 (by trivial) (t * u)
  unfold split_4_into_1_3 at this
  rw [←this, @interchange_of_αβ2ψ_trans_α_β2ψ _ _ Fchar 1 1 1 (by trivial) (by trivial) (by trivial)]

private lemma expand_αβ2ψ_as_commutator_of_αβψ_ψ_31 :
  ∀ t u : F, {αβ2ψ, 4, -2 * t * u} = ⁅{αβψ, 3, u}, {ψ, 1, t}⁆ := by
  intro t u
  have : -2 * t * u = u * (-2 * t) := by group
  rw [this, expand_αβ2ψ_as_commutator_of_α_β2ψ_13 Fchar, ←@interchange_of_αβ2ψ_refl_v _ _ 1 1 1 (by trivial) (by trivial) (by trivial),
  @interchange_of_αβ2ψ_trans_αβψ_ψ _ _ 1 1 1 (by trivial) (by trivial) (by trivial)]

-- 8.135a
theorem expand_αβ2ψ_as_commutator_of_α_β2ψ :
  forall_ij_tu 1 3,
    {αβ2ψ, i + j, t * u} = ⁅{α, i, t}, {β2ψ, j, u}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_00 Fchar]
  | 0, 1 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_01 Fchar]
  | 1, 0 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_10 Fchar]
  | 0, 2 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_02 Fchar]
  | 1, 1 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_11 Fchar]
  | 0, 3 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_03 Fchar]
  | 1, 2 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_12 Fchar]
  | 1, 3 => rw [expand_αβ2ψ_as_commutator_of_α_β2ψ_13 Fchar]

-- 8.135b
theorem expand_αβ2ψ_as_commutator_of_αβψ_ψ :
  forall_ij_tu 3 1,
    {αβ2ψ, i + j, -2 * t * u} = ⁅{αβψ, i, u}, {ψ, j, t}⁆ := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_00 Fchar]
  | 1, 0 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_10 Fchar]
  | 0, 1 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_01 Fchar]
  | 1, 1 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_11 Fchar]
  | 2, 0 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_20 Fchar]
  | 2, 1 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_21 Fchar]
  | 3, 0 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_30 Fchar]
  | 3, 1 => rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ_31 Fchar]

-- 8.136
theorem trivial_comm_of_α_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk α αβ2ψ := by
  intro i j hi hj t u
  rcases decompose_4_into_3_1 j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  have expand_αβ2ψ := @expand_αβ2ψ_as_commutator_of_αβψ_ψ _ _ Fchar j₁ j₂ hj₁ hj₂ (-1/2) u
  field_simp at expand_αβ2ψ
  have := @comm_of_α_αβψ_ψ _ _ i j₁ j₂ hi hj₁ hj₂ t u (-1/2)
  rwa [←expand_αβ2ψ] at this

-- 8.137
theorem trivial_comm_of_ψ_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk ψ αβ2ψ := by
  intro i j hi hj t u
  rcases decompose_4_into_3_1 j hj with ⟨ j₂, j₁, ⟨ rfl, hj₂, hj₁ ⟩ ⟩
  have expand_αβ2ψ := @expand_αβ2ψ_as_commutator_of_α_β2ψ _ _ Fchar j₁ j₂ hj₁ hj₂ 1 u
  have := @comm_of_ψ_α_β2ψ _ _ i j₁ j₂ hi hj₁ hj₂ t 1 u
  rw [←expand_αβ2ψ] at this
  rw [←this]
  group

-- 8.138a
private lemma inv_doub_of_αβ2ψ_a :
  forall_i_t αβ2ψ,
    {αβ2ψ, i, t} * {αβ2ψ, i, -t} = 1 := by
  intro i hi t
  rcases decompose_4_into_3_1 i hi with ⟨ i₂, i₁, ⟨ rfl, hi₂, hi₁ ⟩ ⟩
  have := @expand_αβ2ψ_as_commutator_of_α_β2ψ _ _ Fchar i₁ i₂ hi₁ hi₂
  calc
    {αβ2ψ, i₂ + i₁, t} * {αβ2ψ, i₂ + i₁, -t} = {αβ2ψ, i₁ + i₂, t * 1} * {αβ2ψ, i₁ + i₂, t * (-1)} := by group
    _ = ⁅{α, i₁, t}, {β2ψ, i₂, 1}⁆ * ⁅{α, i₁, t}, {β2ψ, i₂, -1}⁆ := by rw [this t 1, this t (-1)]
    _ = 1 := by rw [lift_hom_inv_doub_of_α_β2ψ_b hi₁ hi₂]

theorem inv_of_αβ2ψ :
  forall_i_t αβ2ψ,
    {αβ2ψ, i, -t} = {αβ2ψ, i, t}⁻¹ := by
  intro i hi t
  have := @inv_doub_of_αβ2ψ_a _ _ Fchar i hi t
  rw [eq_inv_of_mul_eq_one_left this, inv_inv]

-- 8.138b
theorem doub_of_αβ2ψ :
  forall_i_t αβ2ψ.height,
    {αβ2ψ, i, t} * {αβ2ψ, i, t} = {αβ2ψ, i, 2 * t} := by
  intro i hi t
  rcases decompose_4_into_3_1 i hi with ⟨ i₂, i₁, ⟨ rfl, hi₂, hi₁ ⟩ ⟩
  have := @expand_αβ2ψ_as_commutator_of_α_β2ψ _ _ Fchar i₁ i₂ hi₁ hi₂
  calc
    {αβ2ψ, i₂ + i₁, t} * {αβ2ψ, i₂ + i₁, t} = {αβ2ψ, i₁ + i₂, 1 * t} * {αβ2ψ, i₁ + i₂, 1 * t} := by group
    _ = ⁅{α, i₁, (1 : F)}, {β2ψ, i₂, t}⁆ * ⁅{α, i₁, (1 : F)}, {β2ψ, i₂, t}⁆ := by rw [this]
    _ = ⁅{α, i₁, (1 : F)}, {β2ψ, i₂, 2 * t}⁆ := by rw [lift_hom_inv_doub_of_α_β2ψ_c hi₁ hi₂]
    _ = {αβ2ψ, i₂ + i₁, 2 * t} := by rw [←this]; group

-- 8.139a
theorem commutator_of_αβ_ψ_a :
  forall_ij_tu 2 1,
    ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, t * u^2} := by
  intro i j hi hj t u
  have aux := expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar (add_le_add hi hj) hj (u / 2) (-t * u)
  have : {αβ2ψ, i + j + j, -2 * (u / 2) * (-t * u)} = {αβ2ψ, i + 2 * j, t * u^2} := by ring_nf; field_simp
  rw [this] at aux
  rw [(generic_commutator_of_αβ_ψ Fchar hi hj t u).1, aux]

-- 8.139b
theorem commutator_of_αβ_ψ_b :
  forall_ij_tu 2 1,
    ⁅{αβ, i, t}, {ψ, j, u}⁆ = {αβ2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} := by
  intro i j hi hj t u
  have aux := expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar (add_le_add hi hj) hj (u / 2) (t * u)
  rw [(generic_commutator_of_αβ_ψ Fchar hi hj t u).2, ←aux, ←inv_of_αβ2ψ Fchar (by simp [PosRootSys.height, height]; omega)]
  ring_nf; field_simp

-- 8.140a
theorem expand_αβ2ψ_as_α_β2ψ_α_β2ψ :
  forall_ij_tu α β2ψ,
    {αβ2ψ, i + j, t * u} = {α, i, t} * {β2ψ, j, u} * {α, i, -t} * {β2ψ, j, -u} := by
  intro i j hi hj t u
  rw [expand_αβ2ψ_as_commutator_of_α_β2ψ Fchar hi hj, ← inv_of_α, ← inv_of_β2ψ, commutatorElement_def]

-- 8.140b
theorem expand_αβ2ψ_as_β2ψ_α_β2ψ_α :
  forall_ij_tu α β2ψ,
    {αβ2ψ, i + j, t * u} = {β2ψ, j, -u} * {α, i, t} * {β2ψ, j, u} * {α, i, -t} := by
  intro i j hi hj t u
  calc
    {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, t * (-u)}⁻¹ := by rw [←inv_of_αβ2ψ Fchar (add_le_add hi hj)]; group
    _ = ⁅{α, i, t}, {β2ψ, j, -u}⁆⁻¹ := by rw [expand_αβ2ψ_as_commutator_of_α_β2ψ Fchar hi hj]
    _ = ⁅{α, i, t}, {β2ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_β2ψ]
    _ = {β2ψ, j, -u} * {α, i, t} * {β2ψ, j, u} * {α, i, -t} := by rw [← inv_of_β2ψ, ← inv_of_α]; group

-- 8.141a
theorem expand_αβ2ψ_as_αβψ_ψ_αβψ_ψ :
  forall_ij_tu αβψ ψ,
    {αβ2ψ, i + j, -2 * t * u} = {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} * {ψ, j, -t} := by
  intro i j hi hj t u
  rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar hi hj, inv_of_αβψ hi, ← inv_of_ψ _ hj, commutatorElement_def];

-- 8.141b
theorem expand_αβ2ψ_as_ψ_αβψ_ψ_αβψ :
  forall_ij_tu αβψ ψ,
    {αβ2ψ, i + j, -2 * t * u} = {ψ, j, -t} * {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} := by
  intro i j hi hj t u
  calc
    {αβ2ψ, i + j, -2 * t * u} = {αβ2ψ, i + j, -2 * (-t) * u}⁻¹ := by rw [←inv_of_αβ2ψ Fchar (add_le_add hi hj)]; group
    _ = ⁅{αβψ, i, u}, {ψ, j, -t}⁆⁻¹ := by rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar hi hj]
    _ = ⁅{αβψ, i, u}, {ψ, j, t}⁻¹⁆⁻¹ := by rw [inv_of_ψ]
    _ = {ψ, j, -t} * {αβψ, i, u} * {ψ, j, t} * {αβψ, i, -u} := by rw [← inv_of_ψ _ hj, inv_of_αβψ hi]; group

-- 8.142a
@[group_reassoc]
theorem expr_α_β2ψ_as_αβ2ψ_β2ψ_α :
  forall_ij_tu α β2ψ,
    {α, i, t} * {β2ψ, j, u} = {αβ2ψ, i + j, t * u} * {β2ψ, j, u} * {α, i, t} := by
  intro i j hi hj t u
  rw [expand_αβ2ψ_as_commutator_of_α_β2ψ Fchar hi hj]
  group

-- 8.142b
@[group_reassoc]
theorem expr_α_β2ψ_as_β2ψ_αβ2ψ_α :
  forall_ij_tu α β2ψ,
    {α, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {αβ2ψ, i + j, t * u} * {α, i, t} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, t * (-u)}⁻¹ := by rw [←inv_of_αβ2ψ Fchar (add_le_add hi hj)]; group
    _ = ⁅{α, i, t}, {β2ψ, j, -u}⁆⁻¹ := by rw [expand_αβ2ψ_as_commutator_of_α_β2ψ Fchar hi hj]
    _ = ⁅{α, i, t}, {β2ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_β2ψ]
  rw [this]
  group

-- 8.142c
@[group_reassoc]
theorem expr_α_β2ψ_as_β2ψ_α_αβ2ψ :
  forall_ij_tu α β2ψ,
    {α, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {α, i, t} * {αβ2ψ, i + j, t * u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, (-t) * (-u)} := by group
    _ = ⁅{α, i, -t}, {β2ψ, j, -u}⁆ := by rw [expand_αβ2ψ_as_commutator_of_α_β2ψ Fchar hi hj]
    _ = ⁅{α, i, t}⁻¹, {β2ψ, j, u}⁻¹⁆ := by rw [inv_of_β2ψ, inv_of_α]
  rw [this]
  group

-- 8.143a
@[group_reassoc]
theorem expr_ψ_αβψ_as_αβψ_αβ2ψ_ψ :
  forall_ij_tu ψ αβψ,
    {ψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {αβ2ψ, i + j, 2 * t * u} * {ψ, i, t} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, 2 * t * u} = {αβ2ψ, j + i, -2 * t * (-u)} := by group
    _ = ⁅{αβψ, j, u}⁻¹, {ψ, i, t}⁆ := by rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar hj hi, inv_of_αβψ hj]
  rw [this]
  group

-- 8.143b
@[group_reassoc]
theorem expr_ψ_αβψ_as_αβψ_ψ_αβ2ψ :
  forall_ij_tu ψ αβψ,
    {ψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {ψ, i, t} * {αβ2ψ, i + j, 2 * t * u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, 2 * t * u} = {αβ2ψ, j + i, -2 * (-t) * (-u)}⁻¹ := by rw [←inv_of_αβ2ψ Fchar (by simp [PosRootSys.height, height] at *; omega)]; group
    _ = ⁅{αβψ, j, u}⁻¹, {ψ, i, t}⁻¹⁆⁻¹ := by rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar hj hi, inv_of_αβψ hj, inv_of_ψ]
  rw [this]
  group

-- 8.144a
@[group_reassoc]
theorem expr_αβψ_ψ_as_αβ2ψ_ψ_αβψ :
  forall_ij_tu ψ αβψ,
    {αβψ, j, u} * {ψ, i, t} = {αβ2ψ, i + j, -2 * t * u} * {ψ, i, t} * {αβψ, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, -2 * t * u} = {αβ2ψ, j + i, -2 * t * u} := by group
    _ = ⁅{αβψ, j, u}, {ψ, i, t}⁆ := by rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar hj hi]
  rw [this]
  group

-- 8.144b
@[group_reassoc]
theorem expr_αβψ_ψ_as_ψ_αβ2ψ_αβψ :
  forall_ij_tu ψ αβψ,
    {αβψ, j, u} * {ψ, i, t} = {ψ, i, t} * {αβ2ψ, i + j, -2 * t * u} * {αβψ, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + j, -2 * t * u} = {αβ2ψ, j + i, -2 * (-t) * u}⁻¹ := by rw [←inv_of_αβ2ψ Fchar (by simp [PosRootSys.height, height] at *; omega)]; group
    _ = ⁅{αβψ, j, u}, {ψ, i, t}⁻¹⁆⁻¹ := by rw [expand_αβ2ψ_as_commutator_of_αβψ_ψ Fchar hj hi, inv_of_ψ]
  rw [this]
  group

-- 8.145a
@[group_reassoc]
theorem expr_αβ_ψ_as_ψ_αβ_αβψ_αβ2ψ :
  forall_ij_tu 2 1,
    {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβ, i, t} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} := by
  intro i j hi hj t u
  have aux := calc
    {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} = {αβψ, i + j, (-t) * (-u)} * {αβ2ψ, i + 2 * j, -t * (-u)^2} := by ring_nf
    _ = ⁅{αβ, i, -t}, {ψ, j, -u}⁆ := by rw [commutator_of_αβ_ψ_a Fchar hi hj]
  have := calc
    {ψ, j, u} * {αβ, i, t} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u ^ 2}
    = {ψ, j, u} * {αβ, i, t} * ({αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2}) := rfl
    _ = {ψ, j, u} * {αβ, i, t} * ⁅{αβ, i, -t}, {ψ, j, -u}⁆ := by rw [aux]
    _ = {ψ, j, u} * {αβ, i, t} * ⁅{αβ, i, t}⁻¹, {ψ, j, u}⁻¹⁆ := by rw [inv_of_αβ, inv_of_ψ]
    _ = {αβ, i, t} * {ψ, j, u} := by group
  exact this.symm

-- 8.145b
@[group_reassoc]
theorem expr_αβ_ψ_as_ψ_αβψ_αβ2ψ_αβ :
  forall_ij_tu 2 1,
    {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβ, i, t} := by
  intro i j hi hj t u
  have aux : {ψ, j, u} * {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβ, i, t} = {ψ, j, u} * ({αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2}) * {αβ, i, t} := rfl
  have := calc
    {αβψ, i + j, t * u} * {αβ2ψ, i + 2 * j, -t * u^2} = {αβψ, i + j, t * (-u)}⁻¹ * {αβ2ψ, i + 2 * j, t * u^2}⁻¹ := by
      rw [←inv_of_αβ2ψ Fchar (by simp [PosRootSys.height, height]; omega), ←inv_of_αβψ (by simp [PosRootSys.height, height]; omega)]; field_simp
    _ = ({αβ2ψ, i + 2 * j, t * (-u)^2} * {αβψ, i + j, t * (-u)})⁻¹ := by ring_nf; group
    _ = ⁅{αβ, i, t}, {ψ, j, -u}⁆⁻¹ := by rw [commutator_of_αβ_ψ_b Fchar hi hj]
    _ = ⁅{αβ, i, t}, {ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_ψ]
  rw [aux, this]
  group

-- 8.145c
@[group_reassoc]
theorem expr_αβ_ψ_as_ψ_αβ2ψ_αβψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (t u : F),
  {αβ, i, t} * {ψ, j, u} = {ψ, j, u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u} * {αβ, i, t} := by
  intro i j hi hj t u
  have aux : {ψ, j, u} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u} * {αβ, i, t} = {ψ, j, u} * ({αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u}) * {αβ, i, t} := rfl
  have := calc
    {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, t * u} = {αβ2ψ, i + 2 * j, t * (-u)^2}⁻¹ * {αβψ, i + j, t * (-u)}⁻¹ := by rw [←inv_of_αβ2ψ Fchar (by simp [PosRootSys.height, height]; omega), ←inv_of_αβψ (by simp [PosRootSys.height, height]; omega)]; field_simp
    _ = ({αβψ, i + j, t * (-u)} * {αβ2ψ, i + 2 * j, t * (-u)^2})⁻¹ := by group
    _ = ⁅{αβ, i, t}, {ψ, j, -u}⁆⁻¹ := by rw [commutator_of_αβ_ψ_a Fchar hi hj]
    _ = ⁅{αβ, i, t}, {ψ, j, u}⁻¹⁆⁻¹ := by rw [inv_of_ψ]
  rw [aux, this]
  group

-- 8.145d
@[group_reassoc]
theorem expr_αβ_ψ_as_αβ2ψ_αβψ_ψ_αβ :
  forall_ij_tu 2 1,
    {αβ, i, t} * {ψ, j, u} = {αβ2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} * {ψ, j, u} * {αβ, i, t} := by
  intro i j hi hj t u
  rw [←commutator_of_αβ_ψ_b Fchar hi hj]
  group

-- 8.146
@[group_reassoc]
theorem expr_ψ_αβ_as_αβ_αβ2ψ_αβψ_ψ :
  forall_ij_tu αβ ψ,
    {ψ, j, u} * {αβ, i, t} = {αβ, i, t} * {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, -t * u} * {ψ, j, u} := by
  intro i j hi hj t u
  have := calc
    {αβ2ψ, i + 2 * j, -t * u^2} * {αβψ, i + j, -t * u} = ⁅{αβ, i, -t}, {ψ, j, u}⁆ := by rw [commutator_of_αβ_ψ_b Fchar hi hj]
    _ = ⁅{αβ, i, t}⁻¹, {ψ, j, u}⁆ := by rw [inv_of_αβ]
  grw [this]
  group
  stop
  done

theorem id_of_αβψ : id_of_root((weakB3Large F).pres_mk, αβψ) := by
  intro i hi
  have := doub_of_αβψ Fchar hi 0
  rw [mul_zero] at this
  exact mul_right_eq_self.1 this

theorem id_of_αβ2ψ : id_of_root((weakB3Large F).pres_mk, αβ2ψ) := by
  intro i hi
  have := doub_of_αβ2ψ Fchar hi 0
  rw [mul_zero] at this
  exact mul_right_eq_self.1 this

-- 8.147a
theorem hom_lift_of_interchange_of_α2β2ψ_a :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u v : F),
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, 2 * u * v}⁆ = ⁅{αβψ, i + j + k, t * u}, {βψ, j + k, v}⁆ := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, mul_zero, mul_zero, zero_mul, id_of_β2ψ, id_of_αβψ Fchar]; group
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, mul_zero, id_of_βψ, id_of_β2ψ]; group
  have aux := raw_hom_lift_of_interchange_of_α2β2ψ_a hi hj hk (t * u / v) (v / u) u
  have : t * u / v * (v / u) = t := by field_simp
  rw [this] at aux
  have : 2 * (v / u) * u ^ 2 = 2 * u * v := by calc
    2 * (v / u) * u ^ 2 = 2 * v * (u^2 / u) := by field_simp
    _ = 2 * v * (u * u / u) := by rw [pow_two]
    _ = 2 * v * u := by rw [mul_div_assoc, div_self hu, mul_one]
    _ = 2 * u * v := mul_right_comm 2 v u
  rw [this] at aux
  have : -(t * u / v) * (v / u) = -t := by ring_nf; field_simp
  rw [this] at aux
  have : v / u * u = v := div_mul_cancel₀ v hu
  rw [this] at aux
  grw [aux, expand_αβψ_as_ψ_αβ_ψ_αβ_ψ (add_le_add hi hj) hk]

-- 8.147b
theorem hom_lift_of_interchange_of_α2β2ψ_b :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u v : F),
  ⁅{αβψ, i + j + k, t}, {βψ, j + k, u * v}⁆ = ⁅{αβ2ψ, i + j + 2 * k, 2 * t * u}, {β, j, v}⁆ := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, mul_zero, zero_mul, id_of_βψ, id_of_αβ2ψ Fchar]; group
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, mul_zero, id_of_βψ, id_of_β]; group
  have aux := raw_hom_lift_of_interchange_of_α2β2ψ_b hi hj hk (t / (u * v)) v u
  have : t / (u * v) * v = t / u := by sorry
  rw [this] at aux
  have : -(t / (u * v)) * v = -(t / u) := by sorry
  rw [this] at aux
  sorry


-- 8.148
omit Fchar
theorem hom_lift_of_commutator_ψ_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u v : F),
  ⁅{ψ, k, t}, ⁅{αβ, i + j, u}, {β2ψ, j + 2 * k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_ψ]; group
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, id_of_β2ψ]; group
  have aux := raw_hom_lift_of_commutator_of_ψ_αβ_β2ψ hi hj hk (u * t * t / v) (v / (t * t)) t
  have : u * t * t / v * (v / (t * t)) = u := by ring_nf; field_simp
  rw [this] at aux
  have : v / (t * t) * t ^ 2 = v := by ring_nf; field_simp
  rw [this] at aux
  exact aux

-- 8.149
theorem hom_lift_of_commutator_αβ_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : F),
  ⁅{αβ, i + j, t}, ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆⁆ = 1 ∧
  ⁅{αβ, i + j, t}, ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, u}⁆⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, id_of_β2ψ]
    exact ⟨by group, by group⟩
  have aux₁ := raw_hom_lift_of_commutator_of_αβ_αβ_β2ψ_a hi hj hk (t / u) u 1
  have aux₂ := raw_hom_lift_of_commutator_of_αβ_αβ_β2ψ_b hi hj hk (t / u) u 1
  have : t / u * u = t := by field_simp
  rw [this, pow_two, one_mul, mul_one] at aux₁
  rw [this, pow_two, one_mul, mul_one] at aux₂
  have : -(t / u) * u = -t := by field_simp
  rw [this] at aux₂
  exact ⟨aux₁, aux₂⟩

-- 8.150
theorem hom_lift_of_inv_doub_of_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : F),
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ = ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, -u}⁆ ∧
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ * ⁅{αβ, i + j, -t}, {β2ψ, j + 2 * k, u}⁆ = 1 ∧
  ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ * ⁅{αβ, i + j, t}, {β2ψ, j + 2 * k, u}⁆ = ⁅{αβ, i + j, 2 * t}, {β2ψ, j + 2 * k, u}⁆ := by
  intro i j k hi hj hk t u
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, neg_zero, id_of_β2ψ]
    exact ⟨by group, by group, by group⟩
  have aux₁ := raw_hom_lift_of_inv_doub_of_αβ_β2ψ_a hi hj hk (t / u) u 1
  have aux₂ := raw_hom_lift_of_inv_doub_of_αβ_β2ψ_b hi hj hk (t / u) u 1
  have aux₃ := raw_hom_lift_of_inv_doub_of_αβ_β2ψ_c hi hj hk (t / u) u 1
  have eq1 : (t / u) * u = t := by field_simp
  have eq2 : u * 1^2 = u := by rw [pow_two, mul_one, mul_one]
  have eq3 : -(t / u) * u = -t := by field_simp
  have eq4 : -u * 1^2 = -u := by rw [pow_two, mul_one, mul_one]
  have eq5 : 2 * (t / u) * u = 2 * t := by field_simp
  rw [eq1, eq2, eq3, eq4] at aux₁
  rw [eq1, eq2, eq3] at aux₂
  rw [eq1, eq2, eq5] at aux₃
  exact ⟨aux₁, aux₂, aux₃⟩

-- 8.151
include Fchar
theorem hom_lift_of_inv_doub_of_β_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u : F),
  ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = ⁅{β, i, -t}, {αβ2ψ, i + j + 2 * k, -u}⁆ ∧
  ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ * ⁅{β, i, -t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 ∧
  ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ * ⁅{β, i, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = ⁅{β, i, 2 * t}, {αβ2ψ, i + j + 2 * k, u}⁆ := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · sorry
  sorry

-- 8.152
theorem hom_lift_of_commutator_βψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u : F),
  ⁅{βψ, j + k, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_βψ]; group
  have aux := raw_hom_lift_of_commutator_of_βψ_αβ2ψ hi hj hk (u / t) t 1
  rw [pow_two, mul_one, mul_one, mul_one] at aux
  have aux' := @expand_αβ2ψ_as_commutator_of_α_β2ψ _ _ Fchar i (j + 2 * k) hi (by omega) (u / t) t
  have : {αβ2ψ, i + (j + 2 * k), u / t * t} = {αβ2ψ, i + j + 2 * k, u} := by field_simp; group
  rw [this] at aux'
  rw [aux', aux]

-- 8.153
theorem hom_lift_of_commutator_of_β2ψ_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) (t u : F),
  ⁅{β2ψ, j + 2 * k, t}, {αβ2ψ, i + j + 2 * k, u}⁆ = 1 := by
  intro i j k hi hj hk t u
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, id_of_β2ψ]; group
  have aux := raw_hom_lift_of_commutator_of_β2ψ_αβ2ψ hi hj hk (u / t) t 1
  rw [pow_two, mul_one, mul_one] at aux
  have aux' := @expand_αβ2ψ_as_commutator_of_α_β2ψ _ _ Fchar i (j + 2 * k) hi (by omega) (u / t) t
  have : {αβ2ψ, i + (j + 2 * k), u / t * t}  = {αβ2ψ, i + j + 2 * k, u} := by field_simp; group
  rw [this] at aux'
  rw [aux', aux]

-- 8.154
omit Fchar
theorem comm_of_βψ_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ βψ.height) (hj : j ≤ αβ.height) (hk : k ≤ β2ψ.height) (t u v : F),
  ⁅{βψ, i, t}, ⁅{αβ, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, ←inv_of_αβ, ←inv_of_β2ψ, ←expr_αβ_βψ_as_βψ_αβ hj hi, expr_βψ_β2ψ_as_β2ψ_βψ hi hk,
  ←expr_αβ_βψ_as_βψ_αβ hj hi, expr_βψ_β2ψ_as_β2ψ_βψ hi hk]

theorem expr_βψ_comm_αβ_β2ψ_as_comm_αβ_β2ψ_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ βψ.height) (hj : j ≤ αβ.height) (hk : k ≤ β2ψ.height) (t u v : F),
  {βψ, i, t} * ⁅{αβ, j, u}, {β2ψ, k, v}⁆ = ⁅{αβ, j, u}, {β2ψ, k, v}⁆ * {βψ, i, t} := by
  intro i j k hi hj hk t u v
  exact triv_comm_iff_commutes.1 (comm_of_βψ_αβ_β2ψ hi hj hk t u v)

-- 8.155
theorem comm_of_αβ_βψ_αβψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ βψ.height) (hk : k ≤ αβψ.height) (t u v : F),
  ⁅{αβ, i, t}, ⁅{βψ, j, u}, {αβψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, ←inv_of_βψ, ←inv_of_αβψ hk, expr_αβ_βψ_as_βψ_αβ hi hj, expr_αβ_αβψ_as_αβψ_αβ hi hk,
  expr_αβ_βψ_as_βψ_αβ hi hj, expr_αβ_αβψ_as_αβψ_αβ hi hk]

-- 8.156
theorem comm_of_β_αβ_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβ.height) (hk : k ≤ β2ψ.height) (t u v : F),
  ⁅{β, i, t}, ⁅{αβ, j, u}, {β2ψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, ←inv_of_αβ, ←inv_of_β2ψ, expr_β_αβ_as_αβ_β hi hj, expr_β_β2ψ_as_β2ψ_β hi hk,
  expr_β_αβ_as_αβ_β hi hj, expr_β_β2ψ_as_β2ψ_β hi hk]

-- 8.157
theorem comm_of_β_αβψ_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβψ.height) (hk : k ≤ βψ.height) (t u v : F),
  ⁅{β, i, t}, ⁅{αβψ, j, u}, {βψ, k, v}⁆⁆ = 1 := by
  intro i j k hi hj hk t u v
  apply triv_comm_iff_commutes.2
  grw [commutatorElement_def, ←inv_of_αβψ hj, ←inv_of_βψ, expr_β_αβψ_as_αβψ_β hi hj, expr_β_βψ_as_βψ_β hi hk,
  expr_β_αβψ_as_αβψ_β hi hj, expr_β_βψ_as_βψ_β hi hk]

-- Previous proof of (incorrectly stated) 8.158
include Fchar
example :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 2)
  (h35a : ∀ (t u v : F), ⁅{ψ, j, t}, ⁅{αβ, i, u}, {β2ψ, j + k, v}⁆⁆ = 1)
  (h35b : ∀ (t u v : F), ⁅{αβ, i, t}, ⁅{αβ, i, u}, {β2ψ, j + k, v}⁆⁆ = 1)
  (h35c : ∀ (t u : F), ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, -t}, {β2ψ, j + k, -u}⁆)
  (h35d : ∀ (t u : F), ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ * ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u}⁆),
  ∀ (t u v : F), ⁅{αβψ, i + j, t * u}, {βψ, k, v}⁆ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ := by
  intro i j k hi hj hk h35a h35b h35c h35d t u v
  have h35a' := fun t' u' v' ↦ triv_comm_iff_commutes.1 (h35a t' u' v')
  have h35b' := fun t' u' v' ↦ triv_comm_iff_commutes.1 (h35b t' u' v')
  have aux₀ : 2 * (-u / 2) * v = -u * v := by ring_nf; field_simp
  have eq36 : {β2ψ, j + k, -u * v} * {αβ, i, t} = {αβ, i, t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {β2ψ, j + k, -u * v} := by calc
    {β2ψ, j + k, -u * v} * {αβ, i, t} = {αβ, i, t} * ⁅{αβ, i, -t}, {β2ψ, j + k, -u * v}⁆ * {β2ψ, j + k, -u * v} := by
      rw [← inv_of_αβ, neg_mul, ← inv_of_β2ψ]; group
    _ = {αβ, i, t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {β2ψ, j + k, -u * v} := by grw [h35c]; ring_nf
  have eq37 : {αβ, i, -t} * {β2ψ, j + k, -u * v} = {β2ψ, j + k, -u * v} * {αβ, i, -t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ := by
    rw [← inv_of_αβ, neg_mul, ← inv_of_β2ψ]; group
  have := calc
    {αβψ, i + j, t * u} * {βψ, k, v} = {ψ, j, -u/2} * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * {ψ, j, -u/2} * {βψ, k, v} := by rw [expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hi hj]
    _ = {βψ, k, v} * {ψ, j, -u/2} * {β2ψ, j + k, -u * v} * {αβ, i, t} * {β2ψ, j + k, 2 * u * v} * {ψ, j, u} * {αβ, i, -t} * {β2ψ, j + k, -u * v} * {ψ, j, -u/2} := by
      grw [expr_ψ_βψ_as_βψ_β2ψ_ψ hj hk, aux₀, expr_αβ_βψ_as_βψ_αβ hi hk, expr_ψ_βψ_as_βψ_β2ψ_ψ hj hk, expr_αβ_βψ_as_βψ_αβ hi hk, expr_ψ_βψ_as_βψ_ψ_β2ψ hj hk, aux₀]
    _ = {βψ, k, v} * {ψ, j, -u/2} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {αβ, i, t} * {β2ψ, j + k, -u * v} * {β2ψ, j + k, 2 * u * v} * {ψ, j, u} * {β2ψ, j + k, -u * v} * {αβ, i, -t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {ψ, j, -u/2} := by
      grw [eq36, eq37, h35b']
    _ = {βψ, k, v} * {ψ, j, -u/2} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {ψ, j, -u/2} := by
      grw [expr_ψ_β2ψ_as_β2ψ_ψ hj (add_le_add hj hk)]; ring_nf
      rw [id_of_β2ψ, one_mul]
    _ = ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * ⁅{αβ, i, t}, {β2ψ, j + k, u * v}⁆ * {βψ, k, v} * {ψ, j, -u/2} * {αβ, i, t} * {ψ, j, u} * {αβ, i, -t} * {ψ, j, -u/2} := by
      grw [h35a', expr_βψ_comm_αβ_β2ψ_as_comm_αβ_β2ψ_βψ hk hi (add_le_add hj hk), h35b', h35a', h35b', h35a', expr_βψ_comm_αβ_β2ψ_as_comm_αβ_β2ψ_βψ hk hi (add_le_add hj hk)]
    _ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ * {βψ, k, v} * {αβψ, i + j, t * u} := by
      grw [h35d, expand_αβψ_as_ψ_αβ_ψ_αβ_ψ hi hj]
  exact eq_comm_of_reorder_left this

-- 8.158 (revised)
theorem sufficient_conditions_for_commutator_of_αβψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 2)
  (h35a : ∀ (t u v : F), ⁅{ψ, j, t}, ⁅{αβ, i, u}, {β2ψ, j + k, v}⁆⁆ = 1)
  (h35b : ∀ (t u : F), ⁅{αβ, i, t}, ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆⁆ = 1 ∧ ⁅{αβ, i, t}, ⁅{αβ, i, -t}, {β2ψ, j + k, u}⁆⁆ = 1)
  (h35c : ∀ (t u : F), ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, -t}, {β2ψ, j + k, -u}⁆)
  (h35d : ∀ (t u : F), ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ * ⁅{αβ, i, t}, {β2ψ, j + k, u}⁆ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u}⁆),
  ∀ (t u v : F), ⁅{αβψ, i + j, t * u}, {βψ, k, v}⁆ = ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ := by
  sorry

lemma interchange_of_α2β2ψ_aux :
  ∀ (t u : F), ⁅{αβ, 1, t}, {β2ψ, 1, u}⁆ = ⁅{αβ, 0, t}, {β2ψ, 2, u}⁆ := by
    intro t u
    have := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    have this' := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 0 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at this'
    specialize this t (u/2) 1; norm_num at this; field_simp at this
    specialize this' t (u/2) 1; norm_num at this'; field_simp at this'
    exact Eq.trans this (Eq.symm this')

-- 8.159a
theorem partial_A_interchange_of_α2β2ψ_a :
  ∀ (t u v : F),
  ⁅{αβψ, 0, t * u}, {βψ, 2, v}⁆ = ⁅{αβ, 0, t}, {β2ψ, 2, 2 * u * v}⁆ := by
  have h1 := @hom_lift_of_commutator_ψ_αβ_β2ψ F _ 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  have h2 := @hom_lift_of_commutator_αβ_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h3 := @hom_lift_of_inv_doub_of_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h4 := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have := @sufficient_conditions_for_commutator_of_αβψ_and_βψ _ _ Fchar 0 0 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  · intro t u v
    have := @interchange_of_α2β2ψ_aux _ _ Fchar u v
    rw [← this]
    specialize h1 t u v; norm_num at h1; exact h1
  · exact h2
  · exact fun t u ↦ (h3 t u).left
  · intro t u
    have h4a := h4 t 1 u; norm_num at h4a
    have h4b := h4 (2*t) (1/2) u; norm_num at h4b; field_simp at h4b
    specialize h3 t u
    grw [h3.right.right, h4a, h4b]

-- 8.159b
theorem partial_A_interchange_of_α2β2ψ_b :
  ∀ (t u v : F),
  ⁅{αβψ, 2, t * u}, {βψ, 0, v}⁆ = ⁅{αβ, 1, t}, {β2ψ, 1, 2 * u * v}⁆ := by
  have := @sufficient_conditions_for_commutator_of_αβψ_and_βψ _ _ Fchar 1 1 0 (by norm_num) (by norm_num) (by norm_num)
  have h := @interchange_of_α2β2ψ_aux _ _ Fchar
  have h1 := @hom_lift_of_commutator_ψ_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h2 := @hom_lift_of_commutator_αβ_αβ_β2ψ F _ 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  have h3 := @hom_lift_of_inv_doub_of_αβ_β2ψ F _ 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h4 := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  · intro t u v
    rw [h u v]
    specialize h1 t u v; norm_num at h1; exact h1
  · exact h2
  · intro t u
    have h1a := h t u
    have h1b := h (-t) (-u)
    grw [h1a, h1b]
    exact (h3 t u).left
  · intro t u
    specialize h3 t u; norm_num at h3
    rw [h t u]
    grw [h3.right.right]
    rw [h t (2*u)]
    have h4a := h4 t 1 u; norm_num at h4a
    have h4b := h4 (2*t) (1/2) u; norm_num at h4b; field_simp at h4b
    grw [h4a, h4b]

-- 8.160
include Fchar
theorem more_sufficient_conditions_for_commutator_of_αβψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 1)
  (h38a : ∀ (t u v : F), ⁅{β, k, t}, ⁅{αβ2ψ, i + j, u}, {β, k, v}⁆⁆ = 1)
  (h38b : ∀ (t u v : F), ⁅{ψ, j, t}, ⁅{αβ2ψ, i + j, u}, {β, k, v}⁆⁆ = 1)
  (h38c : ∀ (t u : F), ⁅{β, k, u}, {αβ2ψ, i + j, -t}⁆ = ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆)
  (h38d : ∀ (t u : F), ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆ * ⁅{αβ2ψ, i + j, t}, {β, k, u}⁆ = ⁅{αβ2ψ, i + j, 2 * t}, {β, k, u}⁆),
  ∀ (t u v : F), ⁅{αβψ, i, t}, {βψ, j + k, u * v}⁆ = ⁅{αβ2ψ, i + j, 2 * t * u}, {β, k, v}⁆ := by
  intro i j k hi hj hk h38a h38b h38c h38d t u v
  have h39 : {αβ2ψ, i + j, t * u} * {β, k, v} = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {β, k, v} * {αβ2ψ, i + j, t * u} := by group
  have h40 : {β, k, -v} * {αβ2ψ, i + j, t * u}  = {αβ2ψ, i + j, t * u} * {β, k, -v} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ := by
    simp [← h38c, commutatorElement_def, inv_of_β]
    have h1 : {β, k, v}⁻¹ = {β, k, -v} := by grw [inv_of_β]
    have h2 : {αβ2ψ, i + j, t * u}⁻¹ = {αβ2ψ, i + j, -(t * u)} := by
      grw [inv_of_αβ2ψ]
      exact Fchar
      simp [PosRootSys.height, height]
      omega
    rw [← h1, ← h2]
    group
  have h : i + j ≤ αβ2ψ.height := by simp [height]; omega
  have : {αβψ, i, t} * {βψ, j + k, u * v} = ⁅{αβ2ψ, i + j, 2 * t * u}, {β, k, v}⁆ * {βψ, j + k, u * v} * {αβψ, i, t} := by
    nth_rw 1 [expand_βψ_as_ψ_β_ψ_β_ψ]
    grw [expr_αβψ_ψ_as_ψ_αβ2ψ_αβψ,
         ← expr_β_αβψ_as_αβψ_β,
         expr_αβψ_ψ_as_αβ2ψ_ψ_αβψ,
         ← expr_β_αβψ_as_αβψ_β]
    grw [expr_αβψ_ψ_as_αβ2ψ_ψ_αβψ]
    field_simp [add_comm, mul_comm, ← mul_assoc]
    grw [h39, h40]
    have : {ψ, j, u} * {αβ2ψ, i + j, t * u} = {αβ2ψ, i + j, t * u} * {ψ, j, u} := by
      rw [triv_comm_iff_commutes.1]
      rw [trivial_comm_of_ψ_αβ2ψ]
      exact Fchar
    grw [this]
    have : {αβ2ψ, i + j, t * u} * {αβ2ψ, i + j, -(t * u * 2)} * {αβ2ψ, i + j, t * u} = 1 := by
      have : -(t * u * 2) = 2 * (-t * u) := by ring
      rw [this, ← doub_of_αβ2ψ Fchar h]
      group
      rw [inv_of_αβ2ψ]
      simp
      exact Fchar
      simp [PosRootSys.height, height]
      omega
    grw [this]
    grw [h38a, h38b]
    have h1 : {ψ, j, -u / 2} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {ψ, j, -u / 2} := by
      rw [triv_comm_iff_commutes.1]
      exact h38b (-u / 2) (t * u) v
    have h2 : {ψ, j, u} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {ψ, j, u} := by
      rw [triv_comm_iff_commutes.1]
      exact h38b u (t * u) v
    have h3 : {β, k, -v} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {β, k, -v} := by
      rw [triv_comm_iff_commutes.1]
      exact h38a (-v) (t * u) v
    have h4 : {β, k, v} * ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ = ⁅{αβ2ψ, i + j, t * u}, {β, k, v}⁆ * {β, k, v} := by
      rw [triv_comm_iff_commutes.1]
      exact h38a v (t * u) v
    grw [h1, h2, h3, h2, h4, h1, h38d]
    have : {βψ, j + k, u * v} = {ψ, j, -u / 2} * {β, k, v} * {ψ, j, u} * {β, k, -v} * {ψ, j, -u / 2} := by
      rw [← expand_βψ_as_ψ_β_ψ_β_ψ Fchar hj hk u v, mul_comm]
    have h5 : 2 * t * u = t * u * 2 := by
      ring
    grw [h5, ← this]
    repeat assumption
  exact reorder_left_iff_eq_comm.mp this
omit Fchar

-- 8.161
theorem sufficient_conditions_for_commutator_of_αβ2ψ_and_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 3)
  (hyp : ∀ (t u : F), ⁅{β2ψ, k, t}, {αβ2ψ, i + j, u}⁆ = 1),
  ∀ (t u : F), ⁅{β2ψ, i, t}, {αβ2ψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.162a
include Fchar
theorem partial_comm_of_β2ψ_αβ2ψ_a :
  ∀ (t u : F), ⁅{β2ψ, 2, t}, {αβ2ψ, 1, u}⁆ = 1 := by
  have := @sufficient_conditions_for_commutator_of_αβ2ψ_and_β2ψ F _ 2 0 1 (by omega) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  have := @hom_lift_of_commutator_of_β2ψ_αβ2ψ F _ Fchar 1 1 0 (by omega) (by norm_num) (by norm_num)
  norm_num at this
  exact this

-- 8.162b
theorem partial_comm_of_β2ψ_αβ2ψ_b :
  ∀ (t u : F), ⁅{β2ψ, 0, t}, {αβ2ψ, 2, u}⁆ = 1 := by
  have := @sufficient_conditions_for_commutator_of_αβ2ψ_and_β2ψ F _ 0 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  have := @hom_lift_of_commutator_of_β2ψ_αβ2ψ F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this
omit Fchar

-- 8.163
theorem sufficient_conditions_for_commutator_of_ψ_and_αβ2ψ_β :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 4) (hk : k ≤ 1)
  (h41a : ∀ (t u : F), ⁅{β2ψ, 2 * i + k, t}, {αβ2ψ, j, u}⁆ = 1)
  (h41b : ∀ (t u : F), ⁅{βψ, i + k, t}, {αβ2ψ, j, u}⁆ = 1),
  ∀ (t u v : F), ⁅{ψ, i, t}, ⁅{αβ2ψ, j, u}, {β, k, v}⁆⁆ = 1 := by
  sorry

-- 8.164
include Fchar
theorem partial_comm_of_ψ_αβ2ψ_β :
  ∀ (t u v : F), ⁅{ψ, 1, v}, ⁅{αβ2ψ, 1, t}, {β, 0, u}⁆⁆ = 1 := by
  intro t u v
  have := @sufficient_conditions_for_commutator_of_ψ_and_αβ2ψ_β F _ 1 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  exact @partial_comm_of_β2ψ_αβ2ψ_a F _ Fchar
  have := @hom_lift_of_commutator_βψ_αβ2ψ F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

-- 8.165
theorem partial_B_interchange_of_α2β2ψ :
  ∀ (t u v : F), ⁅{αβψ, 0, t}, {βψ, 1, u * v}⁆ = ⁅{αβ2ψ, 1, 2 * t * u}, {β, 0, v}⁆ := by
  have h := @hom_lift_of_inv_doub_of_β_αβ2ψ F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  have := @more_sufficient_conditions_for_commutator_of_αβψ_and_βψ F _ Fchar 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  apply this
  · intro t u v
    have h1 := @hom_lift_of_interchange_of_α2β2ψ_a F _ Fchar 1 0 0 (by norm_num) (by norm_num) (by norm_num) u (1/2) v
    have := @hom_lift_of_interchange_of_α2β2ψ_b F _ Fchar 1 0 0 (by norm_num) (by norm_num) (by norm_num) (u/2) 1 v
    norm_num at h1; norm_num at this; field_simp at h1; field_simp at this
    rw [this] at h1
    have := @comm_of_β_αβ_β2ψ F _ 0 1 0 (by norm_num) (by norm_num) (by norm_num) t u v
    grw [← h1]
    exact this
  · intro t u v
    have := @partial_comm_of_ψ_αβ2ψ_β F _ Fchar u v t
    exact this
  · intro t u
    rcases h (-u) t with ⟨h1, ⟨h2, _⟩⟩
    norm_num at h1
    apply mul_eq_one_iff_eq_inv.mp at h2
    simp only [neg_neg, commutatorElement_inv] at h2
    grw [← h2]
    exact (Eq.symm h1)
  · intro t u
    rcases h (-u) t with ⟨h1, ⟨h2, h3⟩⟩
    norm_num at h1
    apply mul_eq_one_iff_eq_inv.mp at h2
    simp only [neg_neg, commutatorElement_inv] at h2
    grw [← h2, h3]
    rcases h (-2*u) t with ⟨_, ⟨h4, _⟩⟩
    apply mul_eq_one_iff_eq_inv.mp at h4
    simp only [neg_neg, commutatorElement_inv] at h4
    norm_num at h4
    rw [h4]
    have h5 := @hom_lift_of_interchange_of_α2β2ψ_b F _ Fchar 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h5
    have h5a := h5 t 1 u; norm_num at h5a
    have h5b := h5 (t) (1/2) (2*u); field_simp at h5b;
    rw [←h5a, ←h5b]
omit Fchar

-- 8.166
theorem sufficient_conditions_for_commutator_of_αβ_and_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 2) (hj : j ≤ 1) (hk : k ≤ 2)
  (h42a : ∀ (t u : F), ⁅{αβ2ψ, i + 2 * j, t}, {βψ, k, u}⁆ = 1)
  (h42b : ∀ (t u v : F), ⁅{ψ, j, t}, ⁅{αβψ, i + j, u}, {βψ, k, v}⁆⁆ = 1),
  ∀ (t u v : F), ⁅{αβ, i, t}, {β2ψ, j + k, 2 * u * v}⁆ = ⁅{αβψ, i + j, t * u}, {βψ, k, v}⁆ := by
  sorry

-- 8.167
theorem sufficient_conditions_for_commutator_of_αβ2ψ_and_βψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 4) (hj : j ≤ 1) (hk : k ≤ 1)
  (h44a : ∀ (t u v : F), ⁅⁅{αβ2ψ, i, t}, {β, j, u}⁆, {ψ, k, v}⁆ = 1)
  (h44b : ∀ (t u : F), ⁅{β, j, -u}, {αβ2ψ, i, t}⁆ = ⁅{αβ2ψ, i, t}, {β, j, u}⁆)
  (h44c : ∀ (t u : F), ⁅{αβ2ψ, i, t}, {β, j, u}⁆ * ⁅{αβ2ψ, i, -t}, {β, j, u}⁆ = 1),
  ∀ (t u : F), ⁅{αβ2ψ, i, t}, {βψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.168
theorem partial_comm_of_βψ_αβ2ψ :
  ∀ (t u : F), ⁅{αβ2ψ, 2, t}, {βψ, 0, u}⁆ = 1 := by
  sorry

-- 8.169a
theorem partial_C_interchange_of_α2β2ψ_a :
  ∀ (t u v : F), ⁅{αβ, 0, t}, {β2ψ, 1, u * v}⁆ = ⁅{αβψ, 1, t * u}, {βψ, 0, 2 * v}⁆ := by
  sorry

-- 8.169b
theorem partial_C_interchange_of_α2β2ψ_b :
  ∀ (t u v : F), ⁅{αβ, 2, t}, {β2ψ, 0, u * v}⁆ = ⁅{αβψ, 2, t * v}, {βψ, 0, 2 * v}⁆ := by
  sorry

-- 8.170
theorem sufficient_conditions_for_commutator_of_αβ2ψ_and_β :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 3) (hj : j ≤ 1) (hk : k ≤ 1)
  (h47a : ∀ (t u : F), ⁅{αβψ, i, t}, {β2ψ, 2 * j + k, u}⁆ = 1)
  (h47b : ∀ (t u v : F), ⁅⁅{αβψ, i, t}, {βψ, j + k, u}⁆, {ψ, j, v}⁆ = 1)
  (h47c : ∀ (t u : F), ⁅{βψ, j + k, -u}, {αβψ, i, t}⁆ = ⁅{αβψ, i, t}, {βψ, j + k, u}⁆),
  ∀ (t u v : F), ⁅{αβ2ψ, i + j, 2 * t * u}, {β, k, v}⁆ = ⁅{αβψ, i, t}, {βψ, j + k, u * v}⁆ := by
  sorry

-- 8.171
theorem sufficient_conditions_for_commutator_of_αβψ_and_β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
  (hyp : ∀ (t u : F), ⁅{αβ2ψ, i + k, u}, {βψ, j, t}⁆ = 1),
  ∀ (t u : F), ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1 := by
  sorry

-- 8.172
theorem partial_comm_of_αβψ_β2ψ :
  ∀ (t u : F), ⁅{αβψ, 0, t}, {β2ψ, 1, u}⁆ = 1 := by
  sorry

-- 8.173
theorem partial_D_interchange_of_α2β2ψ :
  ∀ (t u v : F), ⁅{αβψ, 0, t}, {βψ, 1, u * v}⁆ = ⁅{αβ2ψ, 0, t * u}, {β, 1, 2 * u}⁆ := by
  sorry

-- 8.175 (8.174 is establishing α2β2ψ)
theorem trivial_comm_of_β_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk β α2β2ψ := by
  sorry

-- 8.176
theorem trivial_comm_of_αβ_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ α2β2ψ := by
  sorry

-- 8.177
theorem trivial_comm_of_βψ_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk βψ α2β2ψ := by
  sorry

-- 8.178a
theorem inv_doub_of_α2β2ψ_a :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ α2β2ψ.height) (t : F),
  {α2β2ψ, i, t} * {α2β2ψ, i, -t} = 1 := by
  sorry

-- 8.178b
theorem inv_doub_of_α2β2ψ_b :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ α2β2ψ.height) (t : F),
  {α2β2ψ, i, t} * {α2β2ψ, i, t} = {α2β2ψ, i, 2 * t} := by
  sorry

-- 8.179a
theorem expand_α2β2ψ_as_αβ_β2ψ_αβ_β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : F),
  {α2β2ψ, i + j, -t * u} = {αβ, i, t} * {β2ψ, j, u} * {αβ, i, -t} * {β2ψ, j, -u} := by
  sorry

-- 8.179b
theorem expand_α2β2ψ_as_β2ψ_αβ_β2ψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : F),
  {α2β2ψ, i + j, -t * u} = {β2ψ, j, -u} * {αβ, i, t} * {β2ψ, j, u} * {αβ, i, -t} := by
  sorry

-- 8.180a
theorem expr_αβ_β2ψ_as_β2ψ_α2β2ψ_αβ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : F),
  {αβ, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {α2β2ψ, i + j, -t * u} * {αβ, i, t} := by
  sorry

-- 8.180b
theorem expr_αβ_β2ψ_as_β2ψ_αβ_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ β2ψ.height) (t u : F),
  {αβ, i, t} * {β2ψ, j, u} = {β2ψ, j, u} * {αβ, i, t} * {α2β2ψ, i + j, -t * u} := by
  sorry

-- 8.181a
theorem expr_β_αβ2ψ_as_αβ2ψ_α2β2ψ_β :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβ2ψ.height) (t u : F),
  {β, i, t} * {αβ2ψ, j, u} = {αβ2ψ, j, u} * {α2β2ψ, i + j, t * u} * {β, i, t} := by
  sorry

-- 8.181b
theorem expr_β_αβ2ψ_as_αβ2ψ_β_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ αβ2ψ.height) (t u : F),
  {β, i, t} * {αβ2ψ, j, u} = {αβ2ψ, j, u} * {β, i, t} * {α2β2ψ, i + j, t * u} := by
  sorry

-- 8.182a
theorem expr_βψ_αβψ_as_αβψ_α2β2ψ_βψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ βψ.height) (hj : j ≤ αβψ.height) (t u : F),
  {βψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {α2β2ψ, i + j, 2 * t * u} * {βψ, i, t} := by
  sorry

-- 8.182b
theorem expr_βψ_αβψ_as_αβψ_βψ_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ βψ.height) (hj : j ≤ αβψ.height) (t u : F),
  {βψ, i, t} * {αβψ, j, u} = {αβψ, j, u} * {βψ, i, t} * {α2β2ψ, i + j, 2 * t * u} := by
  sorry

-- 8.183a
theorem commutator_of_α_βψ_a :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βψ.height) (t u : F),
  ⁅{α, i, t}, {βψ, j, u}⁆ = {αβψ, i + j, t * u} * {α2β2ψ, i + 2 * j, t * u^2} := by
  sorry

-- 8.183b
theorem commutator_of_α_βψ_b :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βψ.height) (t u : F),
  ⁅{α, i, t}, {βψ, j, u}⁆ = {α2β2ψ, i + 2 * j, t * u^2} * {αβψ, i + j, t * u} := by
  sorry

-- 8.184
theorem sufficient_conditions_for_commutator_of_ψ_and_α2β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
  (h50a : ∀ (t u : F), ⁅{αβψ, i + j, t}, {β2ψ, k, u}⁆ = 1)
  (h50b : ∀ (t u : F), ⁅{αβ2ψ, 2 * i + j, t}, {β2ψ, k, u}⁆ = 1),
  ∀ (t u : F), ⁅{ψ, i, t}, {α2β2ψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.185
theorem partial_comm_of_ψ_α2β2ψ :
  ∀ (t u : F), ⁅{ψ, 1, t}, {α2β2ψ, 0, u}⁆ = 1 := by
  sorry

-- 8.186
theorem trivial_comm_of_ψ_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk ψ α2β2ψ := by
  sorry

-- 8.187
theorem trivial_comm_of_β2ψ_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk β2ψ α2β2ψ := by
  sorry

-- 8.188
theorem trivial_comm_of_αβψ_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβψ α2β2ψ := by
  sorry

-- 8.189
theorem trivial_comm_of_αβ2ψ_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ2ψ α2β2ψ := by
  sorry

-- 8.190
theorem mixed_comm_of_α2β2ψ :
  mixed_commutes_of_root (weakB3Large F).pres_mk α2β2ψ := by
  sorry

-- 8.191
theorem trivial_comm_of_αβψ_β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβψ β2ψ := by
  sorry

-- 8.192
theorem trivial_comm_of_βψ_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk βψ αβ2ψ := by
  sorry

-- 8.193
theorem trivial_comm_of_β2ψ_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk β2ψ αβ2ψ := by
  sorry

-- 8.194
theorem trivial_comm_of_αβψ_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβψ αβ2ψ := by
  sorry

-- 8.195
theorem mixed_comm_of_αβ2ψ :
  mixed_commutes_of_root (weakB3Large F).pres_mk αβ2ψ := by
  sorry

-- 8.196
theorem lin_of_αβ2ψ :
  lin_of_root((weakB3Large F).pres_mk, αβ2ψ) := by
  sorry

-- 8.197
theorem lin_of_α2β2ψ :
  lin_of_root((weakB3Large F).pres_mk, α2β2ψ) := by
  sorry

-- 8.198
theorem hom_lift_of_comm_of_α_α2β2ψ_square :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t r : F),
  ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 2 * k, t * r^2}⁆ = 1 := by
  sorry

-- 8.200 (8.199 is about sum of squares in finite field)
theorem hom_lift_of_comm_of_α_α2β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ ψ.height) (t u : F),
  ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 2 * k, u}⁆ = 1 := by
  sorry

-- 8.201
theorem nonhomog_lift_of_comm_of_α_α2β2ψ :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (t u : F),
  ⁅{α, i, t}, {α2β2ψ, i + 2 * j + 1, u}⁆ = 1 := by
  sorry

-- 8.202
theorem sufficient_conditions_for_commutator_of_αβ_and_αβ2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 4)
  (hyp : ∀ (t u : F), ⁅{α, i, t}, {α2β2ψ, j + k, u}⁆ = 1),
  ∀ (t u : F), ⁅{αβ, i + j, t}, {αβ2ψ, k, u}⁆ = 1 := by
  sorry

-- 8.203
theorem partial_comm_of_αβ_α2β2ψ :
  ∀ (t u : F), ⁅{αβ, 0, t}, {αβ2ψ, 1, u}⁆ = 1 := by
  sorry

-- 8.204
theorem sufficient_conditions_for_commutator_of_α_and_α2β2ψ :
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ 1) (hj : j ≤ 2) (hk : k ≤ 3)
  (hyp : ∀ (t u : F), ⁅{αβ, j, t}, {αβ2ψ, i + k, u}⁆ = 1),
  ∀ (t u : F), ⁅{α, i, t}, {α2β2ψ, j + k, u}⁆ = 1 := by
  sorry

-- 8.205
theorem partial_comm_of_α_α2β2ψ :
  ∀ (t u : F), ⁅{α, 1, t}, {α2β2ψ, 0, u}⁆ = 1 := by
  sorry

-- 8.206
theorem trivial_comm_of_α_α2β2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk α α2β2ψ := by
  sorry

-- 8.207
theorem trivial_comm_of_αβ_αβ2ψ :
  trivial_commutator_of_root_pair (weakB3Large F).pres_mk αβ αβ2ψ := by
  sorry

-- 8.208
theorem mixed_comm_of_αβψ :
  mixed_commutes_of_root (weakB3Large F).pres_mk αβψ := by
  sorry

-- 8.209
theorem lin_of_αβψ :
  lin_of_root((weakB3Large F).pres_mk, αβψ) := by
  sorry

end B3LargeProof
