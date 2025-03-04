import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Sigma

import Mathlib.Tactic.Use

namespace Steinberg

-- NS: For now, we encode an input "i ≤ n" as a pair (i : ℕ) (hi : i ≤ n).

/--
  Decompose a number `0 ≤ i ≤ n + m` into `i₁ + i₂`, where `0 ≤ i₁ ≤ n` and `0 ≤ i₂ ≤ m`.
 -/
theorem decompose (n m i : ℕ) (h : i ≤ (n+m)) : ∃ (i₁ i₂ : ℕ), i = i₁ + i₂ ∧ i₁ ≤ n ∧ i₂ ≤ m := by
  by_cases i ≤ n
  · use i, 0
    omega
  · use n, i-n
    omega

theorem decompose' (i : ℕ) (hi : i ≤ 3) : ∃ (i₁ i₂ : ℕ), i = i₁ + 2 * i₂ ∧ i₁ ≤ 1 ∧ i₂ ≤ 1 := by
  match i with
  | 0 => exact ⟨0, 0, by omega⟩
  | 1 => exact ⟨1, 0, by omega⟩
  | 2 => exact ⟨0, 1, by omega⟩
  | 3 => exact ⟨1, 1, by omega⟩

theorem decompose'' (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 3) : ∃ (i j k : ℕ), a = i + j ∧ b = j + 2 * k ∧ i ≤ 1 ∧ j ≤ 1 ∧ k ≤ 1 := by
  match a, b with
  | 0, 0 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 0, 1 => exact ⟨0, 1, 0, by omega, by omega, by omega⟩
  | 0, 2 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 0, 3 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 1, 0 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 1, 1 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 1, 2 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 1, 3 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 2, 0 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 2, 1 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 2, 2 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩
  | 2, 3 => exact ⟨0, 0, 0, by omega, by omega, by omega⟩

theorem decompose_4_into_3_1 (i : ℕ) (hi : i ≤ 4) : ∃ (i₁ i₂ : ℕ), i = i₁ + i₂ ∧ i₁ ≤ 3 ∧ i₂ ≤ 1 := by
  match i with
  | 0 => exact ⟨0, 0, by omega⟩
  | 1 => exact ⟨0, 1, by omega⟩
  | 2 => exact ⟨2, 0, by omega⟩
  | 3 => exact ⟨3, 0, by omega⟩
  | 4 => exact ⟨3, 1, by omega⟩


/--
  Useful theorem to convert `i ≤ n` to `i ∈ List.range (n+1)`.
-/
theorem mem_list_range_iff_le {i n : ℕ} : i ≤ n ↔ i ∈ List.range (n+1) := by
  constructor
  · intro h
    rw [List.mem_range]
    exact Nat.lt_add_one_of_le h
  · intro h
    apply Nat.le_of_lt_add_one
    exact List.mem_range.mp h

theorem mem_finset_range_iff_le {i n : ℕ} : i ≤ n ↔ i ∈ Finset.range (n+1) := by
  constructor
  · intro h
    rw [Finset.mem_range]
    exact Nat.lt_add_one_of_le h
  · intro h
    apply Nat.le_of_lt_add_one
    exact Finset.mem_range.mp h

/- Every (i, j) ∈ (Deg 2 × Deg 2) can be written as (i' + j', j' + k') for i', j', k' ∈ Deg 1, except (0, 2) and (2, 0) -/
def booleans : Finset ℕ := {0, 1}
def boolean_cube : Finset (ℕ × ℕ × ℕ) := booleans ×ˢ booleans ×ˢ booleans

def f_ij_jk : ℕ × ℕ × ℕ → ℕ × ℕ := (fun ijk' : ℕ × ℕ × ℕ => let ( i', j', k' ) := ijk'; (i' + j', j' + k'))
def ij_jk_image : Finset (ℕ × ℕ) := {(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)}

theorem correct_of_ij_jk_image : (Finset.image f_ij_jk boolean_cube) = ij_jk_image := by decide

theorem mem_range_of_boolean_cube (ijk : ℕ × ℕ × ℕ) (hijk_set : ijk ∈ boolean_cube) :
  let ⟨ i, j, k ⟩ := ijk; i ≤ 1 ∧ j ≤ 1 ∧ k ≤ 1 := by
  simp only [boolean_cube] at hijk_set
  constructor
  · have : ijk.1 ∈ booleans := And.left (Finset.mem_product.mp hijk_set)
    exact mem_finset_range_iff_le.mpr this
  · constructor
    · have : ijk.2.1 ∈ booleans := And.left (Finset.mem_product.mp (And.right (Finset.mem_product.mp hijk_set)))
      exact mem_finset_range_iff_le.mpr this
    · have : ijk.2.2 ∈ booleans := And.right (Finset.mem_product.mp (And.right (Finset.mem_product.mp hijk_set)))
      exact mem_finset_range_iff_le.mpr this

end Steinberg
