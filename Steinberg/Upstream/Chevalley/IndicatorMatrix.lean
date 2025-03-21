/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic


/-!
  An implementation of "indicator matrices". These are square matrices whose rows and columns are indexed by
  some type `I` which is an instance of `Fintype` and `DecidableEq`, and they have a single `1` entry and `0`'s
  in all other entries. `E i j` constructs the matrix with a `1` in the `(i,j)` entry. Then, we prove the two
  multiplication identities `(E i j) * (E j k) = E i k` and `(E i j) * (E k l) = 0` for `j ≠ k` in `E_mul` and
  `E_mul_eq_zero`, respectively.
-/

universe u v


variable {R : Type u} [CommRing R]
variable {I : Type v} [DecidableEq I] [Fintype I]

/- Some useful theorems for sums, here for reference -/
#check Fintype.sum_eq_zero
#check Fintype.sum_eq_single
#check Fintype.sum_eq_add
#check Matrix.one_apply_ne

#check Matrix.col

/-- indicator vector -/
private def f (i a : I) : R :=
  if i = a then (1 : R) else (0 : R)

-- /-- entries of indicator matrix -/
-- private def f (i j a b : I) : R :=
--   if a = i ∧ b = j then (1 : R) else (0 : R)

example (i j : I) : ¬(i=j) ↔ ¬(j=i) := by aesop?

private theorem product_of_indicators (i j : I) :
  (Matrix.row Unit (f i)) * (Matrix.col Unit (f j)) = (if i = j then (1 : Matrix Unit Unit R) else (0 : Matrix Unit Unit R)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.row_apply, Matrix.col_apply, f]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  split
  · simp only [Matrix.one_apply_eq]
  · simp only [Matrix.zero_apply]

-- example (a : Matrix I I R) (b : Matrix I (Fin 1) R) (c : Matrix (Fin 1) I R) : (a * b) * c = a * (b * c) := by
--   ex

/-- matrix with a `1` in the `(i,j)` coordinate and `0`'s everywhere else -/
def E (i j : I) : Matrix I I R :=
  (Matrix.col Unit (f i)) * (Matrix.row Unit (f j))

/-- Product of indicator matrices, j = k case -/
theorem E_mul_overlap {i j k : I}
  : (@E R _ _ _ i j) * (E j k) = E i k := by
  simp only [E]
  rw [←Matrix.mul_assoc]
  nth_rewrite 2 [Matrix.mul_assoc]
  simp only [product_of_indicators, ↓reduceIte, Matrix.mul_one, Matrix.one_mul]

/-- Product of indicator matrices, j ≠ k case -/
theorem E_mul_disjoint {i j k l : I} (hjk : j ≠ k)
  : (@E R _ _ _ i j) * (E k l) = 0 := by
  simp only [E]
  rw [←Matrix.mul_assoc]
  nth_rewrite 2 [Matrix.mul_assoc]
  simp_all only [product_of_indicators, ne_eq, ↓reduceIte, Matrix.mul_zero, Matrix.zero_mul]
