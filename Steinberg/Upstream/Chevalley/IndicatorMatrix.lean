import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import Steinberg.Upstream.Chevalley.Macro.Algebra

universe u v

variable {R : Type u} [CommRing R]
variable {I : Type v} [DecidableEq I] [Fintype I]

/- Some useful theorems for sums, here for reference -/
#check Fintype.sum_eq_zero
#check Fintype.sum_eq_single
#check Fintype.sum_eq_add
#check Matrix.one_apply_ne

/-- entries of indicator matrix -/
private def f (i j a b : I) : R :=
  if a = i ∧ b = j then (1 : R) else (0 : R)

/-- matrix with a `1` in the `(i,j)` coordinate and `0`'s everywhere else -/
def E (i j : I) : Matrix I I R :=
  Matrix.of (f i j)

/-- Product of indicator matrices, j = k case -/
theorem E_mul {i j k : I}
  : (E i j) * (E j k) = (@E R _ _ _ i k) := by
  ext a b
  simp only [E, Matrix.mul_apply, Matrix.of_apply]
  rw [f]
  split_ifs with aibk
  · have aux : ∀ x, x ≠ j → (f i j a x) * (f j k x b) = (0 : R) :=
      fun x hxj ↦ by rw [f, f, if_neg (fun h ↦ hxj h.2), zero_mul]
    rw [Fintype.sum_eq_single j aux, f, f, if_pos ⟨aibk.1, rfl⟩,
        if_pos ⟨rfl, aibk.2⟩, one_mul]
  · have aux : ∀ x, f i j a x * f j k x b = (0 : R) := by
      intro x
      rw [f, f]
      split_ifs with aixj xjbk
      · exact False.elim (aibk ⟨aixj.1, xjbk.2⟩)
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    exact Fintype.sum_eq_zero _ aux

/-- Product of indicator matrices, j ≠ k case -/
theorem E_mul_eq_zero {i j k l : I} (hjk : j ≠ k)
  : (@E R _ _ _ i j) * (E k l) = 0 := by
  ext a b
  simp only [E, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  have aux : ∀ x, (f i j a x) * (f k l x b) = (0 : R) := by
    intro x
    rw [f, f]
    split_ifs with aixj xkbl
    · exact False.elim (hjk (Eq.trans aixj.2.symm xkbl.1))
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]
  exact Fintype.sum_eq_zero _ aux
