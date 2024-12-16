import Mathlib.Data.Matrix.Basic
--import Mathlib.Tactic

open Matrix

variable {R : Type*} [Ring R]
variable {n : ℕ}

def f (i j : Fin n) (t : R) (a b : Fin n) : R :=
  if a = b then 1
  else if a = i ∧ b = j then t
  else 0

def E (i j : Fin n) (t : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of (f i j t)

#check Fintype.sum_eq_zero

-- TODO : get rid of the aesops
theorem mul_add_unipotent {i j : Fin n} {t u : R} (hij : i < j)
  : (E i j t) * (E i j u) = E i j (t + u) := by
  ext a b
  simp only [E, Matrix.mul_apply, Matrix.of_apply]
  rw [f]
  split_ifs with ab aibj
  · rw [ab]
    have aux : ∀ x : Fin n, x ≠ b → (f i j t b x) * (f i j u x b) = 0 := by
      intro x hxb
      rw [f, f, if_neg hxb, if_neg hxb.symm]
      aesop
    rw [Fintype.sum_eq_single b aux, f, f]
    simp only [↓reduceIte, mul_one]
  · have aux : ∀ x : Fin n, x ≠ a ∧ x ≠ b → (f i j t a x) * (f i j u x b) = 0 := by
      intro x ⟨hxa, hxb⟩
      rw [f, f]
      aesop
    rw [Fintype.sum_eq_add a b ab aux, f, f, f, f,
        if_pos rfl, if_neg ab, if_pos aibj, if_neg ab, if_pos aibj, if_pos rfl,
        one_mul, mul_one, add_comm]
  · have aux : ∀ x : Fin n, (f i j t a x) * (f i j u x b) = 0 := by
      intro x
      rw [f, f]
      aesop
    exact Fintype.sum_eq_zero _ aux
