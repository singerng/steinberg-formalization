import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

variable {R : Type*} [Ring R]
variable {n : ℕ}

def f (i j : Fin n) (t : R) (a b : Fin n) : R :=
  if a = i ∧ b = j then t else 0

/-- indicator matrix -/
def E (i j : Fin n) (t : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of (f i j t)

def M (i j : Fin n) (t : R) : Matrix (Fin n) (Fin n) R :=
  1 + (E i j t)

#check Fintype.sum_eq_zero
#check Matrix.one_apply_ne
#check Fintype.sum_eq_add
#check Fintype.sum_eq_single

theorem mul_add_unipotent {i j : Fin n} {t u : R} (hij : i < j)
  : (M i j t) * (M i j u) = M i j (t + u) := by
  ext a b
  simp only [M, E, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
  rw [f]
  split_ifs with aibj
  · have hab : a ≠ b := fun ab ↦ by rw [aibj.1, aibj.2] at ab; exact ne_of_lt hij ab
    have aux : ∀ x, x ≠ a ∧ x ≠ b →
      ((1 : Matrix (Fin n) (Fin n) R) a x + f i j t a x) *
      ((1 : Matrix (Fin n) (Fin n) R) x b + f i j u x b) = 0 :=
      fun x ⟨hxa, hxb⟩ ↦ by rw [f, f, Matrix.one_apply_ne hxa.symm, zero_add,
          if_neg (fun h ↦ by rw [h.2] at hxb; exact hxb (aibj.2.symm)), zero_mul]
    rw [Matrix.one_apply_ne hab, zero_add, Fintype.sum_eq_add a b hab aux]
    simp only [Matrix.one_apply, f, if_pos, if_neg hab, zero_add, if_pos aibj]
    repeat rw [if_neg (fun h ↦ by rw [←h.1, h.2] at hij; exact (lt_self_iff_false j).1 hij)]
    rw [add_zero, one_mul, mul_one, add_comm]
  cases eq_or_ne a b with
  | inl hab =>
    have aux : ∀ x, x ≠ b →
      ((1 : Matrix (Fin n) (Fin n) R) b x + f i j t b x) *
      ((1 : Matrix (Fin n) (Fin n) R) x b + f i j u x b) = 0 := by
      intro x hxb
      rw [f, f, Matrix.one_apply_ne hxb, zero_add, Matrix.one_apply_ne hxb.symm, zero_add]
      split_ifs with bixj xibj
      · exact False.elim (hxb (Eq.trans xibj.1 bixj.1.symm))
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    rw [hab, Matrix.one_apply, if_pos rfl, add_zero, Fintype.sum_eq_single b aux,
        Matrix.one_apply, if_pos rfl, f, f]
    repeat rw [if_neg (fun h ↦ ne_of_lt hij (Eq.trans h.1.symm h.2))]
    simp only [add_zero, mul_one]
  | inr hab =>
    rw [add_zero, Matrix.one_apply_ne hab]
    have aux : ∀ x,
      ((1 : Matrix (Fin n) (Fin n) R) a x + f i j t a x) *
      ((1 : Matrix (Fin n) (Fin n) R) x b + f i j u x b) = 0 := by
      intro x
      rw [f, f]
      split_ifs with aixj xibj xibj
      · exact False.elim (aibj ⟨aixj.1, xibj.2⟩)
      · rw [Matrix.one_apply_ne (fun h ↦ aibj ⟨aixj.1, Eq.trans h.symm aixj.2⟩),
            zero_add, mul_zero]
      · rw [Matrix.one_apply_ne (fun h ↦ aibj ⟨Eq.trans h xibj.1, xibj.2⟩),
            zero_add, zero_mul]
      · rw [Matrix.one_apply, Matrix.one_apply]
        split_ifs with hax hxb
        · exact False.elim (hab (Eq.trans hax hxb))
        · simp only [add_zero, mul_zero]
        · simp only [add_zero, mul_one]
        · simp only [add_zero, mul_zero]
    exact Fintype.sum_eq_zero _ aux
