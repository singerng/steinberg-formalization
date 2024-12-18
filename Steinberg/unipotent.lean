import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Algebra.Defs
-- import Steinberg.Macro.Algebra

-- tactic, under development, to simplify algebra expressions
macro (name := algebra) "algebra" : tactic => `(tactic|
  simp only [
    -- additive ring structure
    mul_add, add_mul, neg_add, sub_eq_add_neg, add_zero, zero_add,
    -- multiplicative ring structure
    one_mul, mul_one, mul_zero, zero_mul, mul_neg,
    -- scalar structure
    smul_smul,              -- t • (u • x) = (t * u) • x
    mul_smul_comm,          -- x * (t • y) = t • (x * y)
    smul_mul_assoc,         -- (t • x) * y = t • (x * y)
    ← neg_one_smul,         -- -x = (-1) • x
    ← neg_smul,             -- -(r • x) = (-r) • x
    smul_add,               -- t • (x + y) = t • x + t • y
    smul_zero
  ]
)

universe u v

variable {n : Type v} [DecidableEq n]
variable {R : Type u} [CommRing R]

/-- entries of indicator matrix -/
def f (i j : n) (t : R) (a b : n) : R :=
  if a = i ∧ b = j then t else 0

/-- indicator matrix -/
def E (i j : n) (t : R) : Matrix n n R :=
  Matrix.of (f i j t)

/-- M = 1 + E -/
def M (i j : n) (t : R) : Matrix n n R :=
  1 + (E i j t)

/- Some useful theorems for sums, here for reference -/
#check Fintype.sum_eq_zero
#check Fintype.sum_eq_single
#check Fintype.sum_eq_add
#check Matrix.one_apply_ne

/-- Product of indicator matrices, j = k case -/
theorem E_mul [Fintype n] {i j k : n}
  : (E i j (1 : R)) * (E j k 1) = E i k 1 := by
  ext a b
  simp only [E, Matrix.mul_apply, Matrix.of_apply]
  rw [f]
  split_ifs with aibk
  · have aux : ∀ x, x ≠ j → (f i j 1 a x) * (f j k 1 x b) = (0 : R) :=
      fun x hxj ↦ by rw [f, f, if_neg (fun h ↦ hxj h.2), zero_mul]
    rw [Fintype.sum_eq_single j aux, f, f, if_pos ⟨aibk.1, rfl⟩,
        if_pos ⟨rfl, aibk.2⟩, one_mul]
  · have aux : ∀ x, f i j 1 a x * f j k 1 x b = (0 : R) := by
      intro x
      rw [f, f]
      split_ifs with aixj xjbk
      · exact False.elim (aibk ⟨aixj.1, xjbk.2⟩)
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    exact Fintype.sum_eq_zero _ aux

/-- Product of indicator matrices, j ≠ k case -/
theorem E_mul_eq_zero [Fintype n] {i j k l : n} (hjk : j ≠ k)
  : (E i j (1 : R)) * (E k l 1) = 0 := by
  ext a b
  simp only [E, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  have aux : ∀ x, (f i j (1 : R) a x) * (f k l 1 x b) = 0 := by
    intro x
    rw [f, f]
    split_ifs with aixj xkbl
    · exact False.elim (hjk (Eq.trans aixj.2.symm xkbl.1))
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]
  exact Fintype.sum_eq_zero _ aux

theorem E_smul {i j : n} {t : R}
  : t • (E i j (1 : R)) = E i j t := by
  ext a b
  simp only [E, Matrix.of_apply, Matrix.smul_apply, f]
  rw [smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero]

/-- Relation A.3, identity -/
theorem M_zero_eq_one [Fintype n] {i j : n}
  : M i j (0 : R) = 1 := by
  ext a b
  rw [M, E, Matrix.add_apply, Matrix.of_apply, f, ite_self, add_zero]

/-- Relation A.4, linearity -/
theorem M_mul_add [Fintype n] {i j : n} {t u : R} (hij : i ≠ j)
  : (M i j t) * (M i j u) = M i j (t + u) := by
  ext a b
  simp only [M, E, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
  rw [f]
  split_ifs with aibj
  · have hab : a ≠ b := fun ab ↦ by rw [aibj.1, aibj.2] at ab; exact hij ab
    have aux : ∀ x, x ≠ a ∧ x ≠ b →
      ((1 : Matrix n n R) a x + f i j t a x) *
      ((1 : Matrix n n R) x b + f i j u x b) = 0 :=
      fun x ⟨hxa, hxb⟩ ↦ by rw [f, f, Matrix.one_apply_ne hxa.symm, zero_add,
          if_neg (fun h ↦ by rw [h.2] at hxb; exact hxb (aibj.2.symm)), zero_mul]
    rw [Matrix.one_apply_ne hab, zero_add, Fintype.sum_eq_add a b hab aux]
    simp only [Matrix.one_apply, f, if_pos, if_neg hab, zero_add, if_pos aibj]
    repeat rw [if_neg (fun ⟨ai, aj⟩ ↦ hij (Eq.trans ai.symm aj))]
    rw [add_zero, one_mul, mul_one, add_comm]
  cases eq_or_ne a b with
  | inl hab =>
    have aux : ∀ x, x ≠ b →
      ((1 : Matrix n n R) b x + f i j t b x) *
      ((1 : Matrix n n R) x b + f i j u x b) = 0 := by
      intro x hxb
      rw [f, f, Matrix.one_apply_ne hxb, zero_add, Matrix.one_apply_ne hxb.symm, zero_add]
      split_ifs with bixj xibj
      · exact False.elim (hxb (Eq.trans xibj.1 bixj.1.symm))
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    rw [hab, Matrix.one_apply, if_pos rfl, add_zero, Fintype.sum_eq_single b aux,
        Matrix.one_apply, if_pos rfl, f, f]
    repeat rw [if_neg (fun ⟨bi, bj⟩ ↦ hij (Eq.trans bi.symm bj))]
    simp only [add_zero, mul_one]
  | inr hab =>
    rw [add_zero, Matrix.one_apply_ne hab]
    have aux : ∀ x,
      ((1 : Matrix n n R) a x + f i j t a x) *
      ((1 : Matrix n n R) x b + f i j u x b) = 0 := by
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

-- instance hasMul [Fintype n] : Mul (@TypeAMatrices n _ R _) :=
--   ⟨fun A B => ⟨A * B, by
--     rcases A with ⟨A, ⟨i, j, t, hA⟩⟩
--     rcases B with ⟨B, ⟨k, l, u, hB⟩⟩
--     cases eq_or_ne j k with
--     | inl hjk => sorry
--     | inr hjk => sorry
--   ⟩⟩

/-- Relation A.5, inverses -/
theorem M_inv_neg [Fintype n] {i j : n} {t : R} (hij : i ≠ j)
  : (M i j t) * (M i j (-t)) = 1 := by
  rw [M_mul_add hij, add_neg_cancel, M_zero_eq_one]

/-- Defs only used in the proof of Relation A.6 -/
private def X [Fintype n] (i j k l : n) (t u : R) : Matrix n n R :=
  t • (E i j 1) + u • (E k l 1)

private def Y [Fintype n] (i j k l : n) (t u : R) : Matrix n n R :=
  (t * u) • (E i j 1) * (E k l 1)

/-- Own definition of commutator -/
def M_comm [Fintype n] (i j k l : n) (t u : R) : Matrix n n R :=
  (M i j t) * (M k l u) * (M i j (-t)) * (M k l (-u))

lemma expand_signed_prod [Fintype n] (_X _Y : Matrix n n R) : (1 + _X + _Y) * (1 - _X + _Y) = 1 + (2 : R) • _Y + (_X + _Y) * (-_X + _Y) := by
  algebra
  module

/-- [Mij(t), Mkl(u)] = 1 + 2Y + (X + Y)(-X + Y) -/
lemma M_commutator_calc [Fintype n] {i j k l : n} {t u : R} --(hij : i ≠ j) (hkl : k ≠ l)
  : M_comm i j k l t u =
  1 + (2 : R) • (Y i j k l t u) + ((X i j k l t u) + (Y i j k l t u)) * (-(X i j k l t u) + (Y i j k l t u)) := by
  have h₀ : (M i j t) * (M k l u) = 1 + (X i j k l t u) + (Y i j k l t u) := by
    rw [M, M, ←E_smul, ←@E_smul _ _ _ _ k, X, Y]
    algebra
    module
  have h₁ : (M i j (-t)) * (M k l (-u)) = 1 - (X i j k l t u) + (Y i j k l t u) := by
    rw [M, M, ←E_smul, ←@E_smul _ _ _ _ k, X, Y]
    algebra
    simp only [neg_mul_neg]
    module
  rw [M_comm, h₀, mul_assoc, h₁, expand_signed_prod]

theorem M_commutator [Fintype n] {i j k l : n} {t u : R} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
  : M_comm i j k l t u = 1 := by
  have Y0 : Y i j k l t u = 0 := by
    rw [Y, Matrix.smul_mul, E_mul_eq_zero hjk, smul_zero]
  have X0 : (X i j k l t u) * (X i j k l t u) = 0 := by
    rw [X]
    algebra
    rw [E_mul_eq_zero hij.symm, E_mul_eq_zero hjk, E_mul_eq_zero hil.symm, E_mul_eq_zero hkl.symm]
    simp only [smul_zero, add_zero]
  rw [M_commutator_calc, Y0]
  algebra
  simp only [add_right_eq_self, neg_eq_zero]
  exact X0

theorem M_commutator' [Fintype n] {i j k : n} {t u : R} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
  : M_comm i j j k t u  = M i k (t * u) := by
  have hY : Y i j j k t u = (t * u) • (E i k 1) := by
    rw [Y, Matrix.smul_mul, E_mul]
  have : ((X i j j k t u) + (Y i j j k t u)) * (-(X i j j k t u) + (Y i j j k t u)) = -(t * u) • E i k 1 := by
    rw [X, Y]
    algebra
    simp only [E_mul, E_mul_eq_zero hik.symm, E_mul_eq_zero hjk.symm, E_mul_eq_zero hij.symm]
    module
  rw [M_commutator_calc, this, M, Y, Matrix.smul_mul, E_mul]
  algebra
  nth_rewrite 3 [← E_smul]
  module
