import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

-- import Steinberg.Upstream.Chevalley.fins
import Steinberg.Upstream.Chevalley.Macro.Algebra
import Steinberg.Upstream.Chevalley.IndicatorMatrix

universe u v

variable {R : Type u} [CommRing R]
variable {I : Type v} [DecidableEq I] [Fintype I]

/-- M = 1 + E -/
def M (i j : I) (t : R) : Matrix I I R :=
  1 + t • (E i j)

/-- Relation A.3, identity -/
theorem M_zero_eq_one {i j : I}
  : M i j (0 : R) = 1 := by
  rw [M]
  simp only [zero_smul, add_zero]

/- TODO: `algebra` macro should be able to eliminate the like terms -/

/-- Relation A.4, linearity -/
theorem M_mul_add {i j : I} {t u : R} (hij : i ≠ j)
  : (M i j t) * (M i j u) = M i j (t + u) := by
  repeat rw [M]
  algebra
  simp only [E_mul_eq_zero (Ne.symm hij)]
  module

/-- Relation A.5, inverses -/
theorem M_inv_neg {i j : I} {t : R} (hij : i ≠ j)
  : (M i j t) * (M i j (-t)) = 1 := by
  rw [M_mul_add hij, add_neg_cancel, M_zero_eq_one]

/-- Defs only used in the proof of Relation A.6 -/
private def X (i j k l : I) (t u : R) : Matrix I I R :=
  t • (E i j) + u • (E k l)

private def Y (i j k l : I) (t u : R) : Matrix I I R :=
  (t * u) • (E i j) * (E k l)

/-- Own definition of commutator -/
def M_comm (i j k l : I) (t u : R) : Matrix I I R :=
  (M i j t) * (M k l u) * (M i j (-t)) * (M k l (-u))

lemma expand_signed_prod (_X _Y : Matrix I I R) : (1 + _X + _Y) * (1 - _X + _Y) = 1 + (2 : R) • _Y + (_X + _Y) * (-_X + _Y) := by
  algebra
  module

/-- [Mij(t), Mkl(u)] = 1 + 2Y + (X + Y)(-X + Y) -/
lemma M_commutator_calc (i j k l : I) (t u : R) --(hij : i ≠ j) (hkl : k ≠ l)
  : M_comm i j k l t u =
  1 + (2 : R) • (Y i j k l t u) + ((X i j k l t u) + (Y i j k l t u)) * (-(X i j k l t u) + (Y i j k l t u)) := by
  have h₀ : (M i j t) * (M k l u) = 1 + (X i j k l t u) + (Y i j k l t u) := by
    rw [M, M, X, Y]
    algebra
    module
  have h₁ : (M i j (-t)) * (M k l (-u)) = 1 - (X i j k l t u) + (Y i j k l t u) := by
    rw [M, M, X, Y]
    algebra
    module
  rw [M_comm, h₀, mul_assoc, h₁, expand_signed_prod]

theorem M_commutator (i j k l : I) (t u : R) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
  : M_comm i j k l t u = 1 := by
  have Y0 : Y i j k l t u = 0 := by
    rw [Y]
    rw [Matrix.smul_mul, E_mul_eq_zero hjk, smul_zero]
  have X0 : (X i j k l t u) * (X i j k l t u) = 0 := by
    rw [X]
    algebra
    rw [E_mul_eq_zero hij.symm, E_mul_eq_zero hjk, E_mul_eq_zero hil.symm, E_mul_eq_zero hkl.symm]
    simp only [smul_zero, add_zero]
  rw [M_commutator_calc, Y0]
  algebra
  simp only [add_right_eq_self, neg_eq_zero]
  exact X0

theorem M_commutator' (i j k : I) (t u : R) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
  : M_comm i j j k t u  = M i k (t * u) := by
  have hY : Y i j j k t u = (t * u) • (E i k) := by
    rw [Y, Matrix.smul_mul, E_mul]
  have : ((X i j j k t u) + (Y i j j k t u)) * (-(X i j j k t u) + (Y i j j k t u)) = -(t * u) • E i k := by
    rw [X, Y]
    algebra
    simp only [E_mul, E_mul_eq_zero hik.symm, E_mul_eq_zero hjk.symm, E_mul_eq_zero hij.symm]
    module
  rw [M_commutator_calc, this, M, Y, Matrix.smul_mul, E_mul]
  algebra
  module

-- structure ARoot (n : ℕ) where
--   mk ::
--   i : I
--   j : I
--   hne : i ≠ j

-- def M_root (ζ : ARoot n) (t : R) :=
--   1 + (E ζ.i ζ.j t)
