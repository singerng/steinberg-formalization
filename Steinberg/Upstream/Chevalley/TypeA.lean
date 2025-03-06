import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import Steinberg.Upstream.Chevalley.Macro.Algebra
import Steinberg.Upstream.Chevalley.IndicatorMatrix


/-!
  An implementation of the group `GL_{n+1}(R)` of `(n+1)×(n+1)` matrices with determinant `1` over a ring `R`.
  This group is the Chevalley group for the root system `A_n`. This implementation proceeds by constructing
  generator matrices for the group (which are matrices with `1`'s on the diagonal and a single nonzero entry
  off the diagonal, corresponding to elementary operations in Gaussian elimination), and then verifies
  the *Steinberg* relations which these elements satisfy.

  The matrices' rows and columns can be indexed by any type `I` which is an instance of `Fintype` and
  `DecidableEq`.

  TODO: Show that the generators generate the entire group and that the relations are enough to present
  the group.
-/

universe u v

variable {R : Type u} [CommRing R]
variable {I : Type v} [DecidableEq I] [Fintype I]

def M (i j : I) (t : R)  (hij : i ≠ j) : Matrix I I R :=
  1 + t • (E i j)

theorem M_mul_add {i j : I} {t u : R} (hij : i ≠ j)
  : (M i j t hij) * (M i j u hij) = M i j (t + u) hij := by
  simp only [M]
  algebra
  simp only [E_mul_disjoint hij.symm]
  module

theorem M_commutator_disjoint (i j k l : I) (t u : R) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
  : (M i j t hij) * (M k l u hkl) = (M k l u hkl) * (M i j t hij) := by
  simp only [M]
  algebra
  simp only [E_mul_disjoint hij.symm, E_mul_disjoint hjk, E_mul_disjoint hil.symm, E_mul_disjoint hkl.symm]
  algebra
  module

theorem M_commutator_overlap (i j k : I) (t u : R) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : (M i j t hij) * (M j k u hjk) * (M i j (-t) hij) * (M j k (-u) hjk) = M i k (t * u) hik := by
  simp only [M]
  algebra
  simp only [E_mul_disjoint hij.symm, E_mul_disjoint hjk.symm, E_mul_disjoint hik.symm, E_mul_overlap]
  algebra
  module

-- structure ARoot (n : ℕ) where
--   mk ::
--   i : I
--   j : I
--   hne : i ≠ j

-- def M_root (ζ : ARoot n) (t : R) :=
--   1 + (E ζ.i ζ.j t)
