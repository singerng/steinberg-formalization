/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import Steinberg.Macro.Group

import Steinberg.Upstream.Chevalley.Macro.Algebra
import Steinberg.Upstream.Chevalley.IndicatorMatrix
import Steinberg.Upstream.Commutator


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

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeA
open Chevalley.TypeA Mathlib.Group.Commutator

private def raw_M (i j : I) (hij : i ≠ j) (t : R) : Matrix I I R :=
  1 + t • (E i j)

private theorem val_inv_of_M {i j : I} {t : R} {hij : i ≠ j} :
  (raw_M i j hij t) * (raw_M i j hij (-t)) = 1 := by
  simp only [raw_M]
  algebra
  simp only [E_mul_disjoint hij.symm]
  module

private theorem inv_val_of_M {i j : I} {t : R} {hij : i ≠ j} :
  (raw_M i j hij (-t)) * (raw_M i j hij t) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_M

def A_M (i j : I) (hij : i ≠ j) (t : R) : Matrix.GeneralLinearGroup I R :=
  {
    val := raw_M i j hij t,
    inv := raw_M i j hij (-t),
    val_inv := val_inv_of_M,
    inv_val := inv_val_of_M
  }

private theorem raw_M_prod_overlap (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (t u : R) :
  (raw_M i j hij t) * (raw_M j k hjk u) =
    1 + t • E i j + u • E j k + (u * t) • E i k := by
  unfold raw_M
  algebra
  rw [E_mul_overlap]
  module

private theorem raw_M_prod_disjoint (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (t u : R) :
  (raw_M i j hij t) * (raw_M k l hkl u) =
    1 + t • E i j + u • E k l := by
  unfold raw_M
  algebra
  rw [E_mul_disjoint hjk]
  module

theorem M_mul_add (i j : I) (hij : i ≠ j) (t u : R)
  : (A_M i j hij t) * (A_M i j hij u) = A_M i j hij (t + u) := by
  ext1
  unfold A_M
  simp only [Units.val_mul]
  rw [raw_M_prod_disjoint i j i j hij hij hij.symm]
  unfold raw_M
  module

theorem M_commutator_disjoint (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
  (hjk : j ≠ k) (hil : i ≠ l) (t u : R)
  : ⁅ A_M i j hij t, A_M k l hkl u ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  unfold A_M
  simp only [Units.val_mul]
  rw [raw_M_prod_disjoint i j k l hij hkl hjk]
  rw [raw_M_prod_disjoint k l i j hkl hij hil.symm]
  module

theorem M_commutator_overlap (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t u : R)
  : ⁅ A_M i j hij t, A_M j k hjk u ⁆ = A_M i k hik (t * u) := by
  apply eq_comm_of_reorder_left
  ext1
  unfold A_M
  simp only [Units.val_mul]
  rw [raw_M_prod_overlap i j k hij hjk]
  rw [raw_M_prod_disjoint i k j k hik hjk hjk.symm]
  unfold raw_M
  algebra
  simp only [E_mul_disjoint hik.symm]
  module

/-- ### Type-A roots -/

structure ARoot (I : Type u) [DecidableEq I] [Fintype I] where
  mk ::
  i : I
  j : I
  hij : i ≠ j

def ARoot.M (ζ : ARoot I) (t : R) := A_M ζ.i ζ.j ζ.hij t
