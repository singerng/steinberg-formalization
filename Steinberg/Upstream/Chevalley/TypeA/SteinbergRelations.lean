/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.Upstream.Chevalley.TypeA.Defs

import Steinberg.Upstream.Commutator

/-!
* Group name: `SL_{n}(R)`.
* Matrix shape: `n×n` matrices over a ring `R`.
* Group description: the group of `n×n` matrices with determinant `1` over `R`.
  The coordinates are indexed by a type `I`.
* Corresponding root system: `A_n`.
* Generators: All generators have `1`'s on the diagonal and one off-diagonal entry.

We verify the *Steinberg* relations for these generators.

TODO: Show that the generators generate the entire group and that the relations are enough to present
the group.
-/

variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeA
open Chevalley Chevalley.TypeA

private theorem raw_M_prod_disjoint {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (t u : R) :
  (raw_M i j hij t) * (raw_M k l hkl u) =
    1 + t • E i j + u • E k l := by
  unfold raw_M
  algebra
  rw [E_mul_disjoint hjk]
  module

/-! ## Linearity relations -/

theorem M_mul_add (i j : I) (hij : i ≠ j) (t u : R)
  : (A_M i j hij t) * (A_M i j hij u) = A_M i j hij (t + u) := by
  ext1
  unfold A_M
  simp only [Units.val_mul]
  rw [raw_M_prod_disjoint]
  module
  · exact hij.symm

/-! ## Commutator relations -/

private theorem raw_M_prod_overlap (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (t u : R) :
  (raw_M i j hij t) * (raw_M j k hjk u) =
    1 + t • E i j + u • E j k + (u * t) • E i k := by
  unfold raw_M
  algebra
  rw [E_mul_overlap]
  module

theorem M_commutator_disjoint (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
  (hjk : j ≠ k) (hil : i ≠ l) (t u : R)
  : ⁅ A_M i j hij t, A_M k l hkl u ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  unfold A_M
  simp only [Units.val_mul]
  rw [raw_M_prod_disjoint hij hkl hjk]
  rw [raw_M_prod_disjoint hkl hij hil.symm]
  module

theorem M_commutator_overlap (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t u : R)
  : ⁅ A_M i j hij t, A_M j k hjk u ⁆ = A_M i k hik (t * u) := by
  apply eq_comm_of_reorder_left
  ext1
  unfold A_M
  simp only [Units.val_mul]
  rw [raw_M_prod_overlap i j k hij hjk]
  rw [raw_M_prod_disjoint hik hjk hjk.symm]
  unfold raw_M
  algebra
  simp only [E_mul_disjoint hik.symm]
  module

/-! ## Diagonal relations -/

def n_elt (i j : I) (hij : i ≠ j) (t : Rˣ) := (A_M i j hij t.val) * (A_M j i hij.symm (-t.inv)) * (A_M i j hij t.val)

private lemma n_elt_form (i j : I) (hij : i ≠ j) (t : Rˣ) : (n_elt i j hij t).val =
  1 + t.val • E i j
    - t.inv • E j i
    - E i i
    - E j j
  := by
  simp only [n_elt, A_M, Units.val_mul, raw_M]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint hij,
    E_mul_disjoint hij.symm
  ]
  algebra
  simp only [Units.inv_eq_val_inv, Units.inv_mul, Units.mul_inv, neg_mul]
  module

def h_elt (i j : I) (hij : i ≠ j) (t : Rˣ) := (n_elt i j hij t) * (n_elt i j hij (-1))

private lemma h_elt_form (i j : I) (hij : i ≠ j) (t : Rˣ) : (h_elt i j hij t).val =
  1 + (t.val - 1) • E i i + (t.inv - 1) • E j j
  := by
  simp only [h_elt, Units.val_mul, n_elt_form]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint hij,
    E_mul_disjoint hij.symm,
  ]
  algebra
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one, inv_neg]
  module

theorem M_diagonal (i j : I) (hij : i ≠ j) (t u : Rˣ) : (h_elt i j hij t) * (h_elt i j hij u) = (h_elt i j hij (t*u)) := by
  ext1
  simp only [h_elt_form, Units.val_mul]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint hij,
    E_mul_disjoint hij.symm
  ]
  ring_nf
  simp only [Units.inv_eq_val_inv, mul_inv_rev, Units.val_mul]
  module
