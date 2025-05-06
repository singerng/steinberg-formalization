/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.Upstream.Chevalley.TypeD.Defs

import Steinberg.Upstream.Commutator

/-!
* Group name: `SO_{2n}(R)`.
* Matrix shape: `(2n)×(2n)` matrices over a ring `R`.
* Group description: the group of `(2n)×(2n)` *orthogonal* matrices with determinant
  `1` over `R`. The coordinates are indexed by `Signed I`, which is a type with `2n`
  elements when `I` has `n` elements.
* Corresponding root system: `D_n`.
* Generators: All generators have `1`'s on the diagonal and two paired off-diagonal entries.

We verify the *Steinberg* relations for these generators.
-/

variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeD
open Chevalley.TypeD

theorem M_swap (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (D_M a b i j hij t) = (D_M b a j i hij.symm (-t)) := by
  ext1
  simp only [D_M, raw_M]
  module

/-! ## Commutator relations -/

theorem M_add {a b : Bool} {i j : I} {hij : i ≠ j} {t u : R}
  : (D_M a b i j hij t) * (D_M a b i j hij u) = D_M a b i j hij (t + u) := by
  ext1
  simp only [D_M, raw_M, Units.val_mul]
  algebra
  simp only [
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint (Signed.ne_of_neg),
    E_mul_disjoint (Signed.ne_of_neg).symm
  ]
  algebra
  module

/-! ## Linearity relations -/

/- ### Trivial commutators -/

theorem M_comm_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : (a, i) ≠ (!c, k)) (hil : (a, i) ≠ (!d, l)) (hjk : (b, j) ≠ (!c, k)) (hjl : (b, j) ≠ (!d, l))
  : ⁅ (D_M a b i j hij t), (D_M c d k l hkl u) ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  simp only [D_M, Units.val_mul, Units.inv_mk]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    E_mul_disjoint hik.symm,
    E_mul_disjoint hil.symm,
    E_mul_disjoint hjk.symm,
    E_mul_disjoint hjl.symm,
    E_mul_disjoint (Signed.neg_of_ne hik),
    E_mul_disjoint (Signed.neg_of_ne hil),
    E_mul_disjoint (Signed.neg_of_ne hjk),
    E_mul_disjoint (Signed.neg_of_ne hjl)
    ]
  module

theorem M_comm_disjoint' {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (D_M a b i j hij t), (D_M a (!b) i j hij u) ⁆ = 1 := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [D_M, raw_M, Units.val_mul, Units.val_one]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    Bool.not_not
  ]
  module

/- ### Single commutators -/

theorem M_comm_overlap {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : ⁅ (D_M a b i j hij t), (D_M (!b) c j k hjk u) ⁆ = (D_M a c i k hik (t*u)) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [D_M, raw_M, Units.val_mul]
  algebra
  ring_nf
  simp only [
    E_mul_overlap,
    Bool.not_not,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint (Signed.ne_of_ne hjk),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hjk.symm)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hik)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hik.symm)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hij)),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
  ]
  algebra
  module


/-! ## Diagonal relations -/

def n_elt (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) :=
  (D_M a b i j hij t.val) * (D_M (!a) (!b) i j hij (-t.inv)) * (D_M a b i j hij t.val)

private lemma n_elt_form (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) : (n_elt a b i j hij t).val =
  1 + (3 * t.val) • E (a, i) (!b, j) - (3 * t.val) • E (b, j) (!a, i)
    - (t.inv) • E (!a, i) (b, j) + (t.inv) • E (!b, j) (a, i)
    + E (a, i) (a, i) + E (b, j) (b, j) + E (!a, i) (!a, i) + E (!b, j) (!b, j)
  := by
  simp only [n_elt, D_M, Units.val_mul, raw_M]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg,
    Bool.not_not
  ]
  algebra
  simp only [Units.inv_eq_val_inv, Units.inv_mul, Units.mul_inv, neg_mul]
  module

def h_elt (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) := (n_elt a b i j hij t) * (n_elt a b i j hij (-1))

private lemma h_elt_form (A B C D : R) (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) : (h_elt a b i j hij t).val =
  -- 1 + (3 * (1 - t.val)) • E (a, i) (a, i) - (3 * (1 - t.val)) • E (b, j) (b, j)
  --   - (3 * (1 - t.inv)) • E (!a, i) (!a, i) + (3 * (1 - t.inv)) • E (!b, j) (!b, j)
  1 + A • E (a, i) (a, i) + B • E (b, j) (b, j)
    + C • E (!a, i) (!a, i) + D • E (!b, j) (!b, j)
  := by
  simp only [h_elt, Units.val_mul, n_elt_form]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm
  ]
  algebra
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one, inv_neg]
  match_scalars
  module


theorem M_diagonal (a b : Bool) (i j : I) (hij : i ≠ j) (t u : Rˣ) : (h_elt a b i j hij t) * (h_elt a b i j hij u) = (h_elt a b i j hij (t*u)) := by
  ext1
  simp only [h_elt_form, Units.val_mul]
  algebra
  simp only [
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm
  ]
  ring_nf
  simp only [Units.inv_eq_val_inv, mul_inv_rev, Units.val_mul]
  module
