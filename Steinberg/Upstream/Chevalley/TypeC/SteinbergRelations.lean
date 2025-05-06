/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.Upstream.Chevalley.TypeC.MatrixDefs

import Steinberg.Upstream.Commutator

/-!
* Group name: `Sp_{2n+1}(R)`.
* Matrix shape: `(2n)×(2n)` matrices over a ring `R`.
* Group description: this is the group of `(2n)×(2n)` *symplectic* matrices over `R`.
  The coordinates are indexed by `Signed I`, which is a type with `2n` elements when `I` has `n` elements.
* Corresponding root system: `C_n`.
* Generators: Two disjoint classes corresponding to `short` and `long` roots in the
    root system. All generators have `1`'s on the diagonal.
  * Generators for `long` roots: One nonzero off-diagonal entries.
  * Generators for `short` roots: Two paired nonzero off-diagonal entries.

We verify the *Steinberg* relations for these generators.
-/

variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeC
open Chevalley Chevalley.TypeC

theorem C_MShort_swap (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (C_MShort a b i j t hij) = (C_MShort b a j i (t) hij.symm) := by
  ext1
  simp only [C_MShort, raw_C_MShort]
  module

/-! ## Linearity relations -/

theorem C_MLong_mul_add {a : Bool} {i : I} {t u : R}
  : (C_MLong a i t) * (C_MLong a i u) = C_MLong a i (t + u) := by
  ext1
  simp only [C_MLong, raw_C_MLong, Units.val_mul]
  algebra
  simp only [E_mul_disjoint Signed.ne_of_neg, E_mul_overlap]
  module

theorem C_MShort_mul_add {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (C_MShort a b i j t hij) * (C_MShort a b i j u hij) = C_MShort a b i j (t + u) hij := by
  ext1
  simp only [C_MShort, raw_C_MShort, Units.val_mul]
  algebra
  simp only [
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg
  ]
  module

/-! ## Commutator relations -/

/- ### Trivial commutators -/

private theorem C_MShort_prod_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : (a, i) ≠ (!c, k)) (hil : (a, i) ≠ (!d, l)) (hjk : (b, j) ≠ (!c, k)) (hjl : (b, j) ≠ (!d, l)) :
  (raw_C_MShort a b i j t hij) * (raw_C_MShort c d k l u hkl) =
    1 + (a * t) • E (a, i) (!b, j)
      + (b * t) • E (b, j) (!a, i)
      + (c * u) • E (c, k) (!d, l)
      + (d * u) • E (d, l) (!c, k) := by
  algebra
  ring_nf
  simp only [
    E_mul_disjoint (Signed.neg_of_ne hik),
    E_mul_disjoint (Signed.neg_of_ne hil),
    E_mul_disjoint (Signed.neg_of_ne hjk),
    E_mul_disjoint (Signed.neg_of_ne hjl)
  ]
  module

theorem C_MShort_comm_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : (a, i) ≠ (!c, k)) (hil : (a, i) ≠ (!d, l)) (hjk : (b, j) ≠ (!c, k)) (hjl : (b, j) ≠ (!d, l))
  : ⁅ (C_MShort a b i j t hij), (C_MShort c d k l u hkl) ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  simp only [C_MShort, Units.val_mul, Units.inv_mk]
  rw [C_MShort_prod_disjoint hij hkl hik hil hjk hjl]
  rw [C_MShort_prod_disjoint hkl hij (Signed.neg_of_ne hik).symm (Signed.neg_of_ne hjk).symm
    (Signed.neg_of_ne hil).symm (Signed.neg_of_ne hjl).symm]
  module

/- ### Single commutators -/

theorem C_MShort_comm_overlap {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (C_MShort a b i j t hij), (C_MShort a (!b) i j u hij) ⁆ = C_MLong a i (-2 * a * b * t * u) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [C_MShort, raw_C_MShort, C_MLong, raw_C_MLong, Units.val_mul, Units.val_one]
  algebra
  ring_nf
  simp only [
    E_mul_overlap,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    Bool.not_not, Bool.int_of_neg
  ]
  algebra
  module

theorem C_MShort_comm_overlap' {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : ⁅ (C_MShort a b i j t hij), (C_MShort (!b) c j k u hjk) ⁆ = (C_MShort a c i k (-b*t*u) hik) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [C_MShort, raw_C_MShort, Units.val_mul]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    Bool.not_not,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm,
    E_mul_disjoint (Signed.ne_of_ne hjk),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hjk.symm)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hik)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hik.symm)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hij)),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
  ]
  algebra
  simp only [Bool.int_of_neg]
  module

/- ### Double commutators -/

theorem C_MLong_C_MShort_comm_overlap {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (C_MShort a (!b) i j t hij), (C_MLong b j u) ⁆ = (C_MShort a b i j (t*u) hij) * (C_MLong a i (a * b * t^2 * u)) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [C_MShort, raw_C_MShort, C_MLong, raw_C_MLong, Units.val_mul]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    Bool.not_not,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm,
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hij)),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
  ]
  algebra
  simp only [Bool.int_of_neg, square_eq_one]
  module

/-! ## Diagonal relations -/

def C_Short_n_elt (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) :=
  (C_MShort a b i j t.val hij) * (C_MShort (!a) (!b) i j (-t.inv) hij) * (C_MShort a b i j t.val hij)

private lemma C_Short_n_elt_form (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) : (C_Short_n_elt a b i j hij t).val =
  1 + ((2 * a + b) * t.val) • E (a, i) ((!b), j)
    + (a * t.inv) • E ((!a), i) (b, j)
    + ((2 * b + a) * t.val) • E (b, j) ((!a), i)
    + (b * t.inv) • E ((!b), j) (a, i)
    + (a * b : R) • E (a, i) (a, i)
    + (a * b : R) • E (b, j) (b, j)
    + (a * b : R) • E ((!a), i) ((!a), i)
    + (a * b : R) • E ((!b), j) ((!b), j)
  := by
  simp only [C_Short_n_elt, C_MShort, Units.val_mul, raw_C_MShort]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg,
    Bool.not_not
  ]
  algebra
  simp only [Bool.int_of_neg]
  ring_nf
  /- associate to the right so that we can deal with powers of `t` -/
  -- simp only [mul_assoc, Units.inv_eq_val_inv, ←Units.val_pow_eq_pow_val, ←Units.val_mul]
  match_scalars
  any_goals rw [square_eq_one]
  any_goals ring_nf

  sorry

def C_Short_h_elt (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) :=
  (C_Short_n_elt a b i j hij t) * (C_Short_n_elt a b i j hij (-1))

-- a.toRing * b.toRing * 1 + (a.toRing * ↑t * b.toRing * -1 * 2 + ↑t * -1) * 1 + (a.toRing * b.toRing * 1 + 1 * 1)
-- 2ab + 1 - 2abt - t
-- (2ab+1) * (1-t)

private lemma C_Short_h_elt_form (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) : (C_Short_h_elt a b i j hij t).val =
  1 - ((2 * a * b + 1) * (t.val - 1)) • E (a, i) (a, i)
    - ((2 * a * b + 1) * (t.val - 1)) • E (b, j) (b, j)
    - ((2 * a * b + 1) * (t.inv - 1)) • E ((!a), i) ((!a), i)
    - ((2 * a * b + 1) * (t.inv - 1)) • E ((!b), j) ((!b), j)
  := by
  simp only [C_Short_h_elt, Units.val_mul, C_Short_n_elt_form]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm
  ]
  algebra
  ring_nf
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one, inv_neg, square_eq_one]
  ring_nf
  match_scalars

theorem C_Short_diagonal {a b : Bool} {i j : I} {hij : i ≠ j} {t u : Rˣ} :
  (C_Short_h_elt a b i j hij t) * (C_Short_h_elt a b i j hij u) = (C_Short_h_elt a b i j hij (t*u)) := by
  ext1
  simp only [C_Short_h_elt_form, Units.val_mul]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm
  ]
  simp only [Units.inv_eq_val_inv, mul_inv_rev, Units.val_mul]
  module

def C_Long_n_elt (a : Bool) (i : I) (t : Rˣ) :=
  (C_MLong a i t.val) * (C_MLong (!a) i (-t.inv)) * (C_MLong a i t.val)

private lemma C_Long_n_elt_form (a : Bool) (i : I) (t : Rˣ) : (C_Long_n_elt a i t).val =
  1 - E (a, i) (a, i)
    - E ((!a), i) ((!a), i)
    + t.val • E (a, i) ((!a), i)
    - t.inv • E ((!a), i) (a, i)
  := by
  simp only [C_Long_n_elt, C_MLong, Units.val_mul, raw_C_MLong]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint Signed.ne_of_neg,
    Bool.not_not
  ]
  algebra
  simp only [Units.inv_eq_val_inv, Units.inv_mul, Units.mul_inv, neg_mul, Bool.int_of_neg]
  ring_nf
  module

def C_Long_h_elt (a : Bool) (i : I) (t : Rˣ) :=
  (C_Long_n_elt a i t) * (C_Long_n_elt a i (-1))

private lemma C_Long_h_elt_form (a : Bool) (i : I) (t : Rˣ) : (C_Long_h_elt a i t).val =
  1 + (t.val - 1) • E (a, i) (a, i)
    + (t.inv - 1) • E ((!a), i) ((!a), i)
  := by
  simp only [C_Long_h_elt, Units.val_mul, C_Long_n_elt_form]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm
  ]
  algebra
  ring_nf
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one, inv_neg, square_eq_one]
  module

theorem C_Long_diagonal {a : Bool} {i : I} {t u : Rˣ} :
  (C_Long_h_elt a i t) * (C_Long_h_elt a i u) = (C_Long_h_elt a i (t * u)) := by
  ext1
  simp only [C_Long_h_elt_form, Units.val_mul]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm
  ]
  simp only [Units.inv_eq_val_inv, mul_inv_rev, Units.val_mul]
  module

instance instChevalleyRealization (I : Type TI) [DecidableEq I] [Fintype I] [LinearOrder I] (R : Type TR) [CommRing R]
  : ChevalleyRealization (CRoot I) (Signed I) R where
  M (ζ : CRoot I) (t : R) :=
    match ζ with
    | Sum.inl ζ => C_MLong ζ.a ζ.i t
    | Sum.inr ζ => C_MShort ζ.a ζ.b ζ.i ζ.j t ζ.hij.ne

  M_mul_add := by
    intro ζ t u
    cases ζ with
    | inl ζ => exact C_MLong_mul_add
    | inr ζ => exact C_MShort_mul_add ζ.hij.ne
  h_mul_mul := by
    intro ζ t u
    cases ζ with
    | inl ζ => exact C_Long_diagonal
    | inr ζ => exact C_Short_diagonal
