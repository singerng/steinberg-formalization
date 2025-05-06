/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.Upstream.Chevalley.TypeB.Defs

import Steinberg.Upstream.Commutator

/-!
* Group name: `Ω_{2n+1}(R)`.
* Matrix shape: `(2n+1)×(2n+1)` matrices over a ring `R`.
* Group description: this is a "mysterious" subgroup of `SO_{2n+1}(R)`, the group
    of `(2n+1)×(2n+1)` *orthogonal* matrices with determinant `1` over `R`. The coordinates
    are indexed by `ZSigned I`, which is a type with `2n+1` elements when `I` has `n` elements.
* Corresponding root system: `B_n`.
* Generators: Two disjoint classes corresponding to `short` and `long` roots in the
    root system. All generators have `1`'s on the diagonal.
  * Generators for `long` roots: Two paired nonzero off-diagonal entries.
  * Generators for `short` roots: Three nonzero off-diagonal entries.

We verify the *Steinberg* relations for these generators.
-/

variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeB
open Chevalley Chevalley.TypeB

private lemma raw_B_MLong_prod_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ (!c).inj k) (hil : a.inj i ≠ (!d).inj l) (hjk : b.inj j ≠ (!c).inj k) (hjl : b.inj j ≠ (!d).inj l)
  : (raw_B_MLong a b i j t hij) * (raw_B_MLong c d k l u hkl) =
    1 + (a * t) • E (a.inj i) ((!b).inj j)
      - (a * t) • E (b.inj j) ((!a).inj i)
      + (c * u) • E (c.inj k) ((!d).inj l)
      - (c * u) • E (d.inj l) ((!c).inj k)
    := by
  algebra
  ring_nf
  simp only [
    E_mul_disjoint (ZSigned.neg_of_ne hik),
    E_mul_disjoint (ZSigned.neg_of_ne hil),
    E_mul_disjoint (ZSigned.neg_of_ne hjk),
    E_mul_disjoint (ZSigned.neg_of_ne hjl)
  ]
  algebra

private lemma raw_B_MShort_prod {a b : Bool} {i j : I} {t u : R} (hij : a.inj i ≠ (!b).inj j) :
  (raw_B_MShort a i t) * (raw_B_MShort b j u) =
  1 + (2 * a * t) • E (a.inj i) ZSigned.zero
    - (a * t) • E ZSigned.zero ((!a).inj i)
    - (t ^ 2) • E (a.inj i) ((!a).inj i)
    + (2 * b * u) • E (b.inj j) ZSigned.zero
    - (b * u) • E ZSigned.zero ((!b).inj j)
    - (2 * a * b * t * u) • E (a.inj i) ((!b).inj j)
    - (u ^ 2) • E (b.inj j) ((!b).inj j)
  := by
  unfold raw_B_MShort
  algebra
  simp only [
    E_mul_disjoint ZSigned.zero_ne_signed,
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint (ZSigned.neg_of_ne hij),
    E_mul_overlap
  ]
  module

theorem B_MLong_swap (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (B_MLong a b i j t hij) = (B_MLong b a j i (-t * a * b) hij.symm) := by
  ext1
  simp only [B_MLong, raw_B_MLong]
  ring_nf
  simp only [square_eq_one]
  module

/-! ## Linearity relations -/

theorem B_MShort_mul_add {a : Bool} {i : I} {t u : R}
  : (B_MShort a i t) * (B_MShort a i u) = B_MShort a i (t + u) := by
  ext1
  simp only [B_MShort, raw_B_MShort, Units.val_mul]
  rw [raw_B_MShort_prod]
  · match_scalars
    all_goals (ring_nf)
    simp only [square_eq_one]
    ring_nf
  · exact ZSigned.ne_of_neg.symm

theorem B_MLong_mul_add {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (B_MLong a b i j t hij) * (B_MLong a b i j u hij) = B_MLong a b i j (t + u) hij := by
  ext1
  simp only [B_MLong, Units.val_mul]
  rw [raw_B_MLong_prod_disjoint hij]
  module
  · exact ZSigned.ne_of_neg.symm
  · exact ZSigned.ne_of_ne hij
  · exact ZSigned.ne_of_ne hij.symm
  · exact ZSigned.ne_of_neg.symm

/-! ## Commutator relations -/

/- ### Trivial commutators -/

theorem B_MLong_comm_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ (!c).inj k) (hil : a.inj i ≠ (!d).inj l) (hjk : b.inj j ≠ (!c).inj k) (hjl : b.inj j ≠ (!d).inj l)
  : ⁅ (B_MLong a b i j t hij), (B_MLong c d k l u hkl) ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  simp only [B_MLong, Units.val_mul, Units.inv_mk]
  rw [raw_B_MLong_prod_disjoint hij hkl hik hil hjk hjl]
  rw [raw_B_MLong_prod_disjoint hkl hij
    (ZSigned.neg_of_ne hik).symm (ZSigned.neg_of_ne hjk).symm
    (ZSigned.neg_of_ne hil).symm (ZSigned.neg_of_ne hjl).symm]
  module

private lemma raw_B_MLong_prod_disjoint' {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (raw_B_MLong a b i j t hij) * (raw_B_MLong a (!b) i j u hij) =
    1 + (a * t) • E (a.inj i) ((!b).inj j)
      - (a * t) • (E (b.inj j) ((!a).inj i))
      + (a * u) • (E (a.inj i) (b.inj j))
      - (a * u) • (E ((!b).inj j) ((!a).inj i))
      - (t * u) • (E (a.inj i) ((!a).inj i))
    := by
  algebra
  ring_nf
  simp only [
    square_eq_one,
    Bool.not_not,
    E_mul_overlap,
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint (ZSigned.ne_of_ne hij),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm)
  ]
  module

theorem B_MLong_comm_disjoint' {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (B_MLong a b i j t hij), (B_MLong a (!b) i j u hij) ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  simp only [B_MLong, Units.val_mul]
  nth_rewrite 4 [← Bool.not_not b]
  simp only [raw_B_MLong_prod_disjoint']
  rw [Bool.not_not]
  module

private lemma B_MLong_MShort_prod_disjoint {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j)
  (hik : a.inj i ≠ (!c).inj k) (hjk : b.inj j ≠ (!c).inj k)
  : (raw_B_MLong a b i j t hij) * (raw_B_MShort c k u) =
  1 + (a * t) • E (a.inj i) ((!b).inj j)
    - (a * t) • E (b.inj j) ((!a).inj i)
    + (c * u * 2) • E (c.inj k) ZSigned.zero
    - (c * u) • E ZSigned.zero ((!c).inj k)
    - (u ^ 2) • E (c.inj k) ((!c).inj k) := by
  simp only [B_MLong, raw_B_MLong, B_MShort, raw_B_MShort, Units.val_mul]
  algebra
  simp only [
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint (ZSigned.neg_of_ne hik),
    E_mul_disjoint (ZSigned.neg_of_ne hjk)
  ]
  module

theorem B_MLong_MShort_comm_disjoint {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j)
  (hik : a.inj i ≠ (!c).inj k) (hjk : b.inj j ≠ (!c).inj k)
  : ⁅ (B_MLong a b i j t hij), (B_MShort c k u) ⁆ = 1 := by
  rw [commutatorElement_def']
  ext1
  simp only [B_MLong, B_MShort, Units.val_mul, Units.inv_mk, Units.val_one]
  repeat rw [B_MLong_MShort_prod_disjoint hij hik hjk]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint ZSigned.zero_ne_signed,
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint (ZSigned.ne_of_ne hij),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
    E_mul_disjoint hik.symm,
    E_mul_disjoint hjk.symm,
    E_mul_disjoint (ZSigned.neg_of_ne hik),
    E_mul_disjoint (ZSigned.neg_of_ne hjk)
  ]
  algebra
  ring_nf
  simp only [square_eq_one]
  module


/- ### Single commutators -/

theorem B_MLong_comm_overlap {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : ⁅ (B_MLong a b i j t hij), (B_MLong (!b) c j k u hjk) ⁆ = (B_MLong a c i k (-b*t*u) hik) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [B_MLong, raw_B_MLong, Units.val_mul]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    Bool.not_not,
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint ZSigned.ne_of_neg.symm,
    E_mul_disjoint (ZSigned.ne_of_ne hjk),
    E_mul_disjoint (ZSigned.neg_of_ne (ZSigned.ne_of_ne hjk.symm)),
    E_mul_disjoint (ZSigned.neg_of_ne (ZSigned.ne_of_ne hik)),
    E_mul_disjoint (ZSigned.neg_of_ne (ZSigned.ne_of_ne hik.symm)),
    E_mul_disjoint (ZSigned.neg_of_ne (ZSigned.ne_of_ne hij)),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
  ]
  algebra
  simp only [Bool.int_of_neg]
  module

theorem B_MShort_comm {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (B_MShort a i t), (B_MShort b j u) ⁆ = B_MLong a b i j (-2*b*t*u) hij := by
  rw [commutatorElement_def']
  ext1
  simp only [B_MShort, B_MLong, raw_B_MLong, Units.inv_mk, Units.val_mul]
  repeat rw [raw_B_MShort_prod (ZSigned.ne_of_ne hij)]
  algebra
  simp only [
    E_mul_disjoint ZSigned.zero_ne_signed,
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint (ZSigned.ne_of_ne hij),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
    E_mul_overlap
  ]
  algebra
  ring_nf
  simp only [square_eq_one]
  module

/- ### Double commutators -/


private lemma B_MLong_B_MShort_prod_overlap {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (raw_B_MLong a b i j t hij) * (raw_B_MShort (!a) i u) =
  1 + (a * t) • E (a.inj i) ((!b).inj j)
    - (a * t) • E (b.inj j) ((!a).inj i)
    + (2 * (!a) * u) • E ((!a).inj i) ZSigned.zero
    - (2 * (!a) * u * (a * t)) • E (b.inj j) ZSigned.zero
    + (a * u) • E ZSigned.zero (a.inj i)
    - u ^ 2 • E ((!a).inj i) (a.inj i)
    + (u ^ 2 * (a * t)) • E (b.inj j) (a.inj i) := by
  simp only [raw_B_MLong, raw_B_MShort]
  algebra
  simp only [
    Bool.not_not,
    Bool.int_of_neg,
    E_mul_overlap,
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm)
  ]
  algebra
  module

theorem B_MLong_B_MShort_comm_overlap (a b : Bool) (i j : I) (t u : R) (hij : i ≠ j)
  : ⁅ (B_MLong a b i j t hij), (B_MShort (!a) i u) ⁆ =
    (B_MShort b j (b*t*u)) * (B_MLong (!a) b i j (-t*u^2) hij) := by
    rw [commutatorElement_def']
    ext1
    simp only [B_MShort, B_MLong, Units.inv_mk, Units.val_mul]
    repeat rw [B_MLong_B_MShort_prod_overlap hij]
    have :
      raw_B_MLong (!a) b i j (-t * u ^ 2) hij * raw_B_MShort b j (b * t * u) =
      raw_B_MShort b j (b * t * u) * raw_B_MLong (!a) b i j (-t * u ^ 2) hij := by
      apply triv_comm_iff_commutes.mp
      sorry
    rw [←this]
    rw [B_MLong_MShort_prod_disjoint]
    algebra
    simp only [Bool.not_not]
    simp only [
      E_mul_overlap,
      E_mul_disjoint ZSigned.zero_ne_signed,
      E_mul_disjoint ZSigned.signed_ne_zero,
      E_mul_disjoint ZSigned.ne_of_neg,
      E_mul_disjoint (ZSigned.ne_of_neg).symm,
      E_mul_disjoint (ZSigned.ne_of_ne hij),
      E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
      Bool.int_of_neg
    ]
    ring_nf
    simp only [square_eq_one, cube_eq]
    module
    · exact ZSigned.ne_of_ne hij
    · exact ZSigned.ne_of_neg.symm

/-! ## Diagonal relations -/

variable {F : Type TF} [Field F]

def B_Long_n_elt (a b : Bool) (i j : I) (hij : i ≠ j) (t : F) :=
  (B_MLong a b i j t hij) * (B_MLong (!a) (!b) i j (-t⁻¹) hij) * (B_MLong a b i j t hij)

private lemma B_Long_n_elt_form (a b : Bool) (i j : I) (hij : i ≠ j) (t : F) (h : t ≠ 0) : (B_Long_n_elt a b i j hij t).val =
  1 + (a * t) • E (a.inj i) ((!b).inj j)
    + (a * t⁻¹) • E ((!a).inj i) (b.inj j)
    - (a * t) • E (b.inj j) ((!a).inj i)
    - (a * t⁻¹) • E ((!b).inj j) (a.inj i)
    - E (a.inj i) (a.inj i)
    - E (b.inj j) (b.inj j)
    - E ((!a).inj i) ((!a).inj i)
    - E ((!b).inj j) ((!b).inj j)
  := by
  simp only [B_Long_n_elt, B_MLong, Units.val_mul, raw_B_MLong]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (ZSigned.ne_of_ne hij),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
    E_mul_disjoint ZSigned.ne_of_neg,
    Bool.not_not
  ]
  algebra
  simp only [Bool.int_of_neg]
  ring_nf
  -- simp only [pow_two]
  match_scalars
  · trivial
  · rw [cube_eq]
    simp only [mul_one, add_right_eq_self]
    group
    simp only [Int.reduceNeg, zpow_neg, zpow_one]


def B_Long_h_elt (a b : Bool) (i j : I) (hij : i ≠ j) (t : F) :=
  (B_Long_n_elt a b i j hij t) * (B_Long_n_elt a b i j hij (-1))

private lemma B_Long_h_elt_form (a b : Bool) (i j : I) (hij : i ≠ j) (t : F) : (B_Long_h_elt a b i j hij t).val =
  1 + (t - 1) • E (a.inj i) (a.inj i)
    + (t - 1) • E (b.inj j) (b.inj j)
    + (t⁻¹ - 1) • E ((!a).inj i) ((!a).inj i)
    + (t⁻¹ - 1) • E ((!b).inj j) ((!b).inj j)
  := by
  simp only [B_Long_h_elt, Units.val_mul, B_Long_n_elt_form]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (ZSigned.ne_of_ne hij),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint ZSigned.ne_of_neg.symm
  ]
  algebra
  ring_nf
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one, inv_neg, square_eq_one]
  module

theorem B_Long_M_diagonal (a b : Bool) (i j : I) (hij : i ≠ j) (t u : F) :
  (B_Long_h_elt a b i j hij t) * (B_Long_h_elt a b i j hij u) = (B_Long_h_elt a b i j hij (t*u)) := by
  ext1
  simp only [B_Long_h_elt_form, Units.val_mul]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint (ZSigned.ne_of_ne hij),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint ZSigned.ne_of_neg.symm
  ]
  ring_nf
  simp only [Units.inv_eq_val_inv, mul_inv_rev, Units.val_mul]
  module

def B_Short_n_elt (a : Bool) (i : I) (t : F) :=
  (B_MShort a i t) * (B_MShort (!a) i (-t⁻¹)) * (B_MShort a i t)

private lemma B_Short_n_elt_form (A B C D : R) (a : Bool) (i : I) (t : F) : (B_Short_n_elt a i t).val =
  1 - 2 • E ZSigned.zero ZSigned.zero
    - 1 • E (a.inj i) (a.inj i)
    - 1 • E ((!a).inj i) ((!a).inj i)
  := by
  simp only [B_Short_n_elt, B_MShort, Units.val_mul, raw_B_MShort]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint ZSigned.zero_ne_signed,
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint ZSigned.ne_of_neg,
    Bool.not_not
  ]
  algebra
  simp only [Units.inv_eq_val_inv, Units.inv_mul, Units.mul_inv, neg_mul, Bool.int_of_neg]
  ring_nf
  simp only [square_eq_one, cube_eq]
  match_scalars
  all_goals ring_nf
  -- rw [three_two]
  group
  rw [pow_two, pow_three]
  have : ↑t ^ 2 * ↑t⁻¹ = ↑ t := by rw [pow_two]
  aesop?
  sorry

def B_Short_h_elt (a : Bool) (i : I) (t : Rˣ) :=
  (B_Short_n_elt a i t) * (B_Short_n_elt a i (-1))

-- private lemma B_Long_h_elt_form (a b : Bool) (i j : I) (hij : i ≠ j) (t : Rˣ) : (B_Long_h_elt a b i j hij t).val =
--   1 + (t.val - 1) • E (a.inj i) (a.inj i)
--     + (t.val - 1) • E (b.inj j) (b.inj j)
--     + (t.inv - 1) • E ((!a).inj i) ((!a).inj i)
--     + (t.inv - 1) • E ((!b).inj j) ((!b).inj j)
--   := by
--   simp only [B_Long_h_elt, Units.val_mul, B_Long_n_elt_form]
--   algebra
--   simp only [
--     E_mul_overlap,
--     E_mul_disjoint (ZSigned.ne_of_ne hij),
--     E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
--     E_mul_disjoint ZSigned.ne_of_neg,
--     E_mul_disjoint ZSigned.ne_of_neg.symm
--   ]
--   algebra
--   ring_nf
--   simp only [Units.inv_eq_val_inv, inv_one, Units.val_one, inv_neg, square_eq_one]
--   module

-- theorem B_Long_M_diagonal (a b : Bool) (i j : I) (hij : i ≠ j) (t u : Rˣ) :
--   (B_Long_h_elt a b i j hij t) * (B_Long_h_elt a b i j hij u) = (B_Long_h_elt a b i j hij (t*u)) := by
--   ext1
--   simp only [B_Long_h_elt_form, Units.val_mul]
--   algebra
--   simp only [
--     E_mul_overlap,
--     E_mul_disjoint (ZSigned.ne_of_ne hij),
--     E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
--     E_mul_disjoint ZSigned.ne_of_neg,
--     E_mul_disjoint ZSigned.ne_of_neg.symm
--   ]
--   ring_nf
--   simp only [Units.inv_eq_val_inv, mul_inv_rev, Units.val_mul]
--   module
