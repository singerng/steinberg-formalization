/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.Upstream.Chevalley.TypeC.Defs

import Steinberg.Upstream.Commutator

variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeC
open Chevalley Chevalley.TypeC

theorem MShort_swap (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (MShort a b i j t hij) = (MShort b a j i (t) hij.symm) := by
  ext1
  simp only [MShort, raw_MShort]
  module

theorem MLong_mul_add {a : Bool} {i : I} {t u : R}
  : (MLong a i t) * (MLong a i u) = MLong a i (t + u) := by
  ext1
  simp only [MLong, raw_MLong, Units.val_mul]
  algebra
  simp only [E_mul_disjoint Signed.ne_of_neg, E_mul_overlap]
  module

theorem MShort_mul_add {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (MShort a b i j t hij) * (MShort a b i j u hij) = MShort a b i j (t + u) hij := by
  ext1
  simp only [MShort, raw_MShort, Units.val_mul]
  algebra
  simp only [
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg
  ]
  module

/- ### Trivial commutators -/

private theorem MShort_prod_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : (a, i) ≠ (!c, k)) (hil : (a, i) ≠ (!d, l)) (hjk : (b, j) ≠ (!c, k)) (hjl : (b, j) ≠ (!d, l)) :
  (raw_MShort a b i j t hij) * (raw_MShort c d k l u hkl) =
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

theorem MShort_comm_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : (a, i) ≠ (!c, k)) (hil : (a, i) ≠ (!d, l)) (hjk : (b, j) ≠ (!c, k)) (hjl : (b, j) ≠ (!d, l))
  : ⁅ (MShort a b i j t hij), (MShort c d k l u hkl) ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  simp only [MShort, Units.val_mul, Units.inv_mk]
  rw [MShort_prod_disjoint hij hkl hik hil hjk hjl]
  rw [MShort_prod_disjoint hkl hij (Signed.neg_of_ne hik).symm (Signed.neg_of_ne hjk).symm
    (Signed.neg_of_ne hil).symm (Signed.neg_of_ne hjl).symm]
  module

/- ### Single commutators -/

theorem MShort_comm_overlap {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (MShort a b i j t hij), (MShort a (!b) i j u hij) ⁆ = MLong a i (-2 * a * b * t * u) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [MShort, raw_MShort, MLong, raw_MLong, Units.val_mul, Units.val_one]
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

theorem MShort_comm_overlap' {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : ⁅ (MShort a b i j t hij), (MShort (!b) c j k u hjk) ⁆ = (MShort a c i k (-b*t*u) hik) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [MShort, raw_MShort, Units.val_mul]
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

theorem MLong_MShort_comm_overlap {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (MShort a (!b) i j t hij), (MLong b j u) ⁆ = (MShort a b i j (t*u) hij) * (MLong a i (a * b * t^2 * u)) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [MShort, raw_MShort, MLong, raw_MLong, Units.val_mul]
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
