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
  h_mul_mul := sorry
