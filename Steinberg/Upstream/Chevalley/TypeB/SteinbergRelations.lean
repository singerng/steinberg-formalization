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

private lemma raw_MLong_prod_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ (!c).inj k) (hil : a.inj i ≠ (!d).inj l) (hjk : b.inj j ≠ (!c).inj k) (hjl : b.inj j ≠ (!d).inj l)
  : (raw_MLong a b i j t hij) * (raw_MLong c d k l u hkl) =
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

private lemma raw_MShort_prod {a b : Bool} {i j : I} {t u : R} (hij : a.inj i ≠ (!b).inj j) :
  (raw_MShort a i t) * (raw_MShort b j u) =
  1 + (2 * a * t) • E (a.inj i) ZSigned.zero
    - (a * t) • E ZSigned.zero ((!a).inj i)
    - (t ^ 2) • E (Bool.inj a i) ((!a).inj i)
    + (2 * b * u) • E (b.inj j) ZSigned.zero
    - (b * u) • E ZSigned.zero ((!b).inj j)
    - (2 * a * b * t * u) • E (a.inj i) ((!b).inj j)
    - (u ^ 2) • E (b.inj j) ((!b).inj j)
  := by
  unfold raw_MShort
  algebra
  simp only [
    E_mul_disjoint ZSigned.zero_ne_signed,
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint (ZSigned.neg_of_ne hij),
    E_mul_overlap
  ]
  module

theorem MLong_swap (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (MLong a b i j t hij) = (MLong b a j i (-t * a * b) hij.symm) := by
  ext1
  simp only [MLong, raw_MLong]
  ring_nf
  simp only [square_eq_one]
  module

/-! ## Linearity relations -/

theorem MShort_mul_add {a : Bool} {i : I} {t u : R}
  : (MShort a i t) * (MShort a i u) = MShort a i (t + u) := by
  ext1
  simp only [MShort, raw_MShort, Units.val_mul]
  rw [raw_MShort_prod]
  · match_scalars
    all_goals (ring_nf)
    simp only [square_eq_one]
    ring_nf
  · exact ZSigned.ne_of_neg.symm

theorem MLong_mul_add {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (MLong a b i j t hij) * (MLong a b i j u hij) = MLong a b i j (t + u) hij := by
  ext1
  simp only [MLong, Units.val_mul]
  rw [raw_MLong_prod_disjoint hij]
  module
  · exact ZSigned.ne_of_neg.symm
  · exact ZSigned.ne_of_ne hij
  · exact ZSigned.ne_of_ne hij.symm
  · exact ZSigned.ne_of_neg.symm

/-! ## Commutator relations -/

/- ### Trivial commutators -/

theorem MLong_comm_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ (!c).inj k) (hil : a.inj i ≠ (!d).inj l) (hjk : b.inj j ≠ (!c).inj k) (hjl : b.inj j ≠ (!d).inj l)
  : ⁅ (MLong a b i j t hij), (MLong c d k l u hkl) ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  simp only [MLong, Units.val_mul, Units.inv_mk]
  rw [raw_MLong_prod_disjoint hij hkl hik hil hjk hjl]
  rw [raw_MLong_prod_disjoint hkl hij (ZSigned.neg_of_ne hik).symm (ZSigned.neg_of_ne hjk).symm
    (ZSigned.neg_of_ne hil).symm (ZSigned.neg_of_ne hjl).symm]
  module

private lemma raw_MLong_prod_disjoint' {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (raw_MLong a b i j t hij) * (raw_MLong a (!b) i j u hij) =
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

theorem MLong_comm_disjoint' {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (MLong a b i j t hij), (MLong a (!b) i j u hij) ⁆ = 1 := by
  apply triv_comm_iff_commutes.mpr
  ext1
  simp only [MLong, Units.val_mul]
  nth_rewrite 4 [← Bool.not_not b]
  simp only [raw_MLong_prod_disjoint']
  rw [Bool.not_not]
  module

theorem MLong_MShort_comm_disjoint {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j)
  (hik : a.inj i ≠ (!c).inj k) (hjk : b.inj j ≠ (!c).inj k)
  : ⁅ (MLong a b i j t hij), (MShort c k u) ⁆ = 1 := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  simp only [one_mul]
  ext1
  simp only [MLong, raw_MLong, MShort, raw_MShort, Units.val_mul]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    E_mul_disjoint ZSigned.zero_ne_signed,
    E_mul_disjoint ZSigned.signed_ne_zero,
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint hik.symm,
    E_mul_disjoint hjk.symm,
    E_mul_disjoint (ZSigned.neg_of_ne hik),
    E_mul_disjoint (ZSigned.neg_of_ne hjk)
    ]
  algebra
  module

/- ### Single commutators -/

theorem MLong_comm_overlap {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : ⁅ (MLong a b i j t hij), (MLong (!b) c j k u hjk) ⁆ = (MLong a c i k (-b*t*u) hik) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [MLong, raw_MLong, Units.val_mul]
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

theorem MShort_comm {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (MShort a i t), (MShort b j u) ⁆ = MLong a b i j (-2*b*t*u) hij := by
  rw [commutatorElement_def']
  ext1
  simp only [MShort, MLong, raw_MLong, Units.inv_mk, Units.val_mul]
  repeat rw [raw_MShort_prod (ZSigned.ne_of_ne hij)]
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

theorem MLong_MShort_comm_overlap (a b : Bool) (i j : I) (t u : R) (hij : i ≠ j)
  : ⁅ (MLong a b i j t hij), (MShort (!a) i u) ⁆ =
    (MShort b j (b*t*u)) * (MLong (!a) b i j (-t*u^2) hij) := by
    rw [commutatorElement_def]
    ext1
    simp only [MShort, MLong, raw_MShort, raw_MLong, Units.inv_mk, Units.val_mul]
    algebra
    simp only [Bool.not_not]
    simp only [E_mul_overlap,
      E_mul_disjoint ZSigned.zero_ne_signed,
      E_mul_disjoint ZSigned.signed_ne_zero,
      E_mul_disjoint ZSigned.ne_of_neg,
      E_mul_disjoint (ZSigned.ne_of_neg).symm,
      E_mul_disjoint (ZSigned.ne_of_ne hij),
      E_mul_disjoint (ZSigned.ne_of_ne hij.symm)]
    algebra
    ring_nf
    match_scalars
    any_goals simp
    any_goals simp only [square_eq_one]
    all_goals ring_nf
    all_goals simp only [square_eq_one]
    all_goals ring_nf
