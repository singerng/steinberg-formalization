/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.IndicatorMatrix
import Steinberg.Upstream.Chevalley.TypeB.SignedWithZero
import Steinberg.Upstream.Chevalley.TypeB.BoolToRing

import Steinberg.Upstream.Chevalley.Macro.Algebra

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeB
open Chevalley.TypeB

/-- The generator matrices -/
abbrev raw_MShort (a : Bool) (i : I) (t : R) : Matrix (SignedWithZero I) (SignedWithZero I) R :=
  1 + (2 * a * t) • (E (a.inj i) SignedWithZero.zero)
    - (a * t) • (E SignedWithZero.zero ((!a).inj i))
    - (t^2) • (E (a.inj i) ((!a).inj i))

private theorem val_inv_of_MShort {a : Bool} {i : I} {t : R} :
  (raw_MShort a i t) * (raw_MShort a i (-t)) = 1 := by
  simp only [raw_MShort]
  algebra
  simp only [E_mul_overlap,
    E_mul_disjoint SignedWithZero.ne_of_neg,
    E_mul_disjoint SignedWithZero.zero_ne_signed,
    E_mul_disjoint (Ne.symm SignedWithZero.zero_ne_signed)]
  ring_nf
  simp only [square_eq_one]
  module

private theorem inv_val_of_MShort {a : Bool} {i : I} {t : R} :
  (raw_MShort a i (-t)) * (raw_MShort a i t) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_MShort

def MShort (a : Bool) (i : I) (t : R) : Matrix.GeneralLinearGroup (SignedWithZero I) R :=
  {
    val := raw_MShort a i t,
    inv := raw_MShort a i (-t),
    val_inv := val_inv_of_MShort,
    inv_val := inv_val_of_MShort
  }

abbrev raw_MLong (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) : Matrix (SignedWithZero I) (SignedWithZero I) R :=
  1 + (a * t) • (E (a.inj i) ((!b).inj j))
    - (a * t) • (E (b.inj j) ((!a).inj i))

private theorem val_inv_of_MLong {a b : Bool} {i j : I} {t : R} {hij : i ≠ j} :
  (raw_MLong a b i j t hij) * (raw_MLong a b i j (-t) hij) = 1 := by
  simp only [raw_MLong]
  algebra
  simp only [E_mul_overlap,
    E_mul_disjoint (SignedWithZero.ne_of_ne hij),
    E_mul_disjoint (SignedWithZero.ne_of_ne hij.symm),
    E_mul_disjoint SignedWithZero.ne_of_neg
  ]
  ring_nf
  simp only [square_eq_one]
  module

private theorem inv_val_of_MLong {a b : Bool} {i j : I} {t : R} {hij : i ≠ j} :
  (raw_MLong a b i j (-t) hij) * (raw_MLong a b i j t hij) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_MLong

def MLong (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) : Matrix.GeneralLinearGroup (SignedWithZero I) R :=
  {
    val := raw_MLong a b i j t hij,
    inv := raw_MLong a b i j (-t) hij,
    val_inv := val_inv_of_MLong,
    inv_val := inv_val_of_MLong
  }

theorem inv_of_MLong (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (MLong a b i j t hij)⁻¹ = MLong a b i j (-t) hij := by
  simp only [MLong, Units.inv_mk, neg_neg]

theorem inv_of_MShort (a : Bool) (i : I) (t : R) :
  (MShort a i t)⁻¹ = MShort a i (-t) := by
  simp only [MShort, Units.inv_mk, neg_neg]
