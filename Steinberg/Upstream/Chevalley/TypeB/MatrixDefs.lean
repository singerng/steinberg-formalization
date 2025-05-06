/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.TypeB.BRoot

import Steinberg.Upstream.Chevalley.IndicatorMatrix
import Steinberg.Upstream.Chevalley.ZSigned
import Steinberg.Upstream.Chevalley.BoolToRing

import Steinberg.Upstream.Chevalley.Macro.Algebra

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeB
open Chevalley Chevalley.TypeB

/-! ## Generators corresponding to roots -/

abbrev raw_B_MShort (a : Bool) (i : I) (t : R) : Matrix (ZSigned I) (ZSigned I) R :=
  1 + (2 * a * t) • (E (a.inj i) ZSigned.zero)
    - (a * t) • (E ZSigned.zero ((!a).inj i))
    - (t^2) • (E (a.inj i) ((!a).inj i))

private theorem val_inv_of_B_MShort {a : Bool} {i : I} {t : R} :
  (raw_B_MShort a i t) * (raw_B_MShort a i (-t)) = 1 := by
  simp only [raw_B_MShort]
  algebra
  simp only [E_mul_overlap,
    E_mul_disjoint ZSigned.ne_of_neg,
    E_mul_disjoint ZSigned.zero_ne_signed,
    E_mul_disjoint (Ne.symm ZSigned.zero_ne_signed)]
  ring_nf
  simp only [square_eq_one]
  module

private theorem inv_val_of_B_MShort {a : Bool} {i : I} {t : R} :
  (raw_B_MShort a i (-t)) * (raw_B_MShort a i t) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_B_MShort

def B_MShort (a : Bool) (i : I) (t : R) : Matrix.GeneralLinearGroup (ZSigned I) R where
  val := raw_B_MShort a i t
  inv := raw_B_MShort a i (-t)
  val_inv := val_inv_of_B_MShort
  inv_val := inv_val_of_B_MShort

abbrev raw_B_MLong (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) : Matrix (ZSigned I) (ZSigned I) R :=
  1 + (a * t) • (E (a.inj i) ((!b).inj j))
    - (a * t) • (E (b.inj j) ((!a).inj i))

private theorem val_inv_of_B_MLong {a b : Bool} {i j : I} {t : R} {hij : i ≠ j} :
  (raw_B_MLong a b i j t hij) * (raw_B_MLong a b i j (-t) hij) = 1 := by
  simp only [raw_B_MLong]
  algebra
  simp only [E_mul_overlap,
    E_mul_disjoint (ZSigned.ne_of_ne hij),
    E_mul_disjoint (ZSigned.ne_of_ne hij.symm),
    E_mul_disjoint ZSigned.ne_of_neg
  ]
  ring_nf
  simp only [square_eq_one]
  module

private theorem inv_val_of_B_MLong {a b : Bool} {i j : I} {t : R} {hij : i ≠ j} :
  (raw_B_MLong a b i j (-t) hij) * (raw_B_MLong a b i j t hij) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_B_MLong

def B_MLong (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) : Matrix.GeneralLinearGroup (ZSigned I) R where
  val := raw_B_MLong a b i j t hij
  inv := raw_B_MLong a b i j (-t) hij
  val_inv := val_inv_of_B_MLong
  inv_val := inv_val_of_B_MLong

theorem inv_of_B_MLong (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (B_MLong a b i j t hij)⁻¹ = B_MLong a b i j (-t) hij := by
  simp only [B_MLong, Units.inv_mk, neg_neg]

theorem inv_of_B_MShort (a : Bool) (i : I) (t : R) :
  (B_MShort a i t)⁻¹ = B_MShort a i (-t) := by
  simp only [B_MShort, Units.inv_mk, neg_neg]
