/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.IndicatorMatrix
import Steinberg.Upstream.Chevalley.Signed
import Steinberg.Upstream.Chevalley.BoolToRing
import Steinberg.Upstream.Chevalley.SparseSignVector

import Steinberg.Upstream.Chevalley.Macro.Algebra

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeC
open Chevalley Chevalley.TypeC

/-! ## Generators corresponding to roots -/

abbrev raw_C_MLong (a : Bool) (i : I) (t : R) : Matrix (Signed I) (Signed I) R :=
  1 + t • E (a, i) (!a, i)

private theorem val_inv_of_C_MLong {a : Bool} {i : I} {t : R} :
  (raw_C_MLong a i t) * (raw_C_MLong a i (-t)) = 1 := by
  simp only [raw_C_MLong]
  algebra
  simp only [
    E_mul_overlap,
    E_mul_disjoint Signed.ne_of_neg
  ]
  ring_nf
  module

private theorem inv_val_of_C_MLong {a : Bool} {i : I} {t : R} :
  (raw_C_MLong a i (-t)) * (raw_C_MLong a i t) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_C_MLong

def C_MLong (a : Bool) (i : I) (t : R) : Matrix.GeneralLinearGroup (Signed I) R where
  val := raw_C_MLong a i t
  inv := raw_C_MLong a i (-t)
  val_inv := val_inv_of_C_MLong
  inv_val := inv_val_of_C_MLong

abbrev raw_C_MShort (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) : Matrix (Signed I) (Signed I) R :=
  1 + (a * t) • (E (a, i) (!b, j))
    + (b * t) • (E (b, j) (!a, i))

private theorem val_inv_of_C_MShort {a b : Bool} {i j : I} {t : R} {hij : i ≠ j} :
  (raw_C_MShort a b i j t hij) * (raw_C_MShort a b i j (-t) hij) = 1 := by
  simp only [raw_C_MShort]
  algebra
  simp only [
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm
  ]
  ring_nf
  module

private theorem inv_val_of_C_MShort {a b : Bool} {i j : I} {t : R} {hij : i ≠ j} :
  (raw_C_MShort a b i j (-t) hij) * (raw_C_MShort a b i j t hij) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_C_MShort

def C_MShort (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) : Matrix.GeneralLinearGroup (Signed I) R where
  val := raw_C_MShort a b i j t hij
  inv := raw_C_MShort a b i j (-t) hij
  val_inv := val_inv_of_C_MShort
  inv_val := inv_val_of_C_MShort

theorem inv_of_C_MShort (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (C_MShort a b i j t hij)⁻¹ = C_MShort a b i j (-t) hij := by
  simp only [C_MShort, Units.inv_mk, neg_neg]

theorem inv_of_C_MLong (a : Bool) (i : I) (t : R) :
  (C_MLong a i t)⁻¹ = C_MLong a i (-t) := by
  simp only [C_MLong, Units.inv_mk, neg_neg]

/-! ## Root datastructures -/

abbrev CShortRoot (I : Type TI) [LinearOrder I] := TwoSignVector I

def CShortRoot.M [LinearOrder I] (ζ : CShortRoot I) (t : R) :=
  C_MShort ζ.a ζ.b ζ.i ζ.j t (ne_of_lt ζ.hij)

abbrev CLongRoot (I : Type TI) := OneSignVector I

def CLongRoot.M (ζ : CLongRoot I) (t : R) :=
  C_MLong ζ.a ζ.i t

def CRoot (I : Type TI) [LinearOrder I] := CShortRoot I ⊕ CLongRoot I

def CRoot.M [LinearOrder I] (ζ : CRoot I) (t : R) :=
  match ζ with
  | Sum.inl ζ => ζ.M t
  | Sum.inr ζ => ζ.M t
