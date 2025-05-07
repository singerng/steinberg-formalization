/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.TypeD.DRoot

import Steinberg.Upstream.Chevalley.IndicatorMatrix
import Steinberg.Upstream.Chevalley.Signed
import Steinberg.Upstream.Chevalley.BoolToRing

import Steinberg.Upstream.Chevalley.Macro.Algebra

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeD
open Chevalley.TypeD

/-! ## Generators corresponding to roots -/

abbrev raw_D_M (a b : Bool) (i j : I) (h : i ≠ j) (t : R) : Matrix (Signed I) (Signed I) R :=
  1 + (a * t) • (E (a, i) (!b, j)) - (a * t) • E (b, j) (!a, i)

private theorem val_inv_of_M {a b : Bool} {i j : I} {h : i ≠ j} {t : R} :
  (raw_D_M a b i j h t) * (raw_D_M a b i j h (-t)) = 1 := by
  simp only [raw_D_M]
  algebra
  simp only [E_mul_overlap,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint (Ne.symm Signed.ne_of_neg),
    E_mul_disjoint (Signed.ne_of_ne h),
    E_mul_disjoint (Signed.ne_of_ne (Ne.symm h))]
  ring_nf
  module

private theorem inv_val_of_M {a b : Bool} {i j : I} {h : i ≠ j} {t : R} :
  (raw_D_M a b i j h (-t)) * (raw_D_M a b i j h t) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_M

def D_M (a b : Bool) (i j : I) (h : i ≠ j) (t : R) : Matrix.GeneralLinearGroup (Signed I) R where
  val := raw_D_M a b i j h t
  inv := raw_D_M a b i j h (-t)
  val_inv := val_inv_of_M
  inv_val := inv_val_of_M

theorem inv_of_M (a b : Bool) (i j : I) (h : i ≠ j) (t : R) :
  (D_M a b i j h t)⁻¹ = D_M a b i j h (-t) := by
  simp only [D_M, Units.inv_mk, neg_neg]
