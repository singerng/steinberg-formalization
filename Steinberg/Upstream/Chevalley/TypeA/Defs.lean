/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.IndicatorMatrix
import Steinberg.Upstream.Chevalley.ZSigned
import Steinberg.Upstream.Chevalley.BoolToRing

import Steinberg.Upstream.Chevalley.Macro.Algebra

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeA
open Chevalley Chevalley.TypeA

/-! ## Generators corresponding to roots -/

abbrev raw_A_M (i j : I) (hij : i ≠ j) (t : R) : Matrix I I R :=
  1 + t • (E i j)

private theorem val_inv_of_M {i j : I} {t : R} {hij : i ≠ j} :
  (raw_A_M i j hij t) * (raw_A_M i j hij (-t)) = 1 := by
  simp only [raw_A_M]
  algebra
  simp only [E_mul_disjoint hij.symm]
  module

private theorem inv_val_of_M {i j : I} {t : R} {hij : i ≠ j} :
  (raw_A_M i j hij (-t)) * (raw_A_M i j hij t) = 1 := by
  nth_rewrite 2 [←neg_neg t]
  exact val_inv_of_M

def A_M (i j : I) (hij : i ≠ j) (t : R) : Matrix.GeneralLinearGroup I R where
  val := raw_A_M i j hij t
  inv := raw_A_M i j hij (-t)
  val_inv := val_inv_of_M
  inv_val := inv_val_of_M

/-! ## Root datastructures -/

structure ARoot (I : Type u) [DecidableEq I] [Fintype I] where
  mk ::
  i : I
  j : I
  hij : i ≠ j

def ARoot.M (ζ : ARoot I) (t : R) := A_M ζ.i ζ.j ζ.hij t
