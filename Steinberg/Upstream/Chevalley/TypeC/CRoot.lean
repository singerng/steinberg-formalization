/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.RootSystem
import Steinberg.Upstream.Chevalley.SparseSignVector

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I] [LinearOrder I]

namespace Chevalley.TypeC
open Chevalley Chevalley.TypeC

/-! ## Root datastructures -/

abbrev CShortRoot (I : Type TI) [LinearOrder I] := TwoSignVector I

abbrev CLongRoot (I : Type TI) := OneSignVector I

def CRoot (I : Type TI) [LinearOrder I] := CLongRoot I ⊕ CShortRoot I

def neg (ζ : CRoot I) :=
  match ζ with
  | Sum.inl ζ => Sum.inl (OneSignVector.mk (!ζ.a) ζ.i)
  | Sum.inr ζ => Sum.inr (TwoSignVector.mk (!ζ.a) (!ζ.b) ζ.i ζ.j ζ.hij)

instance instRootSystem (I : Type TI) [DecidableEq I] [Fintype I] [LinearOrder I] : RootSystem (CRoot I) where
  neg := neg
  neg_of_neg := by intro ζ; unfold neg; cases ζ; all_goals simp only [Bool.not_not]
