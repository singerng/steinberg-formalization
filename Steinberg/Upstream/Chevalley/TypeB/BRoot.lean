/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.RootSystem

import Steinberg.Upstream.Chevalley.SparseSignVector

universe TI
variable {I : Type TI} [DecidableEq I] [Fintype I] [LinearOrder I]

namespace Chevalley.TypeB
open Chevalley Chevalley.TypeB

/-! ## Root datastructures -/

abbrev BLongRoot (I : Type TI) [LinearOrder I] := TwoSignVector I

abbrev BShortRoot (I : Type TI) := OneSignVector I

def BRoot (I : Type TI) [LinearOrder I] := BLongRoot I ⊕ BShortRoot I

def neg (ζ : BRoot I) :=
  match ζ with
  | Sum.inl ζ => Sum.inl (TwoSignVector.mk (!ζ.a) (!ζ.b) ζ.i ζ.j ζ.hij)
  | Sum.inr ζ => Sum.inr (OneSignVector.mk (!ζ.a) ζ.i)

instance instRootSystem (I : Type TI) [DecidableEq I] [Fintype I] [LinearOrder I] : RootSystem (BRoot I) where
  neg := neg
  neg_of_neg := by intro ζ; unfold neg; cases ζ; all_goals simp only [Bool.not_not]
