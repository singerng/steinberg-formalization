/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.RootSystem
import Steinberg.Upstream.Chevalley.SparseSignVector

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I] [LinearOrder I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeD
open Chevalley.TypeD

/-! ## Root datastructures -/

abbrev DRoot (I : Type TI) [LinearOrder I] := TwoSignVector I

def neg (ζ : DRoot I) :=
  TwoSignVector.mk (!ζ.a) (!ζ.b) ζ.i ζ.j ζ.hij

instance instRootSystem (I : Type TI) [DecidableEq I] [Fintype I] [LinearOrder I] : RootSystem (DRoot I) where
  neg := neg
  neg_of_neg := by intro ζ; unfold neg; simp only [Bool.not_not]
