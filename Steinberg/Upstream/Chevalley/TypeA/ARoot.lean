/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.RootSystem

universe TI TR
variable {I : Type TI} [DecidableEq I] [Fintype I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeA
open Chevalley Chevalley.TypeA

/-! ## Root datastructures -/

structure ARoot (I : Type u) [DecidableEq I] [Fintype I] where
  mk ::
  i : I
  j : I
  hij : i ≠ j

def neg (ζ : ARoot I) := ARoot.mk ζ.j ζ.i ζ.hij.symm

instance instRootSystem : RootSystem (ARoot I) where
  neg := neg
  neg_of_neg := by intro ζ; unfold neg; trivial
