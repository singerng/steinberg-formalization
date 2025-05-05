/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Order.Defs.LinearOrder

universe TI

/-- Encodes a vector with exactly one ±1 entry -/
structure OneSignVector (I : Type TI) where
  mk ::
  a : Bool
  i : I

/-- Encodes a vector with exactly two ±1 entries -/
structure TwoSignVector (I : Type TI) [LinearOrder I] where
  mk ::
  a : Bool
  b : Bool
  i : I
  j : I
  hij : i < j
