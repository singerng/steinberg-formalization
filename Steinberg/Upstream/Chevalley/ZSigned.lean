/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

import Steinberg.Upstream.Chevalley.Signed

/-!
  Datatype which, given an instance `I` of `Fintype` and `DecidableEq`, produces a new type
  which is an instance of the same typeclasses and has cardinality `2|I|+1`, namely,
  `(Bool × I) ⊕ Unit`. We think of `Bool x I` as a "signed" version of `I` and `Unit` as a
  "zero" element; the type also admits a natural "negation" involution given by sending
  `inl (s, i)` to `inl (!s, i)`. The canonical example for this is where `I = Fin n`, in which case
  `ZSigned I` corresponds to integers between `-n` and `+n` exclusive.
-/

universe TI
variable {I : Type TI} [DecidableEq I] [Fintype I]

namespace Chevalley
open Chevalley

def ZSigned (I : Type TI) [DecidableEq I] [Fintype I] :=
  Signed I ⊕ Unit
instance : DecidableEq (ZSigned I) := instDecidableEqSum
instance : Fintype (ZSigned I) := instFintypeSum _ _

-- TODO-A: Maybe there is a more 'idiomatic' way to write this shortly?

def ZSigned.zero : ZSigned I := Sum.inr ()
def Bool.inj (s : Bool) (i : I) : ZSigned I := Sum.inl (s, i)

theorem ZSigned.zero_ne_signed {a : Bool} {i : I} : ZSigned.zero ≠ a.inj i := by
  simp only [Bool.inj, ZSigned.zero]
  by_contra
  injections

theorem ZSigned.signed_ne_zero {a : Bool} {i : I} : a.inj i ≠ ZSigned.zero := Ne.symm zero_ne_signed

theorem ZSigned.ne_of_neg {a : Bool} {i j : I} : (!a).inj i ≠ a.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  simp_all only [Bool.not_eq_eq_eq_not, Bool.eq_not_self]

theorem ZSigned.ne_of_ne {a b : Bool} {i j : I} (h : i ≠ j) : a.inj i ≠ b.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  contradiction

theorem ZSigned.neg_of_ne {a b : Bool} {i j : I} (h : a.inj i ≠ (!b).inj j) : (!a).inj i ≠ b.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  simp_all only [ne_eq, Bool.not_eq_eq_eq_not, not_true_eq_false]
